import Mathlib.Tactic
import LeanMockingbird.Chapter20
namespace SmullyanMockingbird

open Lean
open Std

/- Chapter 21: The Fixed Point Principle -/

variable {Bird : Type} [forest : Forest Bird]


/- Machinery to algorithmically build a fixed-point solution (aka 'The Secret') -/

inductive Expr (α : Type) where
  | var  : α -> Expr α
  | mul  : Expr α -> Expr α -> Expr α
  deriving BEq

-- Define a recursive function for InfoView pretty-printing
def Expr.format [Repr String] (prec : Nat) : Expr String → Format
  | .var v => f!"{v}"
  | .mul e1 e2 =>
    let res := f!"{Expr.format 70 e1} * {Expr.format 71 e2}"
    if prec > 70 then f!"({res})" else res

-- Link the instance to that function
instance [Repr String] : Repr (Expr String) where
  reprPrec e prec := Expr.format prec e

-- Define the multiplication behavior for our Expr type
-- Use HMul (Heterogeneous Multiplication) for the * operator
instance : HMul (Expr String) (Expr String) (Expr String) where
  hMul := Expr.mul

-- Allow Lean to automatically wrap variables in Expr.var
instance : Coe String (Expr String) where
  coe := Expr.var

-- Now we can write this:
def myExpr : Expr String :=
  let x : Expr String := "x"
  let y : Expr String := "y"
  x * (y * x)

-- Function to check whether some variable occurs or not
def occurs [BEq String] (target : String) : Expr String → Bool
  | .var v     => v == target
  | .mul e1 e2 => occurs target e1 || occurs target e2

#eval myExpr
#eval occurs "y" myExpr

-- Variable elimination function (deterministic with greedy rules 1-3)
def var_eliminate [BEq String] (alpha : String) : Expr String → Expr String
  | .var v    =>
    if alpha == v then "I"
    else "K" * v
  | .mul e1 e2 =>
    if !occurs alpha e1 then
      if e2 == alpha then e1
      else
        "S" * ("K" * e1) * (var_eliminate alpha e2)
    else
      if !occurs alpha e2 then
        "S" * (var_eliminate alpha e1) * ("K" * e2)
      else -- double recursion as last resort
        "S" * (var_eliminate alpha e1) * (var_eliminate alpha e2)

#eval var_eliminate "y" ("y" * "x")
#eval var_eliminate "x" ("S" * "I" * ("K" * "x"))
#eval var_eliminate "x" (var_eliminate "y" ("y" * "x"))
-- prints: S * (K * (S * I)) * K

example (S K I : Bird) (hS : Starling S) (hK : Kestrel K) (hI : Identity I) :
  ∃ A : Bird, ∀ x y : Bird, A * x * y = y * x := by
use S * (K * (S * I)) * K
intro x y
rw [hS, hK, hS, hI, hK]



-- A bird A such that Ay = yA(AyA)
#eval var_eliminate "A" (var_eliminate "y" ("y" * "A" * ("A" * "y" * "A")))
-- prints: S * (S * (K * S) * (S * (K * (S * I)) * K)) * (S * S * K)

theorem thm21_1
    (S K : Bird) (hS : Starling S) (hK : Kestrel K) :
    ∃ A : Bird, ∀ y : Bird, A * y = y * A * (A * y * A) := by
  obtain ⟨I, hI⟩ := thm18_1 S K hS hK
  obtain ⟨M, hM⟩ := thm18_2 S I hS hI
  obtain ⟨T, hT⟩ := thm18_3 S K I hS hK hI
  obtain ⟨B, hB⟩ := thm18_4 S K hS hK
  obtain ⟨C, hC⟩ := thm11_21_bonus B T hB hT
  obtain ⟨W, hW⟩ := thm12_7 B T M hB hT hM
  obtain ⟨Θ, hΘ⟩ := thm13_4 B M W hB hM hW
  --let A₁ : Bird := S * (B * S * T) * (W * C) -- A₁xy = yx(xyx) -- alternative manual solution
  let A₁ : Bird := S * (S * (K * S) * (S * (K * (S * I)) * K)) * (S * S * K)
  use Θ * A₁ -- A₁ is fond of Θ A₁
  intro y
  rw [SageBird] at hΘ
  specialize hΘ A₁ (Θ * A₁) rfl
  rw [FondOf] at hΘ
  nth_rw 1 [← hΘ]
  dsimp [A₁]
  --nth_rw 1 [hS, hB, hS, hT, hW, hC]
  nth_rw 1 [hS, hS, hK, hS, hS, hK, hS, hI, hK, hS, hS, hK]


-- A bird A such that Ayz = z(yA)(yAz)
#eval var_eliminate "A" (var_eliminate "y" (var_eliminate "z"
  ("z" * ("y" * "A") * ("y" * "A" * "z"))))
-- prints: S * (S * (K * S) * (S * (K * (S * (K * S)))
-- * (S * (K * (S * (K * (S * I)))) * (S * (K * (S * (K * K)))
-- * (S * (K * (S * I)) * K))))) * (S * (K * (S * I)) * K)

theorem thm21_2
    (S K : Bird) (hS : Starling S) (hK : Kestrel K) :
    ∃ A : Bird, ∀ y z : Bird, A * y * z = z * (y * A) * (y * A * z) := by
  obtain ⟨I, hI⟩ := thm18_1 S K hS hK
  obtain ⟨M, hM⟩ := thm18_2 S I hS hI
  obtain ⟨T, hT⟩ := thm18_3 S K I hS hK hI
  obtain ⟨B, hB⟩ := thm18_4 S K hS hK
  obtain ⟨W, hW⟩ := thm12_7 B T M hB hT hM
  obtain ⟨Θ, hΘ⟩ := thm13_4 B M W hB hM hW
  -- A₁xyz = (z(yx))(yxz)
  --let A₁ : Bird := S * (S * (K * S) * (S * (K * (S * (K * S)))
  -- * (S * (K * (S * (K * T))) * T))) * T
  let A₁ : Bird := S * (S * (K * S) * (S * (K * (S * (K * S))) --
  * (S * (K * (S * (K * (S * I)))) * (S * (K * (S * (K * K))) --
  * (S * (K * (S * I)) * K))))) * (S * (K * (S * I)) * K)
  use Θ * A₁ -- A₁ is fond of Θ A₁
  intro y z
  rw [SageBird] at hΘ
  specialize hΘ A₁ (Θ * A₁) rfl
  rw [FondOf] at hΘ
  nth_rw 1 [← hΘ]
  dsimp [A₁]
  --nth_rw 1 [hS, hS, hK, hS, hS, hK, hS, hK, hS, hS, hK, hS, hK, hT, hT, hT]
  nth_rw 1 [hS, hS, hK, hS, hS, hK, hS, hK, hS, hS, hK, hS, hK, hS, hI,
    hS, hK, hS, hK, hK, hS, hK, hS, hI, hK, hS, hK, hS, hK, hI]





end SmullyanMockingbird
