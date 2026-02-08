import Mathlib.Tactic
import LeanMockingbird.Chapter17
namespace SmullyanMockingbird

/- Chapter 18: The Master Forest -/

variable {Bird : Type} [forest : Forest Bird]


-- An Identity bird from S, K
theorem thm18_1
    (S K : Bird) (hS : Starling S) (hK : Kestrel K) :
    ∃ I : Bird, Identity I := by
  use S * K * K
  intro x
  rw [hS, hK]

-- A Mockingbird from S, I
theorem thm18_2
    (S I : Bird) (hS : Starling S) (hI : Identity I) :
    ∃ M : Bird, Mockingbird M := by
  use S * I * I
  intro x
  rw [hS, hI]

-- A Thrush from S, K, I
theorem thm18_3
    (S K I : Bird) (hS : Starling S) (hK : Kestrel K) (hI : Identity I) :
    ∃ T : Bird, Thrush T := by
  -- X₁ = SI(Kx), X₂ = S(K(SI))K
  use S * (K * (S * I)) * K
  intro x y
  nth_rw 1 [hS, hK, hS, hI, hK]

-- A Bluebird from S, K, I
theorem thm18_4
    (S K : Bird) (hS : Starling S) (hK : Kestrel K) :
    ∃ B : Bird, Bluebird B := by
  -- X₁ = S(Kx)y, X₂ = S(Kx), X₃ = S(KS)K
  use S * (K * S) * K
  intro x y z
  nth_rw 1 [hS, hK, hS, hK]




end SmullyanMockingbird
