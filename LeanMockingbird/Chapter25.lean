import Mathlib.Tactic
import LeanMockingbird.Chapter24
namespace SmullyanMockingbird

/- Chapter 25: Is there an Ideal Bird? -/

variable {Bird : Type} [forest : LogicalForest Bird]

-- Goedel number of NumberBird 0
def «0#» : ℕ := 3312424
-- Goedel number of (V f)
def s : ℕ :=    313231313312424323233124244444424


def GoedelNumber (n : ℕ) : ℕ :=
  if n = 0 then «0#»
  else ConcatFunction (ConcatFunction (ConcatFunction 3 s) (GoedelNumber (n - 1))) 4


#eval var_eliminate "δ" (var_eliminate "n" (
  "Z" * "n" * "n0#" * ("A" * ("δ" * ("P" * "n")))
))
-- prints:
/-
  S * (K * (S * (S * Z * (K * n0#))))
  * (S * (K * (S * (K * A))) * (S * (S * (K * S) * K) * (K * P)))
-/

-- Goedel numbering bird - preparatory lemma
theorem lemma25_1 (Z A P n0_ : Bird) :
    ∃ δ : Bird, ∀ n : Nat,
    δ * NumberBird n =
    Z * (NumberBird n) * n0_ *
    (A * (δ * (P * NumberBird n))) := by
  let K := forest.K; let hK := forest.hK
  let S := forest.S; let hS := forest.hS
  let Θ := forest.Θ; let hΘ := forest.hΘ
  let A₁ : Bird := S * (K * (S * (S * Z * (K * n0_))))
    * (S * (K * (S * (K * A))) * (S * (S * (K * S) * K) * (K * P)))
  use Θ * A₁
  intro n
  rw [SageBird] at hΘ
  specialize hΘ A₁ (Θ * A₁) rfl
  rw [FondOf] at hΘ
  nth_rw 1 [← hΘ]
  dsimp [A₁]
  rw [hS, hK, hS, hS, hS, hK, hK, hS, hK, hS, hS, hK, hS, hK,
    hK]


-- Existence of a Goedel numbering bird
theorem thm25_1 :
    ∃ δ : Bird, ∀ n : ℕ,
    δ * NumberBird n = NumberBird (GoedelNumber n) := by
  let B := forest.B; let hB := forest.hB
  let C := forest.C; let hC := forest.hC
  let n3 : Bird := NumberBird 3
  let n4 : Bird := NumberBird 4
  let ns : Bird := NumberBird s
  obtain ⟨Cat, hCat⟩ := @thm24_12 Bird forest
  let A := B * (C * Cat * n4) * (Cat * (Cat * n3 * ns))
  let n0_ : Bird := NumberBird «0#»
  obtain ⟨P, hP⟩ := @thm24_2 Bird forest
  obtain ⟨Z, hZ⟩ := @thm24_3 Bird forest
  obtain ⟨δ, hδ⟩ := lemma25_1 Z A P n0_
  use δ
  intro n
  induction n with
  | zero =>
    rw [hδ]
    have hZ1 : Z * NumberBird 0 = t := by
      rw [(hZ 0).1]
      rfl
    rw [hZ1, ht']
    unfold n0_
    unfold GoedelNumber
    dsimp
  | succ n ih =>
    rw [hδ]
    have hZ2 : Z * NumberBird (n + 1) = f := by
      rw [(hZ (n + 1)).2]
      omega
    rw [hZ2, hf']
    unfold A
    rw [hB, hC, hCat, ← lemma_successor, hP, ih, hCat, hCat]
    conv_rhs => unfold GoedelNumber
    conv_lhs => dsimp [GoedelNumber]
    dsimp


def Normalizer (Δ : Bird) : Prop :=
  ∀ n : ℕ, Δ * NumberBird n = NumberBird (ConcatFunction n (GoedelNumber n))

-- Existence of a Normalizer bird
theorem thm25_2 :
    ∃ Δ : Bird, Normalizer Δ := by
  let S := forest.S; let hS := forest.hS
  obtain ⟨Cat, hCat⟩ := @thm24_12 Bird forest
  obtain ⟨δ, hδ⟩ := @thm25_1 Bird forest
  use S * Cat * δ
  intro n
  rw [hS, hδ, hCat]




end SmullyanMockingbird
