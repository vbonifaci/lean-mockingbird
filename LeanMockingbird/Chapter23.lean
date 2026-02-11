import Mathlib.Tactic
import LeanMockingbird.Chapter22
namespace SmullyanMockingbird

/- Chapter 23: Logical Birds -/

variable {Bird : Type}

/-
  With respect to the book, we slightly strengthen the definitions of IsTrue and IsFalse
  instead of requiring x = K for a *particular* K, or x = K * I for *particular* K and I,
  as otherwise we would need additional assumptions (e.g., extensionality) to conclude
  that some bird equals t or f (the forest might contain multiple kestrels or identities)
-/

def IsTrue (x : Bird) [forest : Forest Bird] : Prop :=
  ∀ K : Bird, Kestrel K → x = K

def IsFalse (x : Bird) [forest : Forest Bird] : Prop :=
  ∀ K I : Bird, Kestrel K → Identity I → x = K * I


class LogicalForest (Bird : Type) extends Forest Bird where
  /- Nontriviality assumption (at least two distinct birds in the forest) -/
  hnontrivial : NonTrivial toForest
  /- Combinatorial birds -/
  /-
      K and S are enough, but assuming
      a few more will be handy.
      Naming them will be useful for the next chapter
  -/
  K : Bird
  S : Bird
  I : Bird
  B : Bird
  V : Bird
  R : Bird
  T : Bird
  C : Bird
  L : Bird
  hK : Kestrel K
  hS : Starling S
  hI : Identity I
  hB : Bluebird B
  hV : Vireo V
  hR : Robin R
  hT : Thrush T
  hC : Cardinal C
  hL : Lark L
  /- Sage bird -/
  Θ : Bird
  hΘ : SageBird Θ
  /- Truth birds  -/
  t : Bird
  f : Bird
  ht : IsTrue t
  hf : IsFalse f

variable [forest : LogicalForest Bird]

-- Direct rewriting rule for t: t is a Kestrel
theorem ht' :
    Kestrel forest.t := by
  rw [Kestrel]
  intro x y
  let K := forest.K; let hK := forest.hK
  rw [forest.ht K, hK]
  exact hK

-- Direct rewriting rule for f: f * y is an Identity for any y
theorem hf' :
    ∀ y : Bird, Identity (forest.f * y) := by
  intro x y
  let K := forest.K; let hK := forest.hK
  let I := forest.I; let hI := forest.hI
  rw [forest.hf K I hK hI, hK, hI]

/- Handy abbreviations -/

abbrev t := forest.t
abbrev f := forest.f
abbrev ht := forest.ht
abbrev hf := forest.hf



-- Existence of a Negation bird
theorem thm23_1 :
    ∃ 𝓝 : Bird, 𝓝 * t = f ∧ 𝓝 * f = t := by
  let K := forest.K; let hK := forest.hK
  let I := forest.I; let hI := forest.hI
  let V := forest.V; let hV := forest.hV
  use V * f * t
  constructor
  · rw [hV, ht']
  · rw [hV, hf']


-- Existence of a Conjunction bird
theorem thm23_2 :
    ∃ c : Bird, c * t * t = t ∧ c * f * t = f ∧
                c * t * f = f ∧ c * f * f = f := by
  let K := forest.K; let hK := forest.hK
  let I := forest.I; let hI := forest.hI
  let R := forest.R; let hR := forest.hR
  use R * f
  constructor
  · rw [hR, ht']
  · constructor
    · rw [hR, hf']
    · constructor
      · rw [hR, ht']
      · rw [hR, hf']

-- Existence of a Disjunction bird
theorem thm23_3 :
    ∃ d : Bird, d * t * t = t ∧ d * f * t = t ∧
                d * t * f = t ∧ d * f * f = f := by
  let K := forest.K; let hK := forest.hK
  let I := forest.I; let hI := forest.hI
  let T := forest.T; let hT := forest.hT
  use T * t
  constructor
  · rw [hT, ht']
  · constructor
    · rw [hT, hf']
    · constructor
      · rw [hT, ht']
      · rw [hT, hf']

-- Existence of a If-then bird
theorem thm23_4 :
    ∃ i : Bird, i * t * t = t ∧ i * f * t = t ∧
                i * t * f = f ∧ i * f * f = t := by
  let K := forest.K; let hK := forest.hK
  let I := forest.I; let hI := forest.hI
  let R := forest.R; let hR := forest.hR
  use R * t
  constructor
  · rw [hR, ht']
  · constructor
    · rw [hR, hf']
    · constructor
      · rw [hR, ht']
      · rw [hR, hf']

-- Existence of a If-and-only-if bird
theorem thm23_5 :
    ∃ i : Bird, i * t * t = t ∧ i * f * t = f ∧
                i * t * f = f ∧ i * f * f = t := by
  let K := forest.K; let hK := forest.hK
  let I := forest.I; let hI := forest.hI
  let S := forest.S; let hS := forest.hS
  let C := forest.C; let hC := forest.hC
  obtain ⟨𝓝, h𝓝⟩ := @thm23_1 Bird forest
  use C * S * 𝓝
  constructor
  · rw [hC, hS, ht']
  · constructor
    · rw [hC, hS, hf']
      apply h𝓝.1
    · constructor
      · rw [hC, hS, ht']
      · rw [hC, hS, hf']
        apply h𝓝.2


end SmullyanMockingbird
