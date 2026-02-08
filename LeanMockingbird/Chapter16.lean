import Mathlib.Tactic
import LeanMockingbird.Chapter15
namespace SmullyanMockingbird

/- Chapter 16: The Forest Without A Name -/

variable {Bird : Type} [forest : Forest Bird]
variable (e : Bird)
variable (sings : Bird → Prop)

/- McSnurtle's Facts -/

def McSnurtleFact1 : Prop :=
  ∀ x y : Bird, sings (e * x * y) → sings y

def McSnurtleFact2 : Prop :=
  ∀ x y : Bird, (sings x → ¬ sings (e * x * y)) ∧ (sings (e * x * y) → ¬ sings x)

def McSnurtleFact3 : Prop :=
  ∀ x y : Bird, (¬ sings x ∧ sings y) → sings (e * x * y)

def McSnurtleFact4 : Prop :=
  ∀ x : Bird, ∃ y : Bird, sings y ↔ sings (e * y * x)


-- The four facts imply that no bird sings
theorem thm16_1
    (hf1 : McSnurtleFact1 e sings) (hf2 : McSnurtleFact2 e sings)
    (hf3 : McSnurtleFact3 e sings) (hf4 : McSnurtleFact4 e sings) :
    ∀ x : Bird, ¬ sings x := by
  have h : ∀ x y : Bird, sings (e * x * y) ↔ ¬ sings x ∧ sings y := by
    intro x y
    constructor
    · intro he
      constructor
      · specialize hf2 x y
        apply hf2.2 he
      · specialize hf1 x y
        apply hf1 he
    · intro hxy
      specialize hf3 x y hxy
      exact hf3
  intro x
  specialize hf4 x
  obtain ⟨y, hy⟩ := hf4
  specialize h y x
  tauto




end SmullyanMockingbird
