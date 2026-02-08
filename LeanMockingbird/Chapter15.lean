import Mathlib.Tactic
import LeanMockingbird.Chapter14
namespace SmullyanMockingbird

/- Chapter 15: Russell's Forest -/

variable {Bird : Type} [forest : Forest Bird]
variable (a 𝓝 A : Bird)
variable (sings : Bird → Prop)

/- McSnurd's Facts -/

def McSnurdFact1 : Prop :=
  ∀ x : Bird, sings (a * x) ↔ sings (x * x)

def McSnurdFact2 : Prop :=
  ∀ x : Bird, ∃ x' : Bird, ∀ y : Bird, sings (x' * y) ↔ ¬ sings (x * y)

def McSnurdFact3 : Prop :=
  ∀ x : Bird, sings (𝓝 * x) ↔ ¬ sings x

def McSnurdFact4 : Prop :=
  ∃ Θ : Bird, SageBird Θ

def McSnurdFact5 : Prop :=
  ∀ x y : Bird, sings (A * x * y) ↔ ¬sings x ∧ ¬sings y



-- McSnurd's Facts 1-2 are incompatible
theorem thm15_1
    (hf1 : McSnurdFact1 a sings) (hf2 : McSnurdFact2 sings) :
    False := by
  obtain ⟨a', ha'⟩ := hf2 a
  specialize ha' a'
  specialize hf1 a'
  tauto


-- McSnurd's Facts 3-4 are incompatible
theorem thm15_2
    (hf3 : McSnurdFact3 𝓝 sings) (hf4 : @McSnurdFact4 Bird forest) :
    False := by
  obtain ⟨Θ, hΘ⟩ := hf4
  specialize hf3 (Θ * 𝓝)
  rw [SageBird] at hΘ
  have h : FondOf 𝓝 (Θ * 𝓝) := by
    apply hΘ 𝓝
    rfl
  rw [FondOf] at h
  rw [h] at hf3
  tauto


-- McSnurd's Facts 4-5 are incompatible
theorem thm15_3
    (hf4 : @McSnurdFact4 Bird forest) (hf5 : McSnurdFact5 A sings) :
    False := by
  obtain ⟨Θ, hΘ⟩ := hf4
  have h : ∀ x : Bird, sings x := by
    intro x
    let y : Bird := Θ * (A * x)
    have eq : A * x * y = y := by
      apply hΘ (A * x)
      simp [y]
    rw [McSnurdFact5] at hf5
    specialize hf5 x y
    rw [eq] at hf5
    tauto
  have hA : sings A := h A
  let y : Bird := Θ * (A * A)
  have eq : A * A * y = y := by
    apply hΘ (A * A)
    simp [y]
  rw [McSnurdFact5] at hf5
  specialize hf5 A y
  rw [eq] at hf5
  have hy : ¬sings y := by
    tauto
  tauto

end SmullyanMockingbird
