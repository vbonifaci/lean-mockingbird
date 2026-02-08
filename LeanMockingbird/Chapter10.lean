import Mathlib.Tactic
import LeanMockingbird.Chapter09
namespace SmullyanMockingbird

/- Chapter 10: Is There A Sage Bird? -/

variable {Bird : Type} [forest : Forest Bird]


def SageBird (Θ : Bird) : Prop :=
  ∀ x y : Bird, Θ * x = y → FondOf x y

def Composes (C A B : Bird) : Prop :=
  ∀ x : Bird, C * x = A * (B * x)

-- Existence of a sage bird
theorem thm10_1
    (A M : Bird) (hA : ∀ x : Bird, Composes (A * x) x M)
    (hM : Mockingbird M) (hC₁ : Condition1 forest) :
    ∃ Θ : Bird, SageBird Θ := by
  obtain ⟨Θ, hΘ⟩ := hC₁ M A
  use Θ
  rw [SageBird]
  intro x y h
  rw [FondOf]
  rw [hΘ x] at h
  rw [Mockingbird] at hM
  rw [hM] at h
  specialize hA x
  rw [Composes] at hA
  specialize hA (A * x)
  rw [hM] at hA
  rw [h] at hA
  apply Eq.symm
  exact hA





end SmullyanMockingbird
