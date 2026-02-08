import Mathlib.Tactic
import LeanMockingbird.Chapter18
namespace SmullyanMockingbird

/- Chapter 19: Aristocratic Birds -/

variable {Bird : Type} [forest : Forest Bird]


def Jaybird (J : Bird) : Prop :=
  ∀ x y z w : Bird, J * x * y * z * w = x * y * (x * w * z)

def CardinalTwiceRemoved (C₂ : Bird) : Prop :=
  ∀ x y z w v : Bird, C₂ * x * y * z * w * v = x * y * z * v * w

/- Derivation of the Jaybird -/

-- A Jaybird from E, C₁, C₂, W
theorem thm19_1
    (E C₁ C₂ W : Bird) (hE : Eagle E) (hC₁ : CardinalOnceRemoved C₁)
    (hC₂ : CardinalTwiceRemoved C₂)
    (hW : Warbler W) :
    ∃ J : Bird, Jaybird J := by
  use C₂ * (W * (C₁ * E))
  intro x y z w
  rw [hC₂, hW, hC₁, hE]

-- A Jaybird from B, C, W
theorem thm19_1_corollary
    (B C W : Bird) (hB : Bluebird B) (hC : Cardinal C) (hW : Warbler W) :
    ∃ J : Bird, Jaybird J := by
  obtain ⟨C₁, hC₁⟩ := thm11_31 B C hB hC
  have hC₂ : CardinalTwiceRemoved (B * C₁) := by
    intro x y z w v
    rw [hB, hC₁]
  obtain ⟨E, hE⟩ := thm11_7 B hB
  apply thm19_1 E C₁ (B * C₁) W hE hC₁ hC₂ hW


/- Going in the Other Direction -/

-- A Quixotic bird from J, I
theorem thm19_2
    (J I : Bird) (hJ : Jaybird J) (hI : Identity I) :
    ∃ Q₁ : Bird, QuixoticBird Q₁ := by
  use J * I
  intro x y z
  rw [hJ, hI, hI]

-- A Thrush from Q₁, I
theorem thm19_3
    (Q₁ I : Bird) (hQ₁ : QuixoticBird Q₁) (hI : Identity I) :
    ∃ T : Bird, Thrush T := by
  use Q₁ * I
  intro x y
  rw [hQ₁, hI]

-- A Robin from J, T
theorem thm19_4
    (J T : Bird) (hJ : Jaybird J) (hT : Thrush T) :
    ∃ R : Bird, Robin R := by
  use J * T
  intro x y z
  rw [hJ, hT, hT]

-- A Bluebird from C, Q₁
theorem thm19_5
    (C Q₁ : Bird) (hC : Cardinal C) (hQ₁ : QuixoticBird Q₁) :
    ∃ B : Bird, Bluebird B := by
  have hC₁ : CardinalOnceRemoved (C * (Q₁ * C)) := by
    intro x y z w
    rw [hC, hQ₁, hC]
  use C * (Q₁ * C) * Q₁
  intro x y z
  rw [hC₁, hQ₁]


def Jaybird₁ (J₁ : Bird) : Prop :=
  ∀ x y z w : Bird, J₁ * x * y * z * w = y * x * (w * x * z)

-- A Jaybird₁ from J, B, T
theorem thm19_6
    (J B T : Bird) (hJ : Jaybird J) (hB : Bluebird B) (hT : Thrush T) :
    ∃ J₁ : Bird, Jaybird₁ J₁ := by
  use B * J * T
  intro x y z w
  rw [hB, hJ, hT, hT]

-- A Mockingbird from C, T, J₁
theorem thm19_7
    (C T J₁ : Bird) (hC : Cardinal C) (hT : Thrush T) (hJ₁ : Jaybird₁ J₁) :
    ∃ M : Bird, Mockingbird M := by
  use C * (C * (C * J₁ * T) * T) * T
  intro x
  rw [hC, hC, hC, hJ₁, hT, hT, hT]




end SmullyanMockingbird
