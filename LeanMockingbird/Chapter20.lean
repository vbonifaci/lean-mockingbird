import Mathlib.Tactic
import LeanMockingbird.Chapter19
namespace SmullyanMockingbird

/- Chapter 20: Craig's Discovery -/

variable {Bird : Type} [forest : Forest Bird]


-- A Quirky bird from G, I
theorem thm20_1
    (G I : Bird) (hG : Goldfinch G) (hI : Identity I) :
    ∃ Q₃ : Bird, QuirkyBird Q₃ := by
  use G * I
  intro x y z
  rw [hG, hI]

-- A Thrush from Q₃, I
theorem thm20_2
    (Q₃ I : Bird) (hQ₃ : QuirkyBird Q₃) (hI : Identity I) :
    ∃ T : Bird, Thrush T := by
  use Q₃ * I
  intro x y
  rw [hQ₃, hI]

-- A Thrush from G, I
theorem thm20_2_corollary
    (G I : Bird) (hG : Goldfinch G) (hI : Identity I) :
    ∃ T : Bird, Thrush T := by
  obtain ⟨Q₃, hQ₃⟩ := thm20_1 G I hG hI
  apply thm20_2 Q₃ I hQ₃ hI

-- A Cardinal from G, I
theorem thm20_3
    (G I : Bird) (hG : Goldfinch G) (hI : Identity I) :
    ∃ C : Bird, Cardinal C := by
  use G * G * I * I
  intro x y z
  rw [hG, hI, hG, hI]

-- A Queer bird from R, G, Q₃
theorem thm20_4
    (R G Q₃ : Bird) (hR : Robin R) (hG : Goldfinch G) (hQ₃ : QuirkyBird Q₃) :
    ∃ Q : Bird, QueerBird Q := by
  use G * R * Q₃
  intro x y z
  rw [hG, hR, hQ₃]

-- A Bluebird from G, I
theorem thm20_4_corollary
    (G I : Bird) (hG : Goldfinch G) (hI : Identity I) :
    ∃ B : Bird, Bluebird B := by
  obtain ⟨C, hC⟩ := thm20_3 G I hG hI
  obtain ⟨R, hR⟩ := thm11_23 C hC
  obtain ⟨Q₃, hQ₃⟩ := thm20_1 G I hG hI
  obtain ⟨Q, hQ⟩ := thm20_4 R G Q₃ hR hG hQ₃
  use C * Q
  intro x y z
  rw [hC, hQ]


end SmullyanMockingbird
