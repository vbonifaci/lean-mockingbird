import Mathlib.Tactic
import LeanMockingbird.Chapter16
namespace SmullyanMockingbird

/- Chapter 17: Gödel's Forest -/

variable {Bird : Type} [forest : Forest Bird]
variable (sings Nightingale : Bird → Prop)
variable (mate associate : Bird → Bird)
variable (𝓝 : Bird)

/- Baritoni's Laws -/

def BaritoniLaw1 : Prop :=
  ∀ x : Bird, Nightingale x → sings x

def BaritoniLaw2 : Prop :=
  ∀ x y : Bird, sings ((mate x) * y) ↔ ¬ sings (x * y)

def BaritoniLaw3 : Prop :=
  ∀ x y : Bird, sings ((associate x) * y) ↔ sings (x * (y * y))

def BaritoniLaw4 : Prop :=
  ∀ x : Bird, sings (𝓝 * x) ↔ Nightingale x


-- There is a bird that sings and is not a nightingale
theorem thm17_1
    (hlaw1 : BaritoniLaw1 sings Nightingale) (hlaw2 : BaritoniLaw2 sings mate)
    (hlaw3 : BaritoniLaw3 sings associate) (hlaw4 : BaritoniLaw4 sings Nightingale 𝓝) :
    ∃ 𝓖 : Bird, ¬ Nightingale 𝓖 ∧ sings 𝓖 := by
  let y : Bird := associate (mate (𝓝))
  use y * y
  have h : sings (y * y) ↔ ¬ Nightingale (y * y) := by
    specialize hlaw3 (mate 𝓝) y
    specialize hlaw2 𝓝 (y * y)
    specialize hlaw4 (y * y)
    dsimp [y] at *
    tauto
  specialize hlaw1 (y * y)
  tauto


-- There is a bird that sings and is not a nightingale (alternative construction)
theorem thm17_2
    (hlaw1 : BaritoniLaw1 sings Nightingale) (hlaw2 : BaritoniLaw2 sings mate)
    (hlaw3 : BaritoniLaw3 sings associate) (hlaw4 : BaritoniLaw4 sings Nightingale 𝓝) :
    ∃ 𝓖₁ : Bird, ¬ Nightingale 𝓖₁ ∧ sings 𝓖₁ := by
  let y : Bird := mate (associate (𝓝))
  use y * y
  have h : sings (y * y) ↔ ¬ Nightingale (y * y) := by
    specialize hlaw2 (associate 𝓝) y
    specialize hlaw3 𝓝 y
    specialize hlaw4 (y * y)
    dsimp [y] at *
    tauto
  specialize hlaw1 (y * y)
  tauto


def Represent (A : Bird) (𝓢 : Set Bird) : Prop :=
  ∀ x : Bird, x ∈ 𝓢 ↔ sings (A * x)

def Society (𝓢 : Set Bird) : Prop :=
  ∃ A : Bird, Represent sings A 𝓢

-- Nightingales constitute a society (if Law 4 holds)
example
    (hlaw4 : BaritoniLaw4 sings Nightingale 𝓝) :
    Society sings { x : Bird | Nightingale x } := by
  use 𝓝
  rw [Represent]
  intro x
  rw [hlaw4]
  tauto

-- The set of singing birds do not constitute a society (using Laws 2-3)
theorem thm17_3
    (hlaw2 : BaritoniLaw2 sings mate)
    (hlaw3 : BaritoniLaw3 sings associate) :
    ¬ Society sings { x : Bird | sings x } := by
  intro h
  obtain ⟨S, hS⟩ := h
  have hC : Society sings { x : Bird | ¬ sings x } := by
    use (mate S)
    rw [Represent]
    intro x
    rw [hlaw2]
    specialize hS x
    tauto
  obtain ⟨T, hT⟩ := hC
  specialize hlaw3 T (associate T)
  specialize hT (associate T * associate T)
  tauto



end SmullyanMockingbird
