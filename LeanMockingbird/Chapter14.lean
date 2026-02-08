import Mathlib.Tactic
import LeanMockingbird.Chapter13
namespace SmullyanMockingbird

/- Chapter 14: Curry’s Lively Bird Forest -/

variable {Bird : Type} [forest : Forest Bird]
variable (P : Bird)
variable (sings : Bird → Prop)

/- Byrd's Four Laws -/

def ByrdLaw1 : Prop :=
  ∀ x y : Bird, sings y → sings (P * x * y)

def ByrdLaw2 : Prop :=
  ∀ x y : Bird, ¬sings x → sings (P * x * y)

def ByrdLaw3 : Prop :=
  ∀ x y : Bird, sings x ∧ sings (P * x * y) → sings y

def ByrdLaw4 : Prop :=
  ∀ x : Bird, ∃ y : Bird, sings y ↔ sings (P * y * x)


-- The four laws imply that each bird sings
theorem thm14_1
    (law1 : ByrdLaw1 P sings) (law2 : ByrdLaw2 P sings)
    (law3 : ByrdLaw3 P sings) (law4 : ByrdLaw4 P sings) :
    ∀ x : Bird, sings x := by
  have hP1 : ∀ x y : Bird, (sings x → sings y) → sings (P * x * y) := by
    intro x y h
    by_cases hx : sings x
    · specialize law1 x y
      apply law1
      apply h
      apply hx
    · specialize law2 x y
      apply law2
      exact hx
  have hP2 : ∀ x y : Bird, sings (P * x * y) → (sings x → sings y) := by
    intro x y h hx
    specialize law3 x y
    apply law3
    constructor
    · exact hx
    · exact h
  have hP : ∀ x y : Bird, (sings x → sings y) ↔ sings (P * x * y) := by
    intro x y
    constructor
    · exact hP1 x y
    · exact hP2 x y
  intro x
  specialize law4 x
  obtain ⟨y, hy⟩ := law4
  specialize hP y x
  by_cases hy2 : sings y
  · tauto
  · tauto


-- If L and C are present, Byrd's laws (1-3) imply that each bird sings
theorem thm14_2
    (L C : Bird) (hL : Lark L) (hC : Cardinal C)
    (law1 : ByrdLaw1 P sings) (law2 : ByrdLaw2 P sings) (law3 : ByrdLaw3 P sings) :
    ∀ x : Bird, sings x := by
  have law4 : ByrdLaw4 P sings := by
    rw [ByrdLaw4]
    intro x
    obtain ⟨y, hy⟩ := thm9_25 L hL (C * P * x)
    use y
    have eq : y = P * y * x := by
      rw [FondOf] at *
      rw [hC] at hy
      apply Eq.symm
      exact hy
    nth_rw 1 [eq]
  apply thm14_1 P sings law1 law2 law3 law4


-- If a bird A with Axyz = x(zz)y is present, Byrd's laws (1-3) imply that each bird sings
theorem thm14_3
    (A : Bird)
    (hA : ∀ x y z : Bird, A * x * y * z = x * (z * z) * y)
    (law1 : ByrdLaw1 P sings) (law2 : ByrdLaw2 P sings) (law3 : ByrdLaw3 P sings) :
    ∀ x : Bird, sings x := by
  have law4 : ByrdLaw4 P sings := by
    rw [ByrdLaw4]
    intro x
    use A * P * x * (A * P * x)
    have eq : A * P * x * (A * P * x) = P * (A * P * x * (A * P * x)) * x := by
      nth_rw 1 [hA]
    nth_rw 1 [eq]
  apply thm14_1 P sings law1 law2 law3 law4



end SmullyanMockingbird
