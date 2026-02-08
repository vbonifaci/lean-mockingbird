import Mathlib.Tactic
namespace SmullyanMockingbird

/- Chapter 9: To Mock a Mockingbird -/

class Forest (Bird : Type) extends Mul Bird
variable {Bird : Type} [forest : Forest Bird]

-- Composition condition
def Condition1 (forest : Forest Bird) : Prop :=
  ∀ A B : Bird, ∃ C : Bird, ∀ x : Bird, C * x = A * (B * x)

-- Mockingbird condition
def Condition2 (forest : Forest Bird) : Prop :=
  ∃ M : Bird, ∀ x : Bird, M * x = x * x

-- Alternative condition (for Theorem 9.3)
def Condition2' (forest : Forest Bird) : Prop :=
  ∃ A : Bird, ∀ B : Bird, ∃ x : Bird, A * x = B * x

/- To Mock a Mockingbird -/

def Mockingbird (M : Bird) : Prop :=
  ∀ x : Bird, M * x = x * x

def FondOf (A B : Bird) : Prop := A * B = B

-- Every bird is fond of at least one bird (under Conditions 1-2)
theorem thm9_1
    (A : Bird) (hC₁ : Condition1 forest) (hC₂ : Condition2 forest) :
    ∃ x : Bird, FondOf A x := by
  obtain ⟨M, hM⟩ := hC₂
  obtain ⟨C, hC⟩ := hC₁ A M
  use M * C
  rw [FondOf]
  calc A * (M * C)
    _ = C * C := by rw [hC C]
    _ = M * C := by rw [hM C]

def Egocentric (x : Bird) : Prop := FondOf x x

-- At least one bird is Egocentric (under Conditions 1-2)
theorem thm9_2
    (hC₁ : Condition1 forest) (hC₂ : Condition2 forest) :
    ∃ x : Bird, Egocentric x := by
  have hC₂_copy : Condition2 forest := hC₂
  obtain ⟨M, hM⟩ := hC₂
  obtain ⟨E, hE⟩ := thm9_1 M hC₁ hC₂_copy
  rw [FondOf] at hE
  use E
  rw [Egocentric, FondOf]
  calc E * E
    _ = M * E := by rw [← hM E]
    _ = E := hE

def Agreeable (A : Bird) : Prop :=
  ∀ B : Bird, ∃ x : Bird, A * x = B * x

-- Every bird is fond of at least one bird (under Conditions 1-2')
theorem thm9_3
    (B : Bird) (hC₁ : Condition1 forest) (hC₂' : Condition2' forest) :
    ∃ x : Bird, FondOf B x := by
  obtain ⟨A, hA⟩ := hC₂'
  obtain ⟨C, hC⟩ := hC₁ B A
  specialize hA C
  obtain ⟨x, hx⟩ := hA
  specialize hC x
  use (A * x)
  rw [FondOf]
  apply Eq.symm
  apply Eq.trans hx hC

-- A mockingbird is agreeable
theorem thm9_3_bonus
    (M : Bird) (hM : Mockingbird M) :
    Agreeable M := by
  rw [Mockingbird] at hM
  rw [Agreeable]
  intro B
  specialize hM B
  use B

theorem thm9_4
    (A B C : Bird) (hC_comp : ∀ x : Bird, C * x = A * (B * x))
    (hC_agreeable : Agreeable C) (hC₁ : Condition1 forest) :
    Agreeable A := by
  intro E
  obtain ⟨D, hD⟩ := hC₁ E B
  have h : ∃ x₀ : Bird, C * x₀ = D * x₀ := by apply hC_agreeable
  obtain ⟨x₀, hx₀⟩ := h
  use B * x₀
  rw [← hC_comp, hx₀, hD]

theorem thm9_5
    (A B C : Bird) (hC₁ : Condition1 forest) :
    ∃ D : Bird, ∀ x : Bird, D * x = A * (B * (C * x)) := by
  obtain ⟨E, hE⟩ := hC₁ B C
  obtain ⟨D, hD⟩ := hC₁ A E
  use D
  intro x
  rw [hD x, hE x]


def Compatible (A B : Bird) : Prop :=
  ∃ x y : Bird, A * x = y ∧ B * y = x

-- Any two birds are compatible (under Conditions 1-2)
theorem thm9_6
    (A B : Bird) (hC₁ : Condition1 forest) (hC₂ : Condition2 forest) :
    Compatible A B := by
  obtain ⟨C, hC⟩ := hC₁ B A
  have h : ∃ x : Bird, FondOf C x := thm9_1 C hC₁ hC₂
  obtain ⟨x, hx⟩ := h
  rw [FondOf] at hx
  rw [hC] at hx
  use x, A * x

def Happy (A : Bird) : Prop :=
  Compatible A A

-- Any bird fond of some bird must be happy
theorem thm9_7
    (A : Bird) (hA : ∃ x : Bird, FondOf A x) :
    Happy A := by
  obtain ⟨x, hx⟩ := hA
  rw [FondOf] at hx
  use x, x


def Normal (A : Bird) : Prop :=
  ∃ x : Bird, FondOf A x

-- If some bird is happy, some bird is normal
theorem thm9_8
    (A : Bird) (hA : Happy A) (hC₁ : Condition1 forest) :
    (∃ B : Bird, Normal B) := by
  rw [Happy, Compatible] at hA
  obtain ⟨x, hx⟩ := hA
  obtain ⟨y, hy⟩ := hx
  obtain ⟨B, hB⟩ := hC₁ A A
  use B, x
  rw [FondOf, hB, hy.1]
  exact hy.2


/- Hopeless Egocentricity -/

def FixatedOn (A B : Bird) : Prop :=
  ∀ x : Bird, A * x = B

def HopelesslyEgocentric (A : Bird) : Prop :=
  FixatedOn A A

def Kestrel (K : Bird) : Prop :=
  ∀ x y : Bird, (K * x) * y = x

-- If there is a Kestrel, some bird is hopelessly egocentric (under Conditions 1-2)
theorem thm9
    (K : Bird) (hK : Kestrel K) (hC₁ : Condition1 forest) (hC₂ : Condition2 forest) :
    ∃ A : Bird, HopelesslyEgocentric A := by
  rw [Kestrel] at hK
  obtain ⟨B, hB⟩ := thm9_1 K hC₁ hC₂
  rw [FondOf] at hB
  use B
  rw [HopelesslyEgocentric, FixatedOn]
  intro y
  nth_rw 1 [← hB]
  apply hK

-- Fixation implies fondness
theorem thm9_10
    (x y : Bird) (hf : FixatedOn x y) :
    FondOf x y := by
  rw [FondOf]
  rw [FixatedOn] at hf
  apply hf y

-- Any egocentric Kestrel is hopelessly egocentric
theorem thm9_11
    (K : Bird) (hK : Kestrel K) (egoK : Egocentric K) :
    HopelesslyEgocentric K := by
  rw [Egocentric, FondOf] at egoK
  rw [HopelesslyEgocentric, FixatedOn]
  intro x
  rw [Kestrel] at hK
  specialize hK K x
  nth_rw 1 [← egoK]
  exact hK

theorem thm9_12
    (K x : Bird) (hK : Kestrel K) (ego : Egocentric (K * x)) :
    FondOf K x := by
  rw [Egocentric] at ego
  rw [FondOf] at *
  rw [Kestrel] at hK
  specialize hK x (K * x)
  rw [← ego]
  nth_rw 3 [← hK]

theorem thm9_13
    (A : Bird) (sA : HopelesslyEgocentric A) (x y : Bird) :
    A * x = A * y := by
  rw [HopelesslyEgocentric, FixatedOn] at sA
  rw [sA x, sA y]

theorem thm9_14
    (A : Bird) (sA : HopelesslyEgocentric A) (x y : Bird) :
    (A * x) * y = A := by
  rw [HopelesslyEgocentric, FixatedOn] at sA
  rw [sA x, sA y]

-- Hopeless Egocentricity is contagious
theorem thm9_15
    (A : Bird) (sA : HopelesslyEgocentric A) (x : Bird) :
    HopelesslyEgocentric (A * x) := by
  rw [HopelesslyEgocentric, FixatedOn] at *
  rw [sA x]
  exact sA

-- Left cancellation law for Kestrels
theorem thm9_16
    (K : Bird) (hK : Kestrel K) (x y : Bird) (eq : K * x = K * y) :
    x = y := by
  rw [Kestrel] at hK
  have kxy : (K * x * y = K * y * y) := by rw [eq]
  rw [← hK x y]
  nth_rw 2 [← hK y y]
  exact kxy

-- No bird can be fixated on more than one bird
theorem thm9_17
    (x y z : Bird) (fxy : FixatedOn x y) (fxz : FixatedOn x z) :
    y = z := by
  rw [FixatedOn] at *
  rw [← fxy x, ← fxz x]

theorem thm9_18
    (K x : Bird) (hK : Kestrel K) (f : FondOf K (K * x)) :
    FondOf K x := by
  rw [FondOf] at *
  apply thm9_16 K hK (K * x) x f

-- Any egocentric Kestrel must be extremely lonely
theorem thm9_19
    (K x : Bird) (hK : Kestrel K) (ego : Egocentric K) :
    x = K := by
  have sego : HopelesslyEgocentric K := thm9_11 K hK ego
  rw [HopelesslyEgocentric, FixatedOn] at sego
  rw [Egocentric, FondOf] at ego
  specialize sego x
  have h : K * x * K = K := by rw [sego, ego]
  rw [Kestrel] at hK
  specialize hK x K
  rw [← hK]
  nth_rw 3 [← h]


/- Identity Birds -/

def Identity (I : Bird) : Prop :=
  ∀ x : Bird, I * x = x

-- Every bird must be fond of at least one bird if there is an Identity bird
theorem thm9_20
    (I : Bird) (hI : Identity I) (cI : Agreeable I) :
    ∀ x : Bird, ∃ y : Bird, FondOf x y := by
  rw [Identity] at hI
  rw [Agreeable] at cI
  intro B
  specialize cI B
  obtain ⟨y, hy⟩ := cI
  rw [hI y] at hy
  use y
  rw [FondOf, ← hy]

theorem thm9_21
    (I : Bird) (hI : Identity I)
    (h : (∀ x : Bird, ∃ y : Bird, FondOf x y)) :
    Agreeable I := by
  rw [Agreeable]
  intro B
  specialize h B
  obtain ⟨x, hx⟩ := h
  rw [FondOf] at hx
  use x
  rw [hx, hI]

theorem thm9_22_1
    (I : Bird) (hI : Identity I)
    (h : ∀ x y : Bird, Compatible x y) (x : Bird):
    Normal x := by
  rw [Normal]
  specialize h x I
  rw [Compatible] at h
  obtain ⟨x1, hx1⟩ := h
  obtain ⟨y, hy⟩ := hx1
  use x1
  rw [FondOf]
  rw [hy.1, ← hy.2, hI]

theorem thm9_22_2
    (I : Bird) (hI : Identity I)
    (h : ∀ x y : Bird, Compatible x y) :
    Agreeable I := by
  intro y
  have h1 : Normal y := thm9_22_1 I hI h y
  rw [Normal] at h1
  obtain ⟨x, hx⟩ := h1
  use x
  rw [hI, hx]

theorem thm9_23
    (I : Bird) (hI : Identity I)
    (heI : HopelesslyEgocentric I) (x : Bird) :
    x = I := by
  rw [HopelesslyEgocentric, FixatedOn] at *
  specialize heI x
  rw [hI] at heI
  exact heI


/- Larks -/

def Lark (L : Bird) : Prop := ∀ x y : Bird, L * x * y = x * (y * y)

-- A mockingbird from L, I
theorem thm9_24
    (L : Bird) (hL : Lark L) (I : Bird) (hI : Identity I) :
    ∃ M : Bird, Mockingbird M := by
  use (L * I)
  rw [Mockingbird]
  intro x
  rw [hL, hI]

-- If there is a Lark, every bird must be fond of at least one bird
theorem thm9_25
    (L : Bird) (hL : Lark L) (x : Bird) :
    (∃ y : Bird, FondOf x y) := by
  rw [Lark] at hL
  specialize hL x (L * x)
  use L * x * (L * x)
  rw [FondOf]
  apply Eq.symm
  exact hL

-- If a hopelessly egocentric Lark exists, every bird is fond of it
theorem thm9_26
    (L : Bird) (hL : Lark L) (hego : HopelesslyEgocentric L) (x : Bird) :
    FondOf x L := by
  have h : L * x * (L * x) = x * ((L * x) * (L * x)) := by apply hL
  have h1 : L * x = L := by apply hego
  rw [h1] at h
  rw [hego L] at h
  apply Eq.symm
  exact h

-- If no bird can be both a Lark and a Kestrel, no Lark can be fond of a Kestrel
theorem thm9_27
    (L : Bird) (K : Bird) (hL : Lark L) (hK : Kestrel K)
    (neqLK : L ≠ K) (fLK : FondOf L K) :
    False := by
  have hKK : (FondOf K (K * K)) → FondOf K K := by
    apply thm9_18 K K
    exact hK
  rw [FondOf] at fLK
  have h1 : FondOf K (K * K) := by
    rw [FondOf]
    apply Eq.symm
    calc
      K * K = (L * K) * K := by
        have eqK : K * K = K * K := by rfl
        nth_rw 1 [← fLK] at eqK
        apply Eq.symm
        exact eqK
      _ = K * (K * K) := hL K K
  have h2 : FondOf K K := hKK h1
  rw [← Egocentric] at h2
  have eqLK : L = K := by apply thm9_19 K L hK h2
  contradiction

-- If a Kestrel is fond of a Lark L, then every bird is fond of L
theorem thm9_28
    (L : Bird) (K : Bird) (hL : Lark L) (hK : Kestrel K) (fKL : FondOf K L) :
    ∀ x : Bird, FondOf x L := by
  have h : HopelesslyEgocentric L := by
    rw [FondOf] at fKL
    rw [HopelesslyEgocentric, FixatedOn]
    nth_rw 1 [← fKL]
    exact hK L
  apply thm9_26 L hL h

-- If a Lark exists, then an egocentric bird exists
theorem thm9_29
    (L : Bird) (hL : Lark L) :
    ∃ x : Bird, Egocentric x := by
  have h1 : (∀ x : Bird, ∃ y : Bird, FondOf x y) := thm9_25 L hL
  specialize h1 (L * L)
  obtain ⟨y, hy⟩ := h1
  rw [FondOf] at hy
  rw [hL] at hy
  have h2 : y * y = y * y := by rfl
  nth_rw 1 [← hy] at h2
  rw [hL] at h2
  use (y * y)
  exact h2



end SmullyanMockingbird
