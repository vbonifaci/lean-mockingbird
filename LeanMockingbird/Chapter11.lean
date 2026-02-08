import Mathlib.Tactic
import LeanMockingbird.Chapter10
namespace SmullyanMockingbird

/- Chapter 11: Birds Galore -/

variable {Bird : Type} [forest : Forest Bird]


/- Bluebirds -/

def Bluebird (B : Bird) : Prop :=
  ∀ x y z : Bird, B * x * y * z = x * (y * z)

-- Importance of bluebirds
theorem thm11_1
    (B : Bird) (hB : Bluebird B) (C D : Bird) :
    Composes (B * C * D) C D := by
  rw [Composes]
  rw [Bluebird] at hB
  apply hB C D

theorem thm11_2
    (B M : Bird) (hB : Bluebird B) (hM : Mockingbird M) (x : Bird) :
    FondOf x (M * (B * x * M)) := by
  rw [FondOf]
  apply Eq.symm
  have h : Composes (B * x * M) x M := thm11_1 B hB x M
  nth_rw 1 [hM, h]

-- An egocentric bird from B, M
theorem thm11_3
    (B M : Bird) (hB : Bluebird B) (hM : Mockingbird M) :
    Egocentric (M * (B * M * M)) := by
  have h : FondOf M (M * (B * M * M)) := thm11_2 B M hB hM M
  rw [FondOf] at h
  nth_rw 1 [hM] at h
  rw [Egocentric, FondOf]
  exact h

-- An hopelessly egocentric bird from B, K, M
theorem thm11_4
    (B M K : Bird) (hB : Bluebird B) (hM : Mockingbird M) (hK : Kestrel K) :
    HopelesslyEgocentric (M * (B * K * M)) := by
  have h : FondOf K (M * (B * K * M)) := thm11_2 B M hB hM K
  rw [FondOf] at h
  rw [HopelesslyEgocentric, FixatedOn]
  intro x
  have hx : K * (M * (B * K * M)) * x = M * (B * K * M) * x := by rw [h]
  rw [hK] at hx
  apply Eq.symm
  exact hx

/- Some Derivatives of the Bluebird -/

def Dove (D : Bird) : Prop :=
  ∀ x y z w : Bird, D * x * y * z * w = x * y * (z * w)

-- A Dove from B
theorem thm11_5
    (B : Bird) (hB : Bluebird B) :
    ∃ D : Bird, Dove D := by
  use (B * B)
  rw [Dove]
  intro x y z w
  rw [hB, hB]


def Blackbird (B₁ : Bird) : Prop :=
  ∀ x y z w : Bird, B₁ * x * y * z * w = x * (y * z * w)

-- A Blackbird from B
theorem thm11_6
    (B : Bird) (hB : Bluebird B) :
    ∃ B₁ : Bird, Blackbird B₁ := by
  obtain ⟨D, hD⟩ := thm11_5 B hB
  use (D * B)
  rw [Blackbird]
  intro x y z w
  rw [hD, hB]


def Eagle (E : Bird) : Prop :=
  ∀ x y z w v : Bird, E * x * y * z * w * v = x * y * (z * w * v)

-- An Eagle from B
theorem thm11_7
    (B : Bird) (hB : Bluebird B) :
    ∃ E : Bird, Eagle E := by
  obtain ⟨B₁, hB₁⟩ := thm11_6 B hB
  use (B * B₁)
  intro x y z w v
  rw [hB, hB₁]


def Bunting (B₂ : Bird) : Prop :=
  ∀ x y z w v : Bird, B₂ * x * y * z * w * v = x * (y * z * w * v)

-- A Bunting from B
theorem thm11_8
    (B : Bird) (hB : Bluebird B) :
    ∃ B₂ : Bird, Bunting B₂ := by
  obtain ⟨E, hE⟩ := thm11_7 B hB
  use (E * B)
  intro x y z w v
  rw [hE, hB]

/- Dickcissels -/

def Dickcissel (D₁ : Bird) : Prop :=
  ∀ x y z w v : Bird, D₁ * x * y * z * w * v = x * y * z * (w * v)

-- A Dickcissel from B
theorem thm11_9
    (B : Bird) (hB : Bluebird B) :
    ∃ D₁ : Bird, Dickcissel D₁ := by
  obtain ⟨D, hD⟩ := thm11_5 B hB
  use (B * D)
  intro x y z w v
  rw [hB, hD]


def Becard (B₃ : Bird) : Prop :=
  ∀ x y z w : Bird, B₃ * x * y * z * w = x * (y * (z * w))

-- A Becard from B
theorem thm11_10
    (B : Bird) (hB : Bluebird B) :
    ∃ B₃ : Bird, Becard B₃ := by
  obtain ⟨D₁, hD₁⟩ := thm11_9 B hB
  use (D₁ * B)
  intro x y z w
  rw [hD₁, hB]


def Dovekie (D₂ : Bird) : Prop :=
  ∀ x y z w v : Bird, D₂ * x * y * z * w * v = x * (y * z) * (w * v)

-- A Dovekie from B
theorem thm11_11
    (B : Bird) (hB : Bluebird B) :
    ∃ D₂ : Bird, Dovekie D₂ := by
  obtain ⟨B₃, hB₃⟩ := thm11_10 B hB
  use (B₃ * B)
  intro x y z w v
  rw [hB₃, hB]


def BaldEagle (E' : Bird) : Prop :=
  ∀ x y₁ y₂ y₃ z₁ z₂ z₃ : Bird, E' * x * y₁ * y₂ * y₃ * z₁ * z₂ * z₃
  = x * (y₁ * y₂ * y₃) * (z₁ * z₂ * z₃)

-- A BaldEagle from B
theorem thm11_12
    (B : Bird) (hB : Bluebird B) :
    ∃ E' : Bird, BaldEagle E' := by
  obtain ⟨E, hE⟩ := thm11_7 B hB
  use (E * E)
  intro x y₁ y₂ y₃ z₁ z₂ z₃
  rw [hE, hE]


/- Some Other Birds -/

def Warbler (W : Bird) : Prop :=
  ∀ x y : Bird, W * x * y = x * y * y

-- A Mockingbird from W, I
theorem thm11_14
    (W I : Bird) (hW : Warbler W) (hI : Identity I) :
    ∃ M : Bird, Mockingbird M := by
  use (W * I)
  rw [Mockingbird]
  intro x
  rw [hW, hI]

-- An Identity bird from W, K
theorem thm11_15
    (W K : Bird) (hW : Warbler W) (hK : Kestrel K) :
    ∃ I : Bird, Identity I := by
  use (W * K)
  rw [Identity]
  intro x
  rw [hW, hK]

-- A Mockingbird from W, K
theorem thm11_13
    (W K : Bird) (hW : Warbler W) (hK : Kestrel K) :
    ∃ M : Bird, Mockingbird M := by
  rw [Warbler] at hW
  rw [Kestrel] at hK
  obtain ⟨I, hI⟩ := thm11_15 W K hW hK
  obtain ⟨M, hM⟩ := thm11_14 W I hW hI
  use M


def Cardinal (C : Bird) : Prop :=
  ∀ x y z : Bird, C * x * y * z = x * z * y

-- An Identity bird from C, K
theorem thm11_16
    (C K : Bird) (hC : Cardinal C) (hK : Kestrel K) :
    ∃ I : Bird, Identity I := by
  use (C * K * K)
  intro x
  rw [hC, hK]


def Thrush (T : Bird) : Prop :=
  ∀ x y : Bird, T * x * y = y * x

-- A Thrush from C, I
theorem thm11_17
    (C I : Bird) (hC : Cardinal C) (hI : Identity I) :
    ∃ T : Bird, Thrush T := by
  use (C * I)
  intro x y
  rw [hC, hI]

def Commute (x y : Bird) : Prop :=
  x * y = y * x

theorem thm11_18
    (T : Bird) (hT : Thrush T) (h : ∀ x : Bird, ∃ y : Bird, FondOf x y) :
    ∃ A : Bird, ∀ x : Bird, Commute A x := by
  specialize h T
  obtain ⟨y, hy⟩ := h
  use y
  intro x
  rw [Commute]
  nth_rw 1 [← hy, hT]

-- A bird that commutes with every bird, from B, T, M
theorem thm11_19
    (B T M : Bird) (hB : Bluebird B) (hT : Thrush T) (hM : Mockingbird M) :
    ∃ A : Bird, ∀ x : Bird, Commute A x := by
  have h : ∀ x : Bird, ∃ y : Bird, FondOf x y := by
    intro x
    have h1 : FondOf x (M * (B * x * M)) := thm11_2 B M hB hM x
    use (M * (B * x * M))
  apply thm11_18 T hT h


/- Bluebirds and Thrushes -/

def Robin (R : Bird) : Prop :=
  ∀ x y z : Bird, R * x * y * z = y * z * x

-- A Robin from B, T
theorem thm11_20
    (B T : Bird) (hB : Bluebird B) (hT : Thrush T) :
    ∃ R : Bird, Robin R := by
  use (B * B * T)
  intro x y z
  rw [hB, hB, hT]

-- A Cardinal from R
theorem thm11_21
    (R : Bird) (hR : Robin R) :
    ∃ C : Bird, Cardinal C := by
  use (R * R * R)
  intro x y z
  rw [hR, hR, hR]

-- A Cardinal from B, T
theorem thm11_21_bonus
    (B T : Bird) (hB : Bluebird B) (hT : Thrush T) :
    ∃ C : Bird, Cardinal C := by
  use (B * (T * (B * B * T)) * (B * B * T))
  intro x y z
  nth_rw 1 [hB, hT, hB, hB, hT, hB, hB, hT]

theorem thm11_22
    (B T R C : Bird) (hB : Bluebird B) (hT : Thrush T)
    (eqR : R = B * B * T) (eqC : C = R * R * R) (x : Bird) :
    C * x = R * x * R ∧ C * x = B * (T * x) * R := by
    have hR : Robin R := by
      intro x1 y z
      rw [eqR, hB, hB, hT]
    constructor
    · rw [eqC, hR]
    · rw [eqC, hR]
      nth_rw 1 [eqR]
      nth_rw 1 [hB]

-- A Robin from C
theorem thm11_23
    (C : Bird) (hC : Cardinal C) :
    ∃ R : Bird, Robin R := by
  use (C * C)
  intro x y z
  rw [hC, hC]


def Finch (F : Bird) : Prop :=
  ∀ x y z : Bird, F * x * y * z = z * y * x

-- A Finch from B, R
theorem thm11_24
    (B R : Bird) (hB : Bluebird B) (hR : Robin R) :
    ∃ F : Bird, Finch F := by
  obtain ⟨C, hC⟩ := thm11_21 R hR
  use (B * C * R)
  intro x y z
  nth_rw 1 [hB, hC, hR]

-- A Finch from T, E
theorem thm11_25
    (T E : Bird) (hT : Thrush T) (hE : Eagle E) :
    ∃ F : Bird, Finch F := by
  use (E * T * T * E * T)
  intro x y z
  nth_rw 1 [hE, hT, hE, hT, hT]

-- A Finch from B, T
theorem thm11_26
    (B T : Bird) (hB : Bluebird B) (hT : Thrush T) :
    ∃ F : Bird, Finch F := by
  use (B * (T * T) * (B * (B * B * B) * T))
  intro x y z
  nth_rw 1 [hB, hT, hB, hB, hB, hB, hT, hT]


def Vireo (V : Bird) : Prop :=
  ∀ x y z : Bird, V * x * y * z = z * x * y

-- A Vireo from C, F
theorem thm11_27
    (C F : Bird) (hC : Cardinal C) (hF : Finch F) :
    ∃ V : Bird, Vireo V := by
  use C * F
  intro x y z
  nth_rw 1 [hC, hF]

-- A Vireo from F, R
theorem thm11_28
    (F R : Bird) (hF : Finch F) (hR : Robin R) :
    ∃ V : Bird, Vireo V := by
  use R * F * R
  intro x y z
  nth_rw 1 [hR, hR, hF]

-- A Finch from C, V
theorem thm11_29
    (C V : Bird) (hC : Cardinal C) (hV : Vireo V) :
    ∃ F : Bird, Finch F := by
  use C * V
  intro x y z
  nth_rw 1 [hC, hV]

-- An Identity bird from R, K
theorem thm11_30
    (R K : Bird) (hR : Robin R) (hK : Kestrel K) :
    ∃ I : Bird, Identity I := by
  use R * R * K
  intro x
  nth_rw 1 [hR, hK]


/- Some Relatives -/

/- Note: we use C₁, C₂, ... instead of C*, C**, etc.,
as the latter are not valid Lean identifiers -/

def CardinalOnceRemoved (C₁ : Bird) : Prop :=
  ∀ x y z w : Bird, C₁ * x * y * z * w = x * y * w * z

-- A Cardinal once removed from B, C
theorem thm11_31
    (B C : Bird) (hB : Bluebird B) (hC : Cardinal C) :
    ∃ C₁ : Bird, CardinalOnceRemoved C₁ := by
  use B * C
  rw [CardinalOnceRemoved]
  intro x y z w
  rw [hB, hC]


def RobinOnceRemoved (R₁ : Bird) : Prop :=
  ∀ x y z w : Bird, R₁ * x * y * z * w = x * z * w * y

-- A Robin once removed from B, C
theorem thm11_32
    (B C : Bird) (hB : Bluebird B) (hC : Cardinal C) :
    ∃ R₁ : Bird, RobinOnceRemoved R₁ := by
  obtain ⟨C₁, hC₁⟩ := thm11_31 B C hB hC
  use C₁ * C₁
  rw [RobinOnceRemoved]
  intro x y z w
  rw [hC₁, hC₁]

def FinchOnceRemoved (F₁ : Bird) : Prop :=
  ∀ x y z w : Bird, F₁ * x * y * z * w = x * w * z * y

-- A Finch once removed from B, C
theorem thm11_33
    (B C : Bird) (hB : Bluebird B) (hC : Cardinal C) :
    ∃ F₁ : Bird, FinchOnceRemoved F₁ := by
  obtain ⟨C₁, hC₁⟩ := thm11_32 B C hB hC
  use B * C₁ * C
  rw [FinchOnceRemoved]
  intro x y z w
  rw [hB, hC₁, hC]

def VireoOnceRemoved (V₁ : Bird) : Prop :=
-- Note: this fixes a typo in OUP's 2000 reissue of the book
  ∀ x y z w : Bird, V₁ * x * y * z * w = x * w * y * z

-- A Vireo once removed from B, C
theorem thm11_34
    (B C : Bird) (hB : Bluebird B) (hC : Cardinal C) :
    ∃ V₁ : Bird, VireoOnceRemoved V₁ := by
  obtain ⟨F₁, hF₁⟩ := thm11_33 B C hB hC
  use B * C * F₁
  rw [VireoOnceRemoved]
  intro x y z w
  rw [hB, hC, hF₁]

theorem thm11_35
    (B C : Bird) (hB : Bluebird B) (hC : Cardinal C) :
    ∃ C₂ R₂ F₂ V₂ : Bird, ∀ x y z₁ z₂ z₃ : Bird,
      C₂ * x * y * z₁ * z₂ * z₃ = x * y * z₁ * z₃ * z₂ ∧
      R₂ * x * y * z₁ * z₂ * z₃ = x * y * z₂ * z₃ * z₁ ∧
      F₂ * x * y * z₁ * z₂ * z₃ = x * y * z₃ * z₂ * z₁ ∧
      V₂ * x * y * z₁ * z₂ * z₃ = x * y * z₃ * z₁ * z₂ := by
  obtain ⟨C₁, hC₁⟩ := thm11_31 B C hB hC
  obtain ⟨R₁, hR₁⟩ := thm11_32 B C hB hC
  obtain ⟨F₁, hF₁⟩ := thm11_33 B C hB hC
  obtain ⟨V₁, hV₁⟩ := thm11_34 B C hB hC
  use B * C₁
  use B * R₁
  use B * F₁
  use B * V₁
  intro x y z₁ z₂ z₃
  constructor
  · rw [hB, hC₁]
  · constructor
    · rw [hB, hR₁]
    · constructor
      · rw [hB, hF₁]
      · rw [hB, hV₁]


-- A Vireo from C₁, T
theorem thm11_36
    (C₁ T : Bird) (hC₁ : CardinalOnceRemoved C₁) (hT : Thrush T) :
    ∃ V : Bird, Vireo V := by
  use C₁ * T
  intro x y z
  rw [hC₁, hT]


/- Queer Birds -/

def QueerBird (Q : Bird) : Prop :=
  ∀ x y z : Bird, Q * x * y * z = y * (x * z)

-- A Queer bird from B, T
theorem thm11_37
    (B T : Bird) (hB : Bluebird B) (hT : Thrush T) :
    ∃ Q : Bird, QueerBird Q := by
  obtain ⟨C, hC⟩ := thm11_21_bonus B T hB hT
  use C * B
  intro x y z
  rw [hC, hB]


def QuixoticBird (Q₁ : Bird) : Prop :=
  ∀ x y z : Bird, Q₁ * x * y * z = x * (z * y)

-- A Quixotic bird from B, T
theorem thm11_38
    (B T : Bird) (hB : Bluebird B) (hT : Thrush T) :
    ∃ Q₁ : Bird, QuixoticBird Q₁ := by
  obtain ⟨C, hC⟩ := thm11_21_bonus B T hB hT
  obtain ⟨C₁, hC₁⟩ := thm11_31 B C hB hC
  use C₁ * B
  intro x y z
  rw [hC₁, hB]


def QuizzicalBird (Q₂ : Bird) : Prop :=
  ∀ x y z : Bird, Q₂ * x * y * z = y * (z * x)

-- A Quizzical bird from B, T
theorem thm11_39
    (B T : Bird) (hB : Bluebird B) (hT : Thrush T) :
    ∃ Q₂ : Bird, QuizzicalBird Q₂ := by
  obtain ⟨C, hC⟩ := thm11_21_bonus B T hB hT
  obtain ⟨R₁, hR₁⟩ := thm11_32 B C hB hC
  use R₁ * B
  intro x y z
  rw [hR₁, hB]

-- A Quizzical bird from C, Q₁
theorem thm11_40_1
    (C Q₁ : Bird) (hC : Cardinal C) (hQ₁ : QuixoticBird Q₁) :
    ∃ Q₂ : Bird, QuizzicalBird Q₂ := by
  use C * Q₁
  intro x y z
  --calc C * Q₁ * x * y * z
  --  _ = Q₁ * y * x * z := by apply hC
  rw [hC, hQ₁]

-- A Quixotic bird from C, Q₂
theorem thm11_40_2
    (C Q₂ : Bird) (hC : Cardinal C) (hQ₂ : QuizzicalBird Q₂) :
    ∃ Q₁ : Bird, QuixoticBird Q₁ := by
  use C * Q₂
  intro x y z
  rw [hC, hQ₂]


def QuirkyBird (Q₃ : Bird) : Prop :=
  ∀ x y z : Bird, Q₃ * x * y * z = z * (x * y)

-- A Quirky bird from B, T
theorem thm11_41
    (B T : Bird) (hB : Bluebird B) (hT : Thrush T) :
    ∃ Q₃ : Bird, QuirkyBird Q₃ := by
  obtain ⟨C, hC⟩ := thm11_21_bonus B T hB hT
  obtain ⟨V₁, hV₁⟩ := thm11_34 B C hB hC
  use V₁ * B
  intro x y z
  rw [hV₁, hB]


def QuackyBird (Q₄ : Bird) : Prop :=
  ∀ x y z : Bird, Q₄ * x * y * z = z * (y * x)

-- A Quacky bird from B, T
theorem thm11_42
    (B T : Bird) (hB : Bluebird B) (hT : Thrush T) :
    ∃ Q₄ : Bird, QuackyBird Q₄ := by
  obtain ⟨C, hC⟩ := thm11_21_bonus B T hB hT
  obtain ⟨F₁, hF₁⟩ := thm11_33 B C hB hC
  use F₁ * B
  intro x y z
  rw [hF₁, hB]

-- A Quacky bird from C, Q₃
theorem thm11_43_1
    (C Q₃ : Bird) (hC : Cardinal C) (hQ₃ : QuirkyBird Q₃) :
    ∃ Q₄ : Bird, QuackyBird Q₄ := by
  use C * Q₃
  intro x y z
  rw [hC, hQ₃]

-- A Quirky bird from C, Q₄
theorem thm11_43_2
    (C Q₄ : Bird) (hC : Cardinal C) (hQ₄ : QuackyBird Q₄) :
    ∃ Q₃ : Bird, QuirkyBird Q₃ := by
  use C * Q₄
  intro x y z
  rw [hC, hQ₄]

-- A Quacky bird from Q₁, T
theorem thm11_44
    (Q₁ T : Bird) (hQ₁ : QuixoticBird Q₁) (hT : Thrush T) :
    ∃ Q₄ : Bird, QuackyBird Q₄ := by
  use Q₁ * T
  intro x y z
  rw [hQ₁, hT]

-- A Bluebird from Q, T
theorem thm11_45
    (Q T : Bird) (hQ : QueerBird Q) (hT : Thrush T) :
    ∃ B : Bird, Bluebird B := by
  use Q * T * (Q * Q)
  intro x y z
  rw [hQ, hQ, hT, hQ]

-- A Cardinal from Q, T
theorem thm11_46
    (Q T : Bird) (hQ : QueerBird Q) (hT : Thrush T) :
    ∃ C : Bird, Cardinal C := by
  use Q * Q * (Q * T)
  intro x y z
  rw [hQ, hQ, hQ, hT]


def Goldfinch (G : Bird) : Prop :=
  ∀ x y z w : Bird, G * x * y * z * w = x * w * (y * z)

-- A Goldfinch from B, T
theorem thm11_47
    (B T : Bird) (hB : Bluebird B) (hT : Thrush T) :
    ∃ G : Bird, Goldfinch G := by
  obtain ⟨C, hC⟩ := thm11_21_bonus B T hB hT
  --use V₂ * (B * B) -- this also works
  use B * B * C
  intro x y z w
  rw [hB, hB, hC]



end SmullyanMockingbird
