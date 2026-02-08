import Mathlib.Tactic
import LeanMockingbird.Chapter12
namespace SmullyanMockingbird

/- Chapter 13: A Gallery of Sage Birds -/

variable {Bird : Type} [forest : Forest Bird]


/- Some Sage Birds -/

-- A sage bird from M, B, R
theorem thm13_1
    (B M R : Bird) (hB : Bluebird B) (hM : Mockingbird M) (hR : Robin R) :
    ∃ Θ : Bird, SageBird Θ := by
  use B * M * (R * M * B)
  rw [SageBird]
  intro x y hx
  rw [FondOf, ← hx]
  apply Eq.symm
  nth_rw 1 [hB, hM, hR, hB, hB]

-- A sage bird from M, B, C
theorem thm13_2
    (B M C : Bird) (hB : Bluebird B) (hM : Mockingbird M) (hC : Cardinal C) :
    ∃ Θ : Bird, SageBird Θ := by
  use B * M * (C * B * M)
  rw [SageBird]
  intro x y hx
  rw [FondOf, ← hx]
  apply Eq.symm
  nth_rw 1 [hB, hM, hC, hB, hB]

-- A sage bird from M, B, L
theorem thm13_3
    (B M L : Bird) (hB : Bluebird B) (hM : Mockingbird M) (hL : Lark L) :
    ∃ Θ : Bird, SageBird Θ := by
  use B * M * L
  rw [SageBird]
  intro x y hx
  rw [FondOf, ← hx]
  apply Eq.symm
  rw [hB, hM]
  nth_rw 1 [hL]

-- A sage bird from M, B, W
theorem thm13_4
    (B M W : Bird) (hB : Bluebird B) (hM : Mockingbird M) (hW : Warbler W) :
    ∃ Θ : Bird, SageBird Θ := by
  obtain ⟨L, hL⟩ := thm12_3 B W hB hW
  apply thm13_3 B M L hB hM hL

-- thm13_5 postponed to thm13_7

/- Enter the Queer Bird -/

-- A sage bird from Q, L, W
theorem thm13_6
    (Q L W : Bird) (hQ : QueerBird Q) (hL : Lark L) (hW : Warbler W) :
    ∃ Θ : Bird, SageBird Θ := by
  use W * (Q * L * (Q * L))
  intro x y hx
  rw [FondOf, ← hx]
  apply Eq.symm
  rw [hW, hQ, hQ]
  nth_rw 1 [hL]

-- A sage bird from B, C, W
theorem thm13_7
    (B C W : Bird) (hB : Bluebird B) (hC : Cardinal C) (hW : Warbler W) :
    ∃ Θ : Bird, SageBird Θ := by
  obtain ⟨L, hL⟩ := thm12_3 B W hB hW
  have hQ : QueerBird (C * B) := by
    rw [QueerBird]
    intro x y z
    rw [hC, hB]
  apply thm13_6 (C * B) L W hQ hL hW

-- A sage bird from Q, M
theorem thm13_8
    (Q M : Bird) (hQ : QueerBird Q) (hM : Mockingbird M) :
    ∃ Θ : Bird, SageBird Θ := by
  obtain ⟨L, hL⟩ := thm12_4 M Q hM hQ
  use Q * L * M
  intro x y hx
  rw [FondOf, ← hx]
  apply Eq.symm
  rw [hQ, hM]
  nth_rw 1 [hL]

/- Curry's Sage Bird -/

-- A sage bird from S, L
theorem thm13_9
    (S L : Bird) (hS : Starling S) (hL : Lark L) :
    ∃ Θ : Bird, SageBird Θ := by
  use S * L * L
  intro x y hx
  rw [FondOf, ← hx]
  apply Eq.symm
  rw [hS]
  nth_rw 1 [hL]

-- A sage bird from B, W, S
theorem thm13_10
    (B W S : Bird) (hB : Bluebird B) (hW : Warbler W) (hS : Starling S) :
    ∃ Θ : Bird, SageBird Θ := by
  let L : Bird := B * W * B
  have hL : Lark L := by
    rw [Lark]
    intro x y
    simp [L]
    rw [hB, hW, hB]
  apply thm13_9 S L hS hL

/- The Turing Bird -/

def TuringBird (U : Bird) : Prop :=
  ∀ x y : Bird, U * x * y = y * (x * x * y)

-- A Turing bird from B, M, T
theorem thm13_11
    (B M T : Bird) (hB : Bluebird B) (hM : Mockingbird M) (hT : Thrush T) :
    ∃ U : Bird, TuringBird U := by
  obtain ⟨W, hW⟩ := thm12_7 B T M hB hT hM
  obtain ⟨L, hL⟩ := thm12_3 B W hB hW
  obtain ⟨Q, hQ⟩ := thm11_37 B T hB hT
  use B * W * (L * Q)
  rw [TuringBird]
  intro x y
  rw [hB, hW, hL, hQ]

-- A sage bird from U
theorem thm13_12
    (U : Bird) (hU : TuringBird U) :
    ∃ Θ : Bird, SageBird Θ := by
  use U * U
  rw [SageBird]
  intro x y hx
  rw [FondOf, ← hx]
  apply Eq.symm
  nth_rw 1 [hU]


/- Owls -/

def Owl (O : Bird) : Prop :=
  ∀ x y : Bird, O * x * y = y * (x * y)

-- An owl from Q, W
theorem thm13_13
    (Q W : Bird) (hQ : QueerBird Q) (hW : Warbler W) :
    ∃ O : Bird, Owl O := by
  use Q * Q * W
  intro x y
  rw [hQ, hW, hQ]

-- A Turing bird from O, L
theorem thm13_14
    (O L : Bird) (hO : Owl O) (hL : Lark L) :
    ∃ U : Bird, TuringBird U := by
  use L * O
  intro x y
  rw [hL, hO]

-- A Sage bird from O, L
theorem thm13_14_corollary
    (O L : Bird) (hO : Owl O) (hL : Lark L) :
    ∃ Θ : Bird, SageBird Θ := by
  obtain ⟨U, hU⟩ := thm13_14 O L hO hL
  apply thm13_12 U hU

-- A Mockingbird from O, I
theorem thm13_15
    (O I : Bird) (hO : Owl O) (hI : Identity I) :
    ∃ M : Bird, Mockingbird M := by
  use O * I
  intro x
  rw [hO, hI]

-- An Owl from S, I
theorem thm13_16
    (S I : Bird) (hS : Starling S) (hI : Identity I) :
    ∃ O : Bird, Owl O := by
  use S * I
  intro x y
  rw [hS, hI]


/- Why Owls Are So Interesting -/

-- If x is fond of y, x is fond of xy
theorem thm13_17
    (x y : Bird) (hx : FondOf x y) :
    FondOf x (x * y) := by
  rw [FondOf] at *
  nth_rw 1 [hx]

-- If Θ is a sage bird, OΘ is a sage bird
theorem thm13_18
    (O Θ : Bird) (hO : Owl O) (hΘ : SageBird Θ) :
    SageBird (O * Θ) := by
  rw [SageBird] at *
  intro x y h
  rw [← h]
  rw [hO]
  specialize hΘ x (Θ * x)
  specialize hΘ rfl
  apply thm13_17 x (Θ * x)
  exact hΘ

-- If Θ is a sage bird, ΘO is a sage bird
theorem thm13_19
    (O Θ : Bird) (hO : Owl O) (hΘ : SageBird Θ) :
    SageBird (Θ * O) := by
  rw [SageBird] at *
  intro x y h
  rw [← h]
  rw [FondOf]
  nth_rw 1 [← hO]
  specialize hΘ O (Θ * O)
  specialize hΘ rfl
  nth_rw 1 [hΘ]

-- An owl is fond only of sage birds
theorem thm13_20
    (O A : Bird) (hO : Owl O) (heq : O * A = A) :
    SageBird A := by
  rw [SageBird]
  intro x y hA
  rw [← hA, FondOf]
  nth_rw 2 [← heq]
  rw [hO]


def Choosy (A : Bird) : Prop :=
  ∀ x : Bird, FondOf A x → SageBird x

-- For any choosy bird A, ΘA is a sage bird
theorem thm13_21
    (A Θ : Bird) (hA : Choosy A) (hΘ : SageBird Θ) :
    SageBird (Θ * A) := by
  have h : FondOf A (Θ * A) := by
    apply hΘ
    rfl
  apply hA
  exact h


def Similar (A₁ A₂ : Bird) : Prop :=
  ∀ x : Bird, A₁ * x = A₂ * x

-- OΘ is similar to Θ
theorem thm13_22
    (O Θ : Bird) (hO : Owl O) (hΘ : SageBird Θ) :
    Similar (O * Θ) Θ := by
  intro x
  rw [hO]
  nth_rw 1 [hΘ]
  rfl


def Extensional (forest : Forest Bird) : Prop :=
  ∀ A₁ A₂ : Bird, Similar A₁ A₂ → A₁ = A₂

-- In an extensional forest, an owl is fond of all sage birds
theorem thm13_23
    (O : Bird) (hO : Owl O) (hext : Extensional forest) :
    ∀ Θ : Bird, SageBird Θ → FondOf O Θ := by
  intro Θ hΘ
  have h : Similar (O * Θ) Θ := thm13_22 O Θ hO hΘ
  have eq : O * Θ = Θ := hext (O * Θ) Θ h
  rw [FondOf]
  exact eq




end SmullyanMockingbird
