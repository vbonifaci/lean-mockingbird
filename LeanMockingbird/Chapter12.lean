import Mathlib.Tactic
import LeanMockingbird.Chapter11
namespace SmullyanMockingbird

/- Chapter 12: Mockingbirds, Warblers, and Starlings -/

variable {Bird : Type} [forest : Forest Bird]


/- More on Mockingbirds -/

def DoubleMockingbird (M₂ : Bird) : Prop :=
  ∀ x y : Bird, M₂ * x * y = x * y * (x * y)

-- A Double Mockingbird from B, T
theorem thm12_1
    (B M : Bird) (hB : Bluebird B) (hM : Mockingbird M) :
    ∃ M₂ : Bird, DoubleMockingbird M₂ := by
  use B * M
  intro x y
  rw [hB, hM]

-- A Lark from B, C, M
theorem thm12_2
    (B C M : Bird) (hB : Bluebird B) (hC : Cardinal C) (hM : Mockingbird M) :
    ∃ L : Bird, Lark L := by
  use C * B * M
  intro x y
  rw [hC, hB, hM]

-- A Lark from B, W
theorem thm12_3
    (B W : Bird) (hB : Bluebird B) (hW : Warbler W) :
    ∃ L : Bird, Lark L := by
  use B * W * B
  intro x y
  rw [hB, hW, hB]

-- A Lark from M, Q
theorem thm12_4
    (M Q : Bird) (hM : Mockingbird M) (hQ : QueerBird Q) :
    ∃ L : Bird, Lark L := by
  use Q * M
  intro x y
  rw [hQ, hM]


/- Warblers -/

def ConverseWarbler (W' : Bird) : Prop :=
  ∀ x y : Bird, W' * x * y = y * x * x

-- A Converse Warbler from B, M, R
theorem thm12_5
    (B M R : Bird) (hB : Bluebird B) (hM : Mockingbird M) (hR : Robin R) :
    ∃ W' : Bird, ConverseWarbler W' := by
  use B * M * R
  intro x y
  rw [hB, hM, hR, hR]

-- A Warbler from B, R, C, M
theorem thm12_6
    (B R C M : Bird) (hB : Bluebird B) (hR : Robin R)
    (hC : Cardinal C) (hM : Mockingbird M) :
    ∃ W : Bird, Warbler W := by
  use C * (B * M * R)
  intro x y
  rw [hC, hB, hM, hR, hR]

-- A Warbler from B, T, M
theorem thm12_7
    (B T M : Bird) (hB : Bluebird B) (hT : Thrush T) (hM : Mockingbird M) :
    ∃ W : Bird, Warbler W := by
  have ⟨C, hC⟩ := thm11_21_bonus B T hB hT
  have ⟨R, hR⟩ := thm11_23 C hC
  apply thm12_6 B R C M hB hR hC hM

-- A Mockingbird from T, W
theorem thm12_8
    (T W : Bird) (hT : Thrush T) (hW : Warbler W) :
    ∃ M : Bird, Mockingbird M := by
  use W * T
  intro x
  rw [hW, hT]

-- A Warbler once removed from B, T, M
theorem thm12_9_1
    (B T M : Bird) (hB : Bluebird B) (hT : Thrush T) (hM : Mockingbird M) :
    ∃ W₁ : Bird, ∀ x y z : Bird, W₁ * x * y * z = x * y * z * z := by
  obtain ⟨W, hW⟩ := thm12_7 B T M hB hT hM
  use B * W
  intro x y z
  rw [hB, hW]

-- A Warbler twice removed from B, T, M
theorem thm12_9_2
    (B T M : Bird) (hB : Bluebird B) (hT : Thrush T) (hM : Mockingbird M) :
    ∃ W₂ : Bird, ∀ x y z w : Bird, W₂ * x * y * z * w = x * y * z * w * w := by
  obtain ⟨W₁, hW₁⟩ := thm12_9_1 B T M hB hT hM
  use B * W₁
  intro x y z w
  rw [hB, hW₁]


def Hummingbird (H : Bird) : Prop :=
  ∀ x y z : Bird, H * x * y * z = x * y * z * y

-- A Hummingbird from B, T, M
theorem thm12_10
    (B T M : Bird) (hB : Bluebird B) (hT : Thrush T) (hM : Mockingbird M) :
    ∃ H : Bird, Hummingbird H := by
  obtain ⟨C, hC⟩ := thm11_21_bonus B T hB hT
  obtain ⟨C₁, hC₁⟩ := thm11_31 B C hB hC
  obtain ⟨W₁, hW₁⟩ := thm12_9_1 B T M hB hT hM
  use W₁ * C₁
  intro x y z
  rw [hW₁, hC₁]

-- A Hummingbird from B, C, W
theorem thm12_10_bonus
    (B C W : Bird) (hB : Bluebird B) (hC : Cardinal C) (hW : Warbler W) :
    ∃ H : Bird, Hummingbird H := by
  use B * W * (B * C)
  intro x y z
  rw [hB, hW, hB, hC]

-- A Warbler from C, H
theorem thm12_11
    (C H : Bird) (hC : Cardinal C) (hH : Hummingbird H) :
    ∃ W : Bird, Warbler W := by
  obtain ⟨R, hR⟩ := thm11_23 C hC
  use C * (H * R)
  intro x y
  rw [hC, hH, hR]


/- Starlings -/

def Starling (S : Bird) : Prop :=
  ∀ x y z : Bird, S * x * y * z = x * z * (y * z)

-- A Starling from B, T, M
theorem thm12_12_1
    (B T M : Bird) (hB : Bluebird B) (hT : Thrush T) (hM : Mockingbird M) :
    ∃ S : Bird, Starling S := by
  obtain ⟨W, hW⟩ := thm12_7 B T M hB hT hM
  obtain ⟨G, hG⟩ := thm11_47 B T hB hT
  use B * (B * W) * G
  intro x y z
  rw [hB, hB, hW, hG]

-- A Starling from B, C, W
theorem thm12_12_2
    (B C W : Bird) (hB : Bluebird B) (hC : Cardinal C) (hW : Warbler W) :
    ∃ S : Bird, Starling S := by
  have h : ∃ G : Bird, Goldfinch G := by
    use B * B * C
    intro x y z w
    rw [hB, hB, hC]
  obtain ⟨G, hG⟩ := h
  use B * (B * W) * G
  intro x y z
  rw [hB, hB, hW, hG]

-- A Hummingbird from S, R
theorem thm12_13
    (S R : Bird) (hS : Starling S) (hR : Robin R) :
    ∃ H : Bird, Hummingbird H := by
  use S * R
  intro x y z
  rw [hS, hR]

-- A Warbler from S, R
theorem thm12_14_1
    (S R : Bird) (hS : Starling S) (hR : Robin R) :
    ∃ W : Bird, Warbler W := by
  obtain ⟨C, hC⟩ := thm11_21 R hR
  obtain ⟨H, hH⟩ := thm12_13 S R hS hR
  exact thm12_11 C H hC hH

-- A Warbler from S, C
theorem thm12_14_2
    (S C : Bird) (hS : Starling S) (hC : Cardinal C) :
    ∃ W : Bird, Warbler W := by
  obtain ⟨R, hR⟩ := thm11_23 C hC
  obtain ⟨H, hH⟩ := thm12_13 S R hS hR
  exact thm12_11 C H hC hH

-- A Warbler from S, T
theorem thm12_15
    (S T : Bird) (hS : Starling S) (hT : Thrush T) :
    ∃ W : Bird, Warbler W := by
  use S * T
  intro x y
  rw [hS, hT]

-- A Mockingbird from S, T
theorem thm12_16
    (S T : Bird) (hS : Starling S) (hT : Thrush T) :
    ∃ M : Bird, Mockingbird M := by
  use S * T * T
  intro x
  rw [hS, hT, hT]


/- Exercises -/

theorem exercise12_1_a
    (B T : Bird) (hB : Bluebird B) (hT : Thrush T) :
    ∃ G₁ : Bird, ∀ x y z w v : Bird,
    G₁ * x * y * z * w * v = x * y * v * (z * w) := by
  obtain ⟨G, hG⟩ := thm11_47 B T hB hT
  use B * G
  intro x y z w v
  rw [hB, hG]

theorem exercise12_1_b
    (G₁ B M : Bird)
    (hG₁ : ∀ x y z w v : Bird, G₁ * x * y * z * w * v = x * y * v * (z * w))
    (hB : Bluebird B) (hM : Mockingbird M) :
    ∃ G₂ : Bird, ∀ x y z w : Bird,
    G₂ * x * y * z * w = x * w * (x * w) * (y * z) := by
  use G₁ * (B * M)
  intro x y z w
  rw [hG₁, hB, hM]

theorem exercise12_1_c
    (B T I : Bird) (hB : Bluebird B) (hT : Thrush T) :
    ∃ I₂ : Bird, ∀ x : Bird, I₂ * x = x * I * I := by
  use B * (T * I) * (T * I)
  intro x
  rw [hB, hT, hT]

theorem exercise12_1_d
    (x I I₂ F : Bird) (hI : Identity I) (hF : Finch F)
    (hI₂ : (∀ x : Bird, I₂ * x = x * I * I)) :
    I₂ * (F * x) = x := by
  rw [hI₂, hF, hI, hI]

theorem exercise12_1_e
    (G₂ F Q I I₂ : Bird)
    (hG₂ : (∀ x y z w : Bird, G₂ * x * y * z * w = x * w * (x * w) * (y * z)))
    (hF : Finch F) (hQ : QueerBird Q) (hI : Identity I)
    (hI₂ : (∀ x : Bird, I₂ * x = x * I * I)) :
    Warbler (G₂ * F * (Q * I₂)) := by
  intro x y
  rw [hG₂, hF, hQ, hI₂, hF, hI, hI]

-- Conclusion of points (a)-(e)
theorem exercise12_1
    (B T M I : Bird) (hB : Bluebird B) (hT : Thrush T)
    (hM : Mockingbird M) (hI : Identity I) :
    ∃ W : Bird, Warbler W := by
  obtain ⟨G₁, hG₁⟩ := exercise12_1_a B T hB hT
  obtain ⟨G₂, hG₂⟩ := exercise12_1_b G₁ B M hG₁ hB hM
  obtain ⟨I₂, hI₂⟩ := exercise12_1_c B T I hB hT
  obtain ⟨F, hF⟩ := thm11_26 B T hB hT
  obtain ⟨Q, hQ⟩ := thm11_37 B T hB hT
  use G₂ * F * (Q * I₂)
  exact exercise12_1_e G₂ F Q I I₂ hG₂ hF hQ hI hI₂


theorem exercise12_2
    (B C W : Bird) (hB : Bluebird B) (hC : Cardinal C) (hW : Warbler W) :
    ∃ S : Bird, Starling S := by
  use B * (B * (B * W ) * C ) * (B * B)
  intro x y z
  rw [hB, hB, hB, hW, hC, hB, hB]


def Phoenix (Φ : Bird) : Prop :=
  ∀ x y z w : Bird, Φ * x * y * z * w = x * (y * w) * (z * w)

theorem exercise12_3
    (B S : Bird) (hB : Bluebird B) (hS : Starling S) :
    ∃ Φ : Bird, Phoenix Φ := by
  use B * (B * S) * B
  intro x y z w
  rw [hB, hB, hS, hB]


def PsiBird (Ψ : Bird) : Prop :=
  ∀ x y z w : Bird, Ψ * x * y * z * w = x * (y * z) * (y * w)

theorem exercise12_4
    (B C W : Bird) (hB : Bluebird B) (hC : Cardinal C) (hW : Warbler W) :
    ∃ Ψ : Bird, PsiBird Ψ := by
  obtain ⟨H, hH⟩ := thm12_10_bonus B C W hB hC hW
  obtain ⟨D₂, hD₂⟩ := thm11_11 B hB
  use B * H * D₂
  intro x y z w
  rw [hB, hH, hD₂]

theorem exercise12_5_a
-- Note: this fixes a typo in OUP's 2000 reissue of the book
    (Φ B : Bird) (hΦ : Phoenix Φ) (hB : Bluebird B) :
    ∃ Γ : Bird, ∀ x y z w v : Bird, Γ * x * y * z * w * v = y * (z * w) * (x * y * z * w * v) := by
  use Φ * (Φ * (Φ * B)) * B
  intro x y z w v
  rw [hΦ, hΦ, hΦ, hB, hB]

theorem exercise12_5_b
    (Γ K : Bird)
    (hΓ : ∀ x y z w v : Bird, Γ * x * y * z * w * v = y * (z * w) * (x * y * z * w * v))
    (hK : Kestrel K) :
    ∃ Ψ : Bird, PsiBird Ψ := by
  use Γ * (K * K)
  intro x y z w
  rw [hΓ, hK, hK]


theorem exercise12_6_a
    (S B T : Bird) (hS : Starling S) (hB : Bluebird B) (hT : Thrush T) :
    ∃ S' : Bird, ∀ x y z : Bird, S' * x * y * z = y * z * (x * z) := by
  obtain ⟨C, hC⟩ := thm11_21_bonus B T hB hT
  use C * S
  intro x y z
  rw [hC, hS]

theorem exercise12_6_b
    (S' I : Bird)
    (hS' : ∀ x y z : Bird, S' * x * y * z = y * z * (x * z))
    (hI : Identity I) :
    ∃ W : Bird, Warbler W := by
  use S' * I
  intro x y
  rw [hS', hI]


theorem exercise12_7
    (Q : Bird) (hQ : QueerBird Q) :
    ∃ Q_hat : Bird, ∀ C W : Bird, Cardinal C → Warbler W → Starling (C * Q_hat * W) := by
  use Q * (Q * Q * (Q * Q)) * Q
  intro C W hC hW x y z
  rw [hC, hQ, hQ, hW, hQ, hQ, hQ, hQ]






end SmullyanMockingbird
