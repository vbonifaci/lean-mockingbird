import Mathlib.Tactic
import LeanMockingbird.Chapter20
namespace SmullyanMockingbird

/- Chapter 21: The Fixed Point Principle -/

variable {Bird : Type} [forest : Forest Bird]


-- A bird A such that Ay = yA(AyA)
theorem thm21_1
    (S K : Bird) (hS : Starling S) (hK : Kestrel K) :
    ∃ A : Bird, ∀ y : Bird, A * y = y * A * (A * y * A) := by
  obtain ⟨I, hI⟩ := thm18_1 S K hS hK
  obtain ⟨M, hM⟩ := thm18_2 S I hS hI
  obtain ⟨T, hT⟩ := thm18_3 S K I hS hK hI
  obtain ⟨B, hB⟩ := thm18_4 S K hS hK
  obtain ⟨C, hC⟩ := thm11_21_bonus B T hB hT
  obtain ⟨W, hW⟩ := thm12_7 B T M hB hT hM
  obtain ⟨Θ, hΘ⟩ := thm13_4 B M W hB hM hW
  let A₁ : Bird := S * (B * S * T) * (W * C) -- A₁xy = yx(xyx)
  use Θ * A₁ -- A₁ is fond of Θ A₁
  intro y
  rw [SageBird] at hΘ
  specialize hΘ A₁ (Θ * A₁) rfl
  rw [FondOf] at hΘ
  nth_rw 1 [← hΘ]
  dsimp [A₁]
  nth_rw 1 [hS, hB, hS, hT, hW, hC]


-- A bird A such that Ayz = z(yA)(yAz)
theorem thm21_2
    (S K : Bird) (hS : Starling S) (hK : Kestrel K) :
    ∃ A : Bird, ∀ y z : Bird, A * y * z = z * (y * A) * (y * A * z) := by
  obtain ⟨I, hI⟩ := thm18_1 S K hS hK
  obtain ⟨M, hM⟩ := thm18_2 S I hS hI
  obtain ⟨T, hT⟩ := thm18_3 S K I hS hK hI
  obtain ⟨B, hB⟩ := thm18_4 S K hS hK
  obtain ⟨W, hW⟩ := thm12_7 B T M hB hT hM
  obtain ⟨Θ, hΘ⟩ := thm13_4 B M W hB hM hW
  -- A₁xyz = (z(yx))(yxz)
  let A₁ : Bird := S * (S * (K * S) * (S * (K * (S * (K * S))) * (S * (K * (S * (K * T))) * T))) * T
  use Θ * A₁ -- A₁ is fond of Θ A₁
  intro y z
  rw [SageBird] at hΘ
  specialize hΘ A₁ (Θ * A₁) rfl
  rw [FondOf] at hΘ
  nth_rw 1 [← hΘ]
  dsimp [A₁]
  nth_rw 1 [hS, hS, hK, hS, hS, hK, hS, hK, hS, hS, hK, hS, hK, hT, hT, hT]





end SmullyanMockingbird
