import Mathlib.Tactic
import LeanMockingbird.Chapter23
namespace SmullyanMockingbird

/- Chapter 24: Birds That Can Do Arithmetic -/

variable {Bird : Type} [forest : LogicalForest Bird]

abbrev I := forest.I
abbrev V := forest.V

def NumberBird [forest : LogicalForest Bird] : Nat → Bird
  | 0 => I
  | n + 1 => V * f * NumberBird n

def Successor (σ : Bird) : Prop :=
  ∀ n : Nat, σ * @NumberBird Bird forest n = NumberBird (n + 1)

-- By construction, V * f * NumberBird n = NumberBird (n + 1)
theorem thm24_successor :
    @Successor Bird forest (V * f) := by
  rw [Successor]
  intro n
  rfl

-- NumberBird (n + 1) is not equal to NumberBird 0 for any n
theorem thm24_1_1
    (n : Nat) (hA : NonTrivial forest.toForest) :
    @NumberBird Bird forest (n + 1) ≠ NumberBird 0 := by
  unfold NumberBird
  by_contra hneg
  let K := forest.K; let hK := forest.hK
  have h : V * forest.f * (NumberBird n) * K = K := by
    rw [hneg, forest.hI]
  rw [hf K I hK forest.hI] at h
  rw [forest.hV, hK] at h
  apply thm22_6 K I hK hA
  exact h

-- NumberBird (n + 1) = NumberBird (m + 1) implies NumberBird n = NumberBird m
theorem thm24_1_2
    (n m : Nat) :
    @NumberBird Bird forest (n + 1) = NumberBird (m + 1) →
    @NumberBird Bird forest n = NumberBird m := by
  intro h
  unfold NumberBird at h
  have h' : ∀ x : Bird, V * f * NumberBird n * x = V * f * NumberBird m * x := by
    intro x
    rw [h]
  specialize h' f
  let K := forest.K; let hK := forest.hK
  rw [forest.hV, forest.hV] at h'
  rw [hf' f, hf' f] at h'
  exact h'

-- NumberBird n ≠ NumberBird m for all n > m
theorem thm24_1_3
    (n m : Nat) (hnm : n > m) (hA : NonTrivial forest.toForest) :
    @NumberBird Bird forest n ≠ NumberBird m := by
  by_contra hneg
  induction n generalizing m with
  | zero =>
    contradiction
  | succ n ih =>
    cases m with
    | zero =>
      apply thm24_1_1 n hA
      exact hneg
    | succ m =>
      have h' : @NumberBird Bird forest n = NumberBird m := by
        apply thm24_1_2
        exact hneg
      specialize ih m
      have hnm' : n > m := by omega
      specialize ih hnm' h'
      exact ih

-- The Predecessor Bird P
def Predecessor (P : Bird) : Prop :=
  ∀ n : Nat, P * (forest.V * f * NumberBird n) = NumberBird n

-- Existence of a Predecessor bird
theorem thm24_2 :
    ∃ P : Bird, Predecessor P := by
  let T := forest.T; let hT := forest.hT
  let K := forest.K; let hK := forest.hK
  use T * f
  rw [Predecessor]
  intro n
  rw [hT, forest.hV, hf']


-- Zero-tester bird
def ZeroTester (Z : Bird) : Prop :=
  ∀ n : Nat, (n = 0 → Z * NumberBird n = t)
            ∧ (n ≠ 0 → Z * NumberBird n = f)


-- Existence of a Zero-tester bird
theorem thm24_3 :
    ∃ Z : Bird, ZeroTester Z := by
  let T := forest.T; let hT := forest.hT
  let K := forest.K; let hK := forest.hK
  use T * t
  rw [ZeroTester]
  intro n
  cases n with
  | zero =>
    constructor
    · intro h0
      rw [hT]
      unfold NumberBird
      rw [forest.hI]
    · intro h0
      contradiction
  | succ n =>
    constructor
    · intro h0
      contradiction
    · intro h0
      rw [hT]
      unfold NumberBird
      rw [forest.hV]
      rw [ht']


theorem thm24_4 :
    ∃ A : Bird, ∀ n : Nat, ∀ x y : Bird,
    (n = 0 → A * NumberBird n * x * y = x) ∧
    (n ≠ 0 → A * NumberBird n * x * y = y) := by
  obtain ⟨Z, hZ⟩ := @thm24_3 Bird forest
  let K := forest.K; let hK := forest.hK
  use Z
  intro n x y
  specialize hZ n
  constructor
  · intro hn
    have hZ1 := hZ.1
    specialize hZ1 hn
    rw [hZ1]
    rw [ht']
  · intro hn
    have hZ2 := hZ.2
    specialize hZ2 hn
    rw [hZ2]
    rw [hf']



example (S K σ P Z : Bird) (hS : Starling S) (hK : Kestrel K) :
    ∀ x y z : Bird,
    S * (S * Z * (K * y)) * (S * (K * σ) * (S * (K * (x * y)) * P)) * z =
    Z * z * y * (σ * (x * y * (P * z))) := by
  intro x y z
  rw [hS, hS, hK, hS, hK, hS, hK]


example (S K σ P Z : Bird) (hS : Starling S) (hK : Kestrel K) :
    ∀ x y z : Bird,
    S
    * (S * (K * S) * (S * (K * (S * Z)) * K))
    * (S * (K * (S * (K * σ))) * (S * (S * (K * S) * (S * (K * K) * x)) * (K * P))) * y * z =
    Z * z * y * (σ * (x * y * (P * z))) := by
  intro x y z
  rw [hS, hS, hK, hS, hS, hK, hS, hK, hS, hK, hS, hK, hS, hS, hK, hS, hK, hS, hK, hK]


example (S K σ P Z : Bird) (hS : Starling S) (hK : Kestrel K) :
    ∀ x y z : Bird,
    S * (K * (S * (S * (K * S) * (S * (K * (S * Z)) * K))))
    * (S * (K * (S * (K * (S * (K * σ)))))
    * (S * (S * (K * S) * (S * (K * (S * (K * S))) * (S * (K * K)))) * (K * (K * P))))
    * x * y * z =
    Z * z * y * (σ * (x * y * (P * z))) := by
  intro x y z
  rw [hS, hK, hS, hS, hK, hS, hS, hK, hS, hK, hS, hK, hS, hK, hS,
  hK, hS, hS, hK, hS, hS, hK, hS, hK, hS, hS, hK, hK, hK, hK]


-- Addition bird - preparatory lemma
theorem thm24_5_1 (Z σ P : Bird) :
    ∃ PlusBird : Bird, ∀ n m : Nat,
    --PlusBird * NumberBird n * NumberBird m = NumberBird (n + m) := by
    PlusBird * NumberBird n * NumberBird m =
    Z * (NumberBird m) * (NumberBird n) *
    (σ * (PlusBird * (NumberBird n) * (P * NumberBird m))) := by
  let K := forest.K; let hK := forest.hK
  let S := forest.S; let hS := forest.hS
  let Θ := forest.Θ; let hΘ := forest.hΘ
  let A₁ := S * (K * (S * (S * (K * S) * (S * (K * (S * Z)) * K))))
    * (S * (K * (S * (K * (S * (K * (σ))))))
    * (S * (S * (K * S) * (S * (K * (S * (K * S))) * (S * (K * K)))) * (K * (K * P))))
  use Θ * A₁ -- A₁ is fond of Θ A₁
  intro n m
  rw [SageBird] at hΘ
  specialize hΘ A₁ (Θ * A₁) rfl
  rw [FondOf] at hΘ
  nth_rw 1 [← hΘ]
  dsimp [A₁]
  nth_rw 1 [hS, hK, hS, hS, hK, hS, hS, hK, hS, hK, hS, hK, hS, hK, hS, hK,
  hS, hS, hK, hS, hS, hK, hS, hK, hS, hS, hK, hK, hK, hK]


-- Addition bird
theorem thm24_5_2 :
    ∃ PlusBird : Bird, ∀ n m : Nat,
    PlusBird * NumberBird n * NumberBird m = NumberBird (n + m) := by
  let σ := forest.V * forest.f
  obtain ⟨P, hP⟩ := @thm24_2 Bird forest
  obtain ⟨Z, hZ⟩ := @thm24_3 Bird forest
  obtain ⟨PlusBird, hPlusBird⟩ := thm24_5_1 Z σ P
  use PlusBird
  intro n m
  induction m with
  | zero =>
    specialize hPlusBird n 0
    have h1 : Z * NumberBird 0 = t := by
      apply (hZ 0).1
      rfl
    rw [hPlusBird, h1, ht']
    rw [Nat.add_zero]
  | succ m ih =>
    specialize hPlusBird n (m + 1)
    rw [hPlusBird]
    have h1 : Z * NumberBird (m + 1) = f := by
      apply (hZ (m + 1)).2
      rw [Nat.add_one]
      omega
    rw [h1, hf']
    unfold σ
    have h2 : (PlusBird * NumberBird n * (P * NumberBird (m + 1))) = NumberBird (n + m) := by
      rw [← thm24_successor, hP]
      exact ih
    rw [h2]
    rw [thm24_successor]
    rw [Nat.add_assoc]




















end SmullyanMockingbird
