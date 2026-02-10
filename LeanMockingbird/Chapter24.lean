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


-- Existence of an addition bird
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



#eval var_eliminate "Times" (var_eliminate "n" (var_eliminate "m" (
  "Z" * "m" * "0" * ("Plus" * ("Times" * "n" * ("P" * "m")) * "n")
)))
-- prints:
/-
S * (K * (S * (K * (S * (S * Z * (K * n0))))))
    * (S * (S * (K * S) * (S * (K * (S * (K * S)))
    * (S * (K * (S * (K * (S * (K * PlusBird)))))
    * (S * (S * (K * S) * (S * (K * (S * (K * S)))
    * (S * (K * K)))) * (K * (K * P)))))) * (K * K))
-/

-- Multiplication bird - preparatory lemma
theorem thm24_6_1 (Z n0 P PlusBird : Bird) :
    ∃ TimesBird : Bird, ∀ n m : Nat,
    TimesBird * NumberBird n * NumberBird m =
    Z * (NumberBird m) * (n0) *
    (PlusBird * (TimesBird * (NumberBird n) * (P * (NumberBird m)))
    * NumberBird n) := by
  let K := forest.K; let hK := forest.hK
  let S := forest.S; let hS := forest.hS
  let Θ := forest.Θ; let hΘ := forest.hΘ
  let A₁ :=   S * (K * (S * (K * (S * (S * Z * (K * n0))))))
    * (S * (S * (K * S) * (S * (K * (S * (K * S)))
    * (S * (K * (S * (K * (S * (K * PlusBird)))))
    * (S * (S * (K * S) * (S * (K * (S * (K * S)))
    * (S * (K * K)))) * (K * (K * P)))))) * (K * K))
  use Θ * A₁
  intro n m
  rw [SageBird] at hΘ
  specialize hΘ A₁ (Θ * A₁) rfl
  rw [FondOf] at hΘ
  nth_rw 1 [← hΘ]
  dsimp [A₁]
  nth_rw 1 [hS, hK, hS, hK, hS, hS, hK, hS, hK, hS, hK, hS, hS, hK, hS, hK, hS, hS, hK, hS,
    hK, hS, hK, hS, hS, hK, hS, hS, hK, hS, hK, hS, hS, hK, hK, hK, hK, hK]


-- Existence of a multiplication bird
theorem thm24_6_2 :
    ∃ TimesBird : Bird, ∀ n m : Nat,
    TimesBird * NumberBird n * NumberBird m = NumberBird (n * m) := by
  obtain ⟨P, hP⟩ := @thm24_2 Bird forest
  obtain ⟨Z, hZ⟩ := @thm24_3 Bird forest
  obtain ⟨PlusBird, hPlusBird⟩ := @thm24_5_2 Bird forest
  obtain ⟨TimesBird, hTimesBird⟩ := @thm24_6_1 Bird forest Z (NumberBird 0) P PlusBird
  use TimesBird
  intro n m
  induction m with
  | zero =>
    rw [Nat.mul_zero]
    specialize hTimesBird n 0
    have h1 : Z * NumberBird 0 = t := by
      apply (hZ 0).1
      rfl
    rw [hTimesBird, h1, ht']
  | succ m ih =>
    specialize hTimesBird n (m + 1)
    rw [hTimesBird]
    have h1 : Z * NumberBird (m + 1) = f := by
      apply (hZ (m + 1)).2
      rw [Nat.add_one]
      omega
    rw [h1, hf']
    have h2 : (TimesBird * NumberBird n * (P * NumberBird (m + 1))) = NumberBird (n * m) := by
      rw [← thm24_successor, hP]
      exact ih
    rw [h2]
    rw [hPlusBird (n * m) n]
    have h3 : n * m + n = n * (m + 1) := by
      linarith
    rw [h3]


#eval var_eliminate "Exp" (var_eliminate "n" (var_eliminate "m" (
  "Z" * "m" * "1" * ("Times" * ("Exp" * "n" * ("P" * "m")) * "n")
)))
-- prints:
/-
  S * (K * (S * (K * (S * (S * Z * (K * 1))))))
  * (S * (S * (K * S) * (S * (K * (S * (K * S)))
  * (S * (K * (S * (K * (S * (K * Times)))))
  * (S * (S * (K * S) * (S * (K * (S * (K * S)))
  * (S * (K * K)))) * (K * (K * P)))))) * (K * K))
-/

-- Exponentiating bird - preparatory lemma
theorem thm24_7_1 (Z n1 P TimesBird : Bird) :
    ∃ ExpBird : Bird, ∀ n m : Nat,
    ExpBird * NumberBird n * NumberBird m =
    Z * (NumberBird m) * (n1) *
    (TimesBird * (ExpBird * (NumberBird n) * (P * (NumberBird m)))
    * NumberBird n) := by
  let K := forest.K; let hK := forest.hK
  let S := forest.S; let hS := forest.hS
  let Θ := forest.Θ; let hΘ := forest.hΘ
  let A₁ := S * (K * (S * (K * (S * (S * Z * (K * n1))))))
  * (S * (S * (K * S) * (S * (K * (S * (K * S)))
  * (S * (K * (S * (K * (S * (K * TimesBird)))))
  * (S * (S * (K * S) * (S * (K * (S * (K * S)))
  * (S * (K * K)))) * (K * (K * P)))))) * (K * K))
  use Θ * A₁
  intro n m
  rw [SageBird] at hΘ
  specialize hΘ A₁ (Θ * A₁) rfl
  rw [FondOf] at hΘ
  nth_rw 1 [← hΘ]
  dsimp [A₁]
  nth_rw 1 [hS, hK, hS, hK, hS, hS, hK, hS, hK, hS, hK, hS, hS, hK, hS, hK, hS, hS, hK, hS,
    hK, hS, hK, hS, hS, hK, hS, hS, hK, hS, hK, hS, hS, hK, hK, hK, hK, hK]

-- Existence of an exponentiating bird
theorem thm24_7_2 :
    ∃ ExpBird : Bird, ∀ n m : Nat,
    ExpBird * NumberBird n * NumberBird m = NumberBird (n ^ m) := by
  obtain ⟨P, hP⟩ := @thm24_2 Bird forest
  obtain ⟨Z, hZ⟩ := @thm24_3 Bird forest
  obtain ⟨TimesBird, hTimesBird⟩ := @thm24_6_2 Bird forest
  obtain ⟨ExpBird, hExpBird⟩ := @thm24_7_1 Bird forest Z (NumberBird 1) P TimesBird
  use ExpBird
  intro n m
  induction m with
  | zero =>
    rw [Nat.pow_zero]
    specialize hExpBird n 0
    have h1 : Z * NumberBird 0 = t := by
      apply (hZ 0).1
      rfl
    rw [hExpBird, h1, ht']
  | succ m ih =>
    specialize hExpBird n (m + 1)
    rw [hExpBird]
    have h1 : Z * NumberBird (m + 1) = f := by
      apply (hZ (m + 1)).2
      rw [Nat.add_one]
      omega
    rw [h1, hf']
    have h2 : (ExpBird * NumberBird n * (P * NumberBird (m + 1))) = NumberBird (n ^ m) := by
      rw [← thm24_successor, hP]
      exact ih
    rw [h2]
    rw [hTimesBird (n ^ m) n]
    have h3 : n ^ m * n = n ^ (m + 1) := by
      exact rfl
    rw [h3]


#eval var_eliminate "A" (var_eliminate "n" (
  "Z" * "n" * "t" * ("𝓝" * ("A" * ("P" * "n")))
))
-- prints:
/-
  S * (K * (S * (S * Z * (K * t))))
  * (S * (K * (S * (K * 𝓝)))
  * (S * (S * (K * S) * K) * (K * P)))
-/

-- Even property bird - preparatory lemma
theorem thm24_8_1 (Z P t 𝓝 : Bird) :
    ∃ A : Bird, ∀ n : Nat,
    A * NumberBird n =
    Z * (NumberBird n) * (t) *
    (𝓝 * (A * (P * (NumberBird n)))) := by
  let K := forest.K; let hK := forest.hK
  let S := forest.S; let hS := forest.hS
  let Θ := forest.Θ; let hΘ := forest.hΘ
  let A₁ := S * (K * (S * (S * Z * (K * t))))
  * (S * (K * (S * (K * 𝓝)))
  * (S * (S * (K * S) * K) * (K * P)))
  use Θ * A₁
  intro n
  rw [SageBird] at hΘ
  specialize hΘ A₁ (Θ * A₁) rfl
  rw [FondOf] at hΘ
  nth_rw 1 [← hΘ]
  dsimp [A₁]
  nth_rw 1 [hS, hK, hS, hS, hK, hS, hK, hS, hK, hS, hS, hK, hS, hK,
    hK]

-- Existence of an Even property bird
theorem thm24_8_2 :
    ∃ EvenBird : Bird, ∀ n : Nat,
    EvenBird * NumberBird n = (if n % 2 = 0 then t else f) := by
  obtain ⟨P, hP⟩ := @thm24_2 Bird forest
  obtain ⟨Z, hZ⟩ := @thm24_3 Bird forest
  obtain ⟨𝓝, h𝓝⟩ := @thm23_1 Bird forest
  obtain ⟨EvenBird, hEvenBird⟩ := @thm24_8_1 Bird forest Z P t 𝓝
  use EvenBird
  intro n
  induction n with
  | zero =>
    have h1 : Z * NumberBird 0 = t := by
      apply (hZ 0).1
      rfl
    rw [hEvenBird, h1, ht']
    simp
  | succ n ih =>
    specialize hEvenBird (n + 1)
    rw [hEvenBird]
    have h1 : Z * NumberBird (n + 1) = f := by
      apply (hZ (n + 1)).2
      rw [Nat.add_one]
      omega
    rw [h1, hf']
    have h2 : ((P * NumberBird (n + 1))) = NumberBird n := by
      rw [← thm24_successor, hP]
    rw [h2]
    rw [ih]
    by_cases h : n % 2 = 0
    · simp [h]
      have h' : ¬ ((n + 1) % 2 = 0) := by omega
      simp [h']
      rw [h𝓝.1]
    · simp [h]
      have h' : ((n + 1) % 2 = 0) := by omega
      simp [h']
      rw [h𝓝.2]


#eval var_eliminate "g" (var_eliminate "n" (var_eliminate "m" (
  "Z" * "n" * "f" * ("Z" * "m" * "t" * ("g" * ("P" * "n") * ("P" * "m")))
)))
-- prints:
/-
  S * (K * (S * (S * (K * S) * (S * (K * K) * (S * Z * (K * f))))))
  * (S * (K * (S * (K * (S * (S * Z * (K * t))))))
  * (S * (S * (K * S) * (S * (K * (S * (K * S)))
  * (S * (K * (S * (K * K))) * (S * (S * (K * S) * K) * (K * P))))) * (K * (K * P))))
-/

-- "Is greater than" bird - preparatory lemma
theorem thm24_9_1 (Z P t f : Bird) :
    ∃ g : Bird, ∀ n m : Nat,
    g * NumberBird n * NumberBird m =
    Z * (NumberBird n) * f * (Z * (NumberBird m) * t *
    (g * (P * (NumberBird n)) * (P * (NumberBird m)))) := by
  let K := forest.K; let hK := forest.hK
  let S := forest.S; let hS := forest.hS
  let Θ := forest.Θ; let hΘ := forest.hΘ
  let A₁ := S * (K * (S * (S * (K * S) * (S * (K * K) * (S * Z * (K * f))))))
  * (S * (K * (S * (K * (S * (S * Z * (K * t))))))
  * (S * (S * (K * S) * (S * (K * (S * (K * S)))
  * (S * (K * (S * (K * K))) * (S * (S * (K * S) * K) * (K * P))))) * (K * (K * P))))
  use Θ * A₁
  intro n m
  rw [SageBird] at hΘ
  specialize hΘ A₁ (Θ * A₁) rfl
  rw [FondOf] at hΘ
  nth_rw 1 [← hΘ]
  dsimp [A₁]
  nth_rw 1 [hS, hK, hS, hS, hK, hS, hS, hK, hK, hS, hS, hK, hK, hS, hK,
    hS, hS, hS, hS, hK, hK, hS, hS, hK, hS, hK, hS, hS, hK, hS, hK,
    hK, hS, hS, hK, hS, hK, hK, hK, hK]

-- Existence of "Is greater than" bird
theorem thm24_9_2 :
    ∃ g : Bird, ∀ n m : Nat,
    g * NumberBird n * NumberBird m = (if n > m then t else f) := by
  obtain ⟨P, hP⟩ := @thm24_2 Bird forest
  obtain ⟨Z, hZ⟩ := @thm24_3 Bird forest
  obtain ⟨g, hg⟩ := @thm24_9_1 Bird forest Z P t f
  use g
  intro n m
  induction n generalizing m with
  | zero =>
    specialize hg 0 m
    nth_rw 1 [hg]
    have h1 : Z * NumberBird 0 = t := by
      apply (hZ 0).1
      rfl
    rw [h1, ht']
    simp
  | succ n ih =>
    specialize hg (n + 1) m
    rw [hg]
    have h1 : Z * NumberBird (n + 1) = f := by
      apply (hZ (n + 1)).2
      rw [Nat.add_one]
      omega
    rw [h1, hf']
    cases m with
    | zero =>
      have h0 : Z * NumberBird 0 = t := by
        apply (hZ 0).1
        rfl
      simp [h0]
      rw [ht']
    | succ m =>
      have h0 : Z * NumberBird (m + 1) = f := by
        apply (hZ (m + 1)).2
        omega
      rw [h0, hf']
      have h2 : ((P * NumberBird (n + 1))) = NumberBird n := by
        rw [← thm24_successor, hP]
      have h3 : ((P * NumberBird (m + 1))) = NumberBird m := by
        rw [← thm24_successor, hP]
      rw [h2, h3]
      specialize ih m
      rw [ih]
      simp


def Relational (A : Bird) : Prop :=
  ∀ n m : Nat,
  A * NumberBird n * NumberBird m = t ∨ A * NumberBird n * NumberBird m = f

def Regular (A : Bird) : Prop :=
  ∀ n : Nat, ∃ m : Nat,
  A * NumberBird n * NumberBird m = t

def MinimizerOf_old (A' A : Bird) : Prop :=
  ∀ n : Nat, ∃ k : Nat,
  A' * NumberBird n = NumberBird k ∧
  A * NumberBird n * NumberBird k = t ∧
  ∀ j : Nat,
  (A * NumberBird n * NumberBird j = t) → k ≤ j

open Classical in
def MinimizerOf (A' A : Bird) (hreg : Regular A) : Prop :=
  ∀ n : ℕ,
  A' * NumberBird n = NumberBird (Nat.find (hreg n))

#eval var_eliminate "A₁" (var_eliminate "n" (var_eliminate "m" (
  "A" * "n" * "m" * "m" * ("A₁" * "n" * ("σ" * "m"))
)))
-- prints:
/-
  S * (K * (S * (S * (K * S) * (S * (S * (K * S) * A) * (K * I)))))
  * (S * (S * (K * S) * (S * (K * (S * (K * S))) * (S * (K * K)))) * (K * (K * σ)))
-/

-- A₁ bird - preparatory lemma
theorem thm24_10_1 (A σ : Bird) :
    ∃ A₁ : Bird, ∀ n m : Nat,
    A₁ * NumberBird n * NumberBird m =
    A * (NumberBird n) * (NumberBird m) * (NumberBird m) *
    (A₁ * (NumberBird n) * (σ * (NumberBird m))) := by
  let K := forest.K; let hK := forest.hK
  let S := forest.S; let hS := forest.hS
  let Θ := forest.Θ; let hΘ := forest.hΘ
  let A₁ := S * (K * (S * (S * (K * S) * (S * (S * (K * S) * A) * (K * I)))))
  * (S * (S * (K * S) * (S * (K * (S * (K * S))) * (S * (K * K)))) * (K * (K * σ)))
  use Θ * A₁
  intro n m
  rw [SageBird] at hΘ
  specialize hΘ A₁ (Θ * A₁) rfl
  rw [FondOf] at hΘ
  nth_rw 1 [← hΘ]
  dsimp [A₁]
  nth_rw 1 [hS, hK, hS, hS, hK, hS, hS, hK, hS, hK, hS, hS, hS, hK,
    hS, hS, hK, hS, hK, hS, hS, hK, hK, hK, hK, forest.hI]

-- Existence of A₁ for any A
theorem thm24_10_2 (A : Bird) :
    ∃ A₁ : Bird, ∀ n m : Nat,
    (A * NumberBird n * NumberBird m = f →
      A₁ * NumberBird n * NumberBird m = A₁ * NumberBird n * (V * f * NumberBird m))
      ∧
    (A * NumberBird n * NumberBird m = t →
      A₁ * NumberBird n * NumberBird m = NumberBird m) := by
  let σ : Bird := V * f
  have hσ : Successor σ := thm24_successor
  obtain ⟨A₁, hA₁⟩ := @thm24_10_1 Bird forest A σ
  use A₁
  unfold σ at hσ
  intro n m
  constructor
  · intro hA
    rw [hσ]
    specialize hA₁ n m
    rw [hA₁, hA, hf', hσ]
  · intro hA
    rw [hA₁, hA, ht']



-- Existence of a Minimizer bird A' for any regular relational A
open Classical in
theorem thm24_10_old (A : Bird) (hreg1 : Relational A) (hreg2 : Regular A) :
    ∃ A' : Bird, MinimizerOf_old A' A := by
  let C := forest.C; let hC := forest.hC
  let n0 : Bird := NumberBird 0
  obtain ⟨A₁, hA₁⟩ := thm24_10_2 A
  use C * A₁ * n0
  intro n
  rw [hC]
  specialize hreg2 n
  let k : Nat := Nat.find hreg2
  have k_good := Nat.find_spec hreg2
  use k
  unfold n0
  constructor
  · have h : ∀ k' < k, A₁ * NumberBird n * NumberBird k' =
      A₁ * NumberBird n * (NumberBird (k' + 1)) := by
        intro k' hk'
        have h0 : ¬ (A * NumberBird n * NumberBird k' = t) := by
          apply Nat.find_min hreg2 hk'
        rw [Relational] at hreg1
        specialize hreg1 n k'
        have h1 : A * NumberBird n * NumberBird k' = f := by
          apply hreg1.resolve_left h0
        specialize hA₁ n k'
        rw [thm24_successor] at hA₁
        apply hA₁.1
        exact h1
    have h_ind : ∀ j : Nat, (A * NumberBird n * NumberBird k = t ∧
        ∀ k' < j, A₁ * NumberBird n * NumberBird k' =
        A₁ * NumberBird n * (NumberBird (k' + 1))) →
        A₁ * NumberBird n * NumberBird 0 = A₁ * NumberBird n * NumberBird j := by
      intro k
      induction k with
      | zero =>
        intro _
        rfl
      | succ k ih =>
        intro h2
        have h_prev : ∀ k' < k, A₁ * NumberBird n * NumberBird k' =
            A₁ * NumberBird n * NumberBird (k' + 1) :=
          fun k' hk' => h2.2 k' (Nat.lt_succ_of_lt hk')
        specialize ih ⟨h2.1, h_prev⟩
        have h_step : A₁ * NumberBird n * NumberBird k
            = A₁ * NumberBird n * NumberBird (k + 1) :=   by
          apply h2.2 k
          omega
        rw [← h_step]
        exact ih
    specialize h_ind k ⟨k_good, h⟩
    rw [h_ind]
    apply (hA₁ n k).2
    exact k_good
  · constructor
    · exact k_good
    · intro j hj
      have k_min : k ≤ j := Nat.find_min' hreg2 hj
      exact k_min


-- Existence of a Minimizer bird A' for any regular relational A
open Classical in
theorem thm24_10 (A : Bird) (hreg1 : Relational A) (hreg2 : Regular A) :
    ∃ A' : Bird, MinimizerOf A' A hreg2 := by
  let C := forest.C; let hC := forest.hC
  let n0 : Bird := NumberBird 0
  obtain ⟨A₁, hA₁⟩ := thm24_10_2 A
  use C * A₁ * n0
  intro n
  rw [hC]
  specialize hreg2 n
  let k : Nat := Nat.find hreg2
  have k_good := Nat.find_spec hreg2
  have h : ∀ k' < k, A₁ * NumberBird n * NumberBird k' =
    A₁ * NumberBird n * (NumberBird (k' + 1)) := by
      intro k' hk'
      have h0 : ¬ (A * NumberBird n * NumberBird k' = t) := by
        apply Nat.find_min hreg2 hk'
      rw [Relational] at hreg1
      specialize hreg1 n k'
      have h1 : A * NumberBird n * NumberBird k' = f := by
        apply hreg1.resolve_left h0
      specialize hA₁ n k'
      rw [thm24_successor] at hA₁
      apply hA₁.1
      exact h1
  have h_ind : ∀ j : Nat, (A * NumberBird n * NumberBird k = t ∧
      ∀ k' < j, A₁ * NumberBird n * NumberBird k' =
      A₁ * NumberBird n * (NumberBird (k' + 1))) →
      A₁ * NumberBird n * NumberBird 0 = A₁ * NumberBird n * NumberBird j := by
    intro k
    induction k with
    | zero =>
      intro _
      rfl
    | succ k ih =>
      intro h2
      have h_prev : ∀ k' < k, A₁ * NumberBird n * NumberBird k' =
          A₁ * NumberBird n * NumberBird (k' + 1) :=
        fun k' hk' => h2.2 k' (Nat.lt_succ_of_lt hk')
      specialize ih ⟨h2.1, h_prev⟩
      have h_step : A₁ * NumberBird n * NumberBird k
          = A₁ * NumberBird n * NumberBird (k + 1) :=   by
        apply h2.2 k
        omega
      rw [← h_step]
      exact ih
  specialize h_ind k ⟨k_good, h⟩
  rw [h_ind]
  apply (hA₁ n k).2
  exact k_good


-- Length function and its well-posedness
theorem thm24_11_bound (n : ℕ) : 10^n > n := by
  induction n with
  | zero =>
    -- Base case: 0 < 10^0
    simp
  | succ k ih =>
    -- Inductive step: show k + 1 < 10^(k + 1)
    calc
      k + 1 ≤ 10^k := by
        -- Since 10^k > k, and they are naturals, 10^k >= k+1
        -- Except for cases where 10^k is very small (but 10^k is at least 1)
        exact ih -- (Actually, ih is k < 10^k, which implies k + 1 <= 10^k)
      _ < 10 * 10^k := by
        -- 10^k < 10 * 10^k is true because 10^k >= 1
        omega
      _ = 10^(k + 1) := by
        apply Eq.symm
        rw [Nat.pow_add_one]
        omega

theorem thm24_11_exist (n : ℕ) : ∃ k : ℕ, 10^k > n := by
  use n
  exact thm24_11_bound n

def LengthFunction (n : ℕ) : ℕ :=
  Nat.find (thm24_11_exist n)

def LengthBird (ℓ : Bird) : Prop :=
  ∀ n : ℕ, ℓ * NumberBird n = NumberBird (LengthFunction n)

-- Existence of a "length measurer" bird
open Classical in
theorem thm24_11 :
    ∃ ℓ : Bird, LengthBird ℓ := by
  obtain ⟨g, hg⟩ := @thm24_9_2 Bird forest
  obtain ⟨ExpBird, hExpBird⟩ := @thm24_7_2 Bird forest
  let B := forest.B; let hB := forest.hB
  let C := forest.C; let hC := forest.hC
  let A := C * (B * g * (ExpBird * NumberBird 10))
  have h1 : ∀ n m : ℕ, 10 ^ n > m ↔ A * NumberBird m * NumberBird n = t := by
    intro n m  --hnm
    constructor
    · intro hnm
      unfold A
      rw [hC, hB, hExpBird, hg]
      simp [hnm]
    · intro hA
      rw [hC, hB, hExpBird, hg] at hA
      by_contra hneg
      rw [if_neg hneg] at hA
      unfold f t at hA
      let K := forest.K; let hK := forest.hK
      let I := forest.I; let hI := forest.hI
      rw [ht K hK] at hA
      rw [hf K I hK hI] at hA
      apply thm22_6 K I hK forest.hnontrivial
      exact hA
  have h2 : ∀ n m : ℕ, ¬ 10 ^ n > m → A * NumberBird m  * NumberBird n = f := by
    intro n m hnm
    rw [hC, hB, hExpBird, hg]
    simp [hnm]
  have hreg1 : Relational A := by
    rw [Relational]
    intro n m
    by_cases h_case : 10 ^ m > n
    constructor
    · apply (h1 m n).1 h_case
    · right
      apply h2 m n h_case
  have hreg2 : Regular A := by
    rw [Regular]
    intro n
    obtain ⟨k, hk⟩ := thm24_11_exist n
    use k
    specialize h1 k n
    tauto
  obtain ⟨ℓ, hℓ⟩ := @thm24_10 Bird forest A hreg1 hreg2
  use ℓ
  rw [LengthBird]
  rw [MinimizerOf] at hℓ
  intro n
  specialize hℓ n
  rw [LengthFunction]
  have h_equiv : ∀ k, 10^k > n ↔ A * NumberBird n * NumberBird k = t := by
    intro k
    exact h1 k n
  rw [hℓ]
  congr 1
  obtain ⟨k, hk⟩ := hreg2 n
  apply Nat.find_congr hk
  intro n1 hn1
  specialize h1 n1 n
  apply Iff.symm
  exact h1




end SmullyanMockingbird
