import Mathlib.Tactic
import LeanMockingbird.Chapter21
namespace SmullyanMockingbird

/- Chapter 22: A Glimpse into Infinity -/

variable {Bird : Type} [forest : Forest Bird]

def NonTrivial (_ : Forest Bird) : Prop :=
  ∃ x y : Bird, x ≠ y

/- Some Facts about the Kestrel -/

-- A kestrel cannot be fond of an identity bird
theorem thm22_1
    (K I : Bird) (hK : Kestrel K) (hI : Identity I) (hA : NonTrivial forest) :
    ¬ FondOf K I := by
  by_contra h
  have eq : ∀ x : Bird, x = I := by
    intro x
    rw [← hI x]
    nth_rw 2 [← hK I x]
    rw [FondOf] at h
    rw [h]
  rw [NonTrivial] at hA
  obtain ⟨x, hx⟩ := hA
  obtain ⟨y, hy⟩ := hx
  have eq1 : x = I := by apply eq x
  have eq2 : y = I := by apply eq y
  rw [eq1, eq2] at hy
  tauto

-- I ≠ K
theorem thm22_2
    (K I : Bird) (hK : Kestrel K) (hI : Identity I) (hA : NonTrivial forest) :
    I ≠ K := by
  by_contra eq
  have h : FondOf K I := by
    rw [FondOf]
    nth_rw 2 [← hI I]
    apply Eq.symm
    nth_rw 1 [eq]
  apply thm22_1 K I hK hI hA h

-- No Starling can be fond of a Kestrel
theorem thm22_3
    (K S : Bird) (hK : Kestrel K) (hS : Starling S) (hA : NonTrivial forest) :
    ¬ FondOf S K := by
  by_contra h
  have all_eq : ∀ x y : Bird, x = y := by
    intro x y
    have all_K : ∀ x : Bird, x = K := by
      intro x
      rw [← hK x (K * x)]
      nth_rw 3 [← hK K x]
      rw [← hS]
      rw [h]
    rw [all_K x, all_K y]
  rw [NonTrivial] at hA
  tauto

-- S ≠ I (note: we need a Kestrel in the forest)
theorem thm22_4
    (S I K : Bird) (hS : Starling S) (hI : Identity I) (hK : Kestrel K) (hA : NonTrivial forest) :
    S ≠ I := by
  by_contra h
  apply thm22_3 K S hK hS hA
  rw [FondOf, h, hI]

-- S ≠ K
theorem thm22_5
    (S K : Bird) (hS : Starling S) (hK : Kestrel K) (hA : NonTrivial forest) :
    S ≠ K := by
  by_contra h
  have h2 : S * K * K = K * K * K := by rw [h]
  have hI : Identity (S * K * K) := by
    intro x
    rw [hS, hK]
  have hK : Kestrel (K * K * K) := by
    intro x y
    rw [hK, hK]
  apply thm22_2 (K * K * K) (S * K * K) hK hI hA
  exact h2


-- For no bird x, Kx = K
theorem thm22_6
    (K x : Bird) (hK : Kestrel K) (hA : NonTrivial forest) :
    K * x ≠ K := by
  by_contra h
  have hy : ∀ y : Bird, x = K * y := by
    intro y
    rw [← hK x y, h]
  have h2 : x = K * K := hy K
  have h3 : x = K * x := hy x
  have h4 : x = K := by
    rw [h3, h]
  rw [h4] at h
  have all_K : ∀ z : Bird, z = K := by
    intro z
    apply thm9_19 K z hK h
  rw [NonTrivial] at hA
  obtain ⟨x₁, hx₁⟩ := hA
  obtain ⟨x₂, hx₂⟩ := hx₁
  have hk1 : x₁ = K := all_K x₁
  have hk2 : x₂ = K := all_K x₂
  rw [← hk1] at hk2
  tauto

-- For no bird x, Kx = I
theorem thm22_7
    (K I x : Bird) (hK : Kestrel K) (hI : Identity I) (hA : NonTrivial forest) :
    K * x ≠ I := by
  by_contra h
  have all_x : ∀ y : Bird, y = x := by
    --have h2 : K * x * y
    intro y
    rw [← hI y, ← hK x y, h]
  rw [NonTrivial] at hA
  obtain ⟨x₁, hx₁⟩ := hA
  obtain ⟨x₂, hx₂⟩ := hx₁
  have h1 : x₁ = x := all_x x₁
  have h2 : x₂ = x := all_x x₂
  rw [← h1] at h2
  tauto


/- Some Nonegocentric Birds -/

-- K ≠ T
theorem thm22_8
    (K I T : Bird) (hK : Kestrel K) (hI : Identity I) (hT : Thrush T)
    (hIK : I ≠ K) :
    K ≠ T := by
  by_contra hKT
  have h : K * I * K * K = T * I * K * K := by rw [hKT]
  rw [hK, hI, hT, hK] at h
  tauto

-- No Thrush can be egocentric
theorem thm22_9
    (K I T : Bird) (hK : Kestrel K) (hI : Identity I) (hT : Thrush T)
    (hIK : I ≠ K) :
    T * T ≠ T := by
  by_contra hTT
  have h : T * T * I * K * I = T * I * K * I := by rw [hTT]
  rw [hT, hI, hT, hI, hT, hK] at h
  tauto

-- RII ≠ I
theorem thm22_10
    (K I R : Bird) (hK : Kestrel K) (hI : Identity I) (hR : Robin R)
    (hIK : I ≠ K) :
    R * I * I ≠ I := by
  by_contra hRII
  have h : R * I * I * K * I * K = I * K * I * K := by rw [hRII]
  rw [hR, hI, hK, hI, hK] at h
  tauto

-- RI ≠ I
theorem thm22_10_ex1
    (K I R : Bird) (hK : Kestrel K) (hI : Identity I) (hR : Robin R)
    (hIK : I ≠ K) :
    R * I ≠ I := by
  by_contra hRI
  have h : R * I * I = I * I := by rw [hRI]
  rw [hI] at h
  have h2 : R * I * I ≠ I := thm22_10 K I R hK hI hR hIK
  tauto

-- R ≠ I
theorem thm22_10_ex2
    (K I R : Bird) (hK : Kestrel K) (hI : Identity I) (hR : Robin R)
    (hIK : I ≠ K) :
    R ≠ I := by
  by_contra hRI
  have h : R * I = I * I := by rw [hRI]
  rw [hI] at h
  have h2 : R * I ≠ I := thm22_10_ex1 K I R hK hI hR hIK
  tauto

-- RR ≠ R
theorem thm22_11
    (K I R : Bird) (hK : Kestrel K) (hI : Identity I) (hR : Robin R)
    (hIK : I ≠ K) :
    R * R ≠ R := by
  by_contra hneg
  have h : R * R * I * I * I = R * I * I * I := by rw [hneg]
  rw [hR, hI, hI, hR, hI, hI] at h
  have h2 : R * I ≠ I := thm22_10_ex1 K I R hK hI hR hIK
  tauto

-- CC ≠ C
theorem thm22_12
    (K I C : Bird) (hK : Kestrel K) (hI : Identity I) (hC : Cardinal C)
    (hIK : I ≠ K) :
    C * C ≠ C := by
  by_contra hneg
  obtain ⟨R, hR⟩ := thm11_23 C hC
  have h : C * C * I * R * I * I = C * I * R * I * I := by rw [hneg]
  rw [hC, hC, hC, hI, hI, hR, hI, hI] at h
  have h2 : R * I ≠ I := thm22_10_ex1 K I R hK hI hR hIK
  tauto


/-- VV ≠ V (we assume a Robin is given for simplicity; it's without
loss of generality, since we are in the Master forest) -/
theorem thm22_13
    (K I V R : Bird) (hK : Kestrel K) (hI : Identity I) (hV : Vireo V) (hR : Robin R)
    (hIK : I ≠ K) :
    V * V ≠ V := by
  by_contra hneg
  have h : V * V * R * I * I * I * I = V * R * I * I * I * I := by rw [hneg]
  rw [hV, hI, hV, hI, hR, hI, hI] at h
  have h2 : R * I * I ≠ I := thm22_10 K I R hK hI hR hIK
  tauto

-- WI ≠ I
theorem thm22_14_a
    (K I W : Bird) (hK : Kestrel K) (hI : Identity I) (hW : Warbler W)
    (hIK : I ≠ K) :
    W * I ≠ I := by
  by_contra hneg
  have h : W * I * K = I * K := by rw [hneg]
  rw [hW, hI] at h
  have hA : ∃ x y : Bird, x ≠ y := by
    use I, K
  have h2 : K * K ≠ K := thm22_6 K K hK hA
  tauto

-- WW ≠ W
theorem thm22_14_b
    (K I W : Bird) (hK : Kestrel K) (hI : Identity I) (hW : Warbler W)
    (hIK : I ≠ K) :
    W * W ≠ W := by
  by_contra hneg
  have h : W * W * I = W * I := by rw [hneg]
  rw [hW, hW, hI, hI] at h
  --apply Eq.symm at h
  have h2 : W * I ≠ I := thm22_14_a K I W hK hI hW hIK
  tauto

-- SII ≠ I
theorem thm22_15_a
    (K I S : Bird) (hK : Kestrel K) (hI : Identity I) (hS : Starling S)
    (hIK : I ≠ K) :
    S * I * I ≠ I := by
  by_contra hneg
  have h : S * I * I * K = I * K := by rw [hneg]
  rw [hS, hI] at h
  have hA : ∃ x y : Bird, x ≠ y := by
    use I, K
  have h2 : K * K ≠ K := thm22_6 K K hK hA
  tauto

-- SS ≠ S
-- Note: the proof in the book contains an error (SSIII is not SI(SI)I)
theorem thm22_15_b
    (K I S : Bird) (hK : Kestrel K) (hI : Identity I) (hS : Starling S)
    (hIK : I ≠ K) :
    S * S ≠ S := by
  by_contra hneg
  have h : S * S * I * K * I * K = S * I * K * I * K := by rw [hneg]
  nth_rw 1 [hS, hI, hS, hK, hS, hI, hI, hI, hK] at h
  tauto

-- BKK ≠ KK
theorem thm22_16_a
    (K I B : Bird) (hK : Kestrel K) (hB : Bluebird B)
    (hIK : I ≠ K) :
    B * K * K ≠ K * K := by
  by_contra hneg
  have h : B * K * K * I * K = K * K * I * K := by rw [hneg]
  rw [hB, hK, hK] at h
  have h2 : I = K := thm9_16 K hK I K h
  tauto

-- BB ≠ B
theorem thm22_16_b
    (K I B : Bird) (hK : Kestrel K) (hI : Identity I) (hB : Bluebird B)
    (hIK : I ≠ K) :
    B * B ≠ B := by
  by_contra hneg
  have h : B * B * I * K = B * I * K := by rw [hneg]
  rw [hB, hI] at h
  have h2 : B * K * K = B * I * K * K := by rw [h]
  rw [hB, hI] at h2
  apply thm22_16_a K I B hK hB hIK
  tauto


-- QQ ≠ Q
theorem thm22_17
    (K I Q : Bird) (hK : Kestrel K) (hI : Identity I) (hQ : QueerBird Q)
    (hIK : I ≠ K) :
    Q * Q ≠ Q := by
  by_contra hneg
  have h : Q * Q * I * K * I = Q * I * K * I := by rw [hneg]
  rw [hQ, hI, hQ, hI] at h
  have h2 : Q * K * I * I = K * I * I := by rw [h]
  rw [hQ, hI, hK] at h2
  have hA : ∃ x y : Bird, x ≠ y := by
    use I, K
  have h3 : K * I ≠ I := thm22_1 K I hK hI hA
  tauto


/- Kestrels and Infinity -/

theorem thm22_18
    (K : Bird) (hK : Kestrel K) :
    K * K * K = K := by
    rw [hK]

-- (nth_K K i) is Kᵢ₊₁ in the book's notation
/-
def nth_K (K : Bird) (n : Nat) : Bird :=
  if n = 0 then K
  else K * (nth_K K (n - 1))
-/
def nth_K (K : Bird) : Nat → Bird
  | 0 => K
  | n + 1 => K * (nth_K K n)

/-
def NumberBird : Nat → Bird
  | 0 => I
  | n + 1 => V * f * NumberBird n
-/

-- nth_K K 0 ≠ nth_K K n for all n ≠ 0
theorem thm22_19_1
    (K : Bird) (n : Nat) (hn : n ≠ 0) (hK : Kestrel K)
    (hA : NonTrivial forest) :
    (nth_K K 0) ≠ (nth_K K n) := by
  rw [nth_K]
  dsimp
  unfold nth_K
  split
  · contradiction
  · rename ℕ => n
    apply Ne.symm
    apply thm22_6 K (nth_K K n) hK hA

theorem thm22_19_2
    (K : Bird) (n m : Nat) (hK : Kestrel K) :
    (nth_K K (n + 1)) = (nth_K K (m + 1)) → (nth_K K n) = (nth_K K m) := by
  conv_lhs => unfold nth_K
  intro h
  apply thm9_16 K hK (nth_K K n) (nth_K K m)
  exact h

-- nth_K K n ≠ nth_K K m for all n > m
theorem thm22_19_3
    (K : Bird) (n m : Nat) (hK : Kestrel K)
    (hA : NonTrivial forest) (hnm : n > m) :
    (nth_K K n) ≠ (nth_K K m) := by
  induction n generalizing m with
  | zero =>
    contradiction
  | succ n ih =>
    cases m with
    | zero =>
      have h : n + 1 ≠ 0 := by omega
      apply Ne.symm
      apply thm22_19_1 K (n + 1) h hK hA
    | succ m =>
      have h : n > m := by omega
      specialize ih m h
      by_contra hneg
      have h': nth_K K n = nth_K K m := by
        apply thm22_19_2 K n m hK
        exact hneg
      contradiction



end SmullyanMockingbird
