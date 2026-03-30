/-
# Erdős Problem #848: Squarefree Products and Extremal Sets

Determine the maximum size of A ⊆ {1,...,N} such that ab + 1 is never
squarefree for all a, b ∈ A (including a = b).

Equivalently: for every a, b ∈ A, there exists a prime p with p² | ab + 1.

The conjectured extremal sets are {n ≡ 7 (mod 25)} and {n ≡ 18 (mod 25)},
each giving |A| ≈ N/25.

Solved by Sawhney for sufficiently large N.

Reference: https://erdosproblems.com/848
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.SumTwoSquares

/- ## Definitions -/

/-- n is squarefree if no prime squared divides n. -/
def IsSquarefree (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬(p * p ∣ n)

/-- A set A ⊆ {1,...,N} has the non-squarefree product property if
    ab + 1 is not squarefree for all a, b ∈ A. -/
def HasNonSqfreeProductProp (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬IsSquarefree (a * b + 1)

/- ## Extremal Function -/

open Classical in
/-- The maximum size of a subset of {1,...,N} with the non-squarefree
    product property. Defined as the supremum over all qualifying subsets. -/
noncomputable def maxNonSqfreeSet (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (fun A => HasNonSqfreeProductProp A)).sup Finset.card

/-- The max size is at most N: any qualifying subset of {1,...,N} has ≤ N elements. -/
theorem maxNonSqfreeSet_le (N : ℕ) : maxNonSqfreeSet N ≤ N := by
  classical
  unfold maxNonSqfreeSet
  apply Finset.sup_le
  intro A hA
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA
  -- |A| ≤ |Icc 1 N| ≤ N via injection x ↦ x - 1 from Icc 1 N to range N
  have hIcc_le : (Finset.Icc 1 N).card ≤ N := by
    have hle : (Finset.Icc 1 N).card ≤ (Finset.range N).card := by
      apply Finset.card_le_card_of_injOn (fun x => x - 1)
      · intro x hx
        simp only [Finset.mem_coe] at hx ⊢
        rw [Finset.mem_Icc] at hx; rw [Finset.mem_range]; omega
      · intro a ha b hb hab
        simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb
        dsimp only at hab; omega
    linarith [Finset.card_range N]
  linarith [Finset.card_le_card hA.1]

/- ## Known Results -/

/-- The set {n ∈ {1,...,N} : n ≡ 7 (mod 25)} achieves the property:
    for a ≡ b ≡ 7 (mod 25), ab + 1 ≡ 50 ≡ 0 (mod 25), so 5² | ab + 1. -/
theorem mod25_achieves :
  ∀ a b : ℕ, a % 25 = 7 → b % 25 = 7 →
    5 * 5 ∣ a * b + 1 := by
  intro a b ha hb
  have ha' : a = 25 * (a / 25) + 7 := by omega
  have hb' : b = 25 * (b / 25) + 7 := by omega
  rw [ha', hb']
  exact ⟨25 * (a / 25) * (b / 25) + 7 * (a / 25) + 7 * (b / 25) + 2, by ring⟩

/-- The symmetric case: {n ≡ 18 (mod 25)} also achieves the property.
    For a ≡ b ≡ 18 (mod 25), ab + 1 ≡ 325 ≡ 0 (mod 25), so 5² | ab + 1. -/
theorem mod25_achieves_18 :
  ∀ a b : ℕ, a % 25 = 18 → b % 25 = 18 →
    5 * 5 ∣ a * b + 1 := by
  intro a b ha hb
  have ha' : a = 25 * (a / 25) + 18 := by omega
  have hb' : b = 25 * (b / 25) + 18 := by omega
  rw [ha', hb']
  exact ⟨25 * (a / 25) * (b / 25) + 18 * (a / 25) + 18 * (b / 25) + 13, by ring⟩

/-- 5 is prime — needed to connect 5² | n to ¬IsSquarefree n. -/
theorem five_prime : Nat.Prime 5 := by decide

/-- If 5² | n, then n is not squarefree (by our definition). -/
theorem not_sqfree_of_five_sq_dvd {n : ℕ} (h : 5 * 5 ∣ n) : ¬IsSquarefree n := by
  intro hsf
  exact hsf 5 five_prime h

/-- The mod 7 residue class satisfies the full non-squarefree product property. -/
theorem mod7_set_has_property (A : Finset ℕ) (hA : ∀ a ∈ A, a % 25 = 7) :
    HasNonSqfreeProductProp A := by
  intro a ha b hb
  exact not_sqfree_of_five_sq_dvd (mod25_achieves a b (hA a ha) (hA b hb))

/-- The mod 18 residue class satisfies the full non-squarefree product property. -/
theorem mod18_set_has_property (A : Finset ℕ) (hA : ∀ a ∈ A, a % 25 = 18) :
    HasNonSqfreeProductProp A := by
  intro a ha b hb
  exact not_sqfree_of_five_sq_dvd (mod25_achieves_18 a b (hA a ha) (hA b hb))

/- ## Lower Bound via Witness Construction -/

/-- The mod 7 residue class in {1,...,N}. -/
private def mod7Set (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => n % 25 = 7)

/-- mod7Set is a subset of Icc 1 N. -/
private lemma mod7Set_sub (N : ℕ) : mod7Set N ⊆ Finset.Icc 1 N :=
  Finset.filter_subset _ _

/-- All elements of mod7Set are ≡ 7 (mod 25). -/
private lemma mod7Set_residue {N n : ℕ} (hn : n ∈ mod7Set N) : n % 25 = 7 := by
  simp only [mod7Set, Finset.mem_filter] at hn
  exact hn.2

/-- mod7Set satisfies HasNonSqfreeProductProp. -/
private lemma mod7Set_prop (N : ℕ) : HasNonSqfreeProductProp (mod7Set N) :=
  mod7_set_has_property (mod7Set N) (fun _ h => mod7Set_residue h)

/-- Key cardinality bound: |{n ∈ {1,...,N} : n ≡ 7 (mod 25)}| ≥ N/25.
    Proof via injection: k ↦ 25k + 7 maps {0,...,N/25-1} into mod7Set. -/
private lemma mod7Set_card_ge (N : ℕ) (hN : 25 ≤ N) : N / 25 ≤ (mod7Set N).card := by
  -- Define the injection k ↦ 25k + 7
  set f : ℕ → ℕ := fun k => 25 * k + 7 with hf_def
  -- Image of {0,...,N/25-1} under f lands in mod7Set N
  have hf_mem : ∀ k, k ∈ Finset.range (N / 25) → f k ∈ mod7Set N := by
    intro k hk
    simp only [Finset.mem_range] at hk
    simp only [mod7Set, Finset.mem_filter, Finset.mem_Icc, hf_def]
    refine ⟨⟨by omega, ?_⟩, by omega⟩
    have := Nat.div_mul_le_self N 25
    omega
  -- f is injective on Finset.range (N / 25)
  have hf_inj : Set.InjOn f (Finset.range (N / 25) : Set ℕ) := by
    intro a _ b _ hab
    simp only [hf_def] at hab
    omega
  -- Conclude via card comparison
  calc N / 25 = (Finset.range (N / 25)).card := (Finset.card_range _).symm
    _ ≤ (mod7Set N).card := Finset.card_le_card_of_injOn f hf_mem hf_inj

/-- Lower bound: maxNonSqfreeSet(N) ≥ ⌊N/25⌋ for N ≥ 25.
    Proved by exhibiting the mod 7 residue class as a witness. -/
theorem lower_bound (N : ℕ) (hN : 25 ≤ N) :
    N / 25 ≤ maxNonSqfreeSet N := by
  classical
  unfold maxNonSqfreeSet
  -- mod7Set N is in the filtered powerset
  have hmem : mod7Set N ∈
      (Finset.Icc 1 N).powerset.filter (fun A => HasNonSqfreeProductProp A) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr (mod7Set_sub N), mod7Set_prop N⟩
  calc N / 25 ≤ (mod7Set N).card := mod7Set_card_ge N hN
    _ ≤ _ := Finset.le_sup hmem

/- ## Van Doorn's Argument: Key Intermediate Steps

Van Doorn's density bound proceeds by showing every a ∈ A must satisfy
a² ≡ -1 (mod p²) for some prime p ≡ 1 (mod 4), then applying a union bound
over such primes. We formalize the key constraint here. -/

/-- Diagonal constraint: the product property implies every element satisfies
    ∃ p prime, p² | a² + 1. This is the starting point for Van Doorn's argument. -/
theorem diagonal_constraint (A : Finset ℕ) (hA : HasNonSqfreeProductProp A)
    (a : ℕ) (ha : a ∈ A) :
    ∃ p : ℕ, p.Prime ∧ p * p ∣ a * a + 1 := by
  have h := hA a ha a ha
  unfold IsSquarefree at h
  push_neg at h
  exact h

/-- 4 never divides a² + 1: since a² mod 4 ∈ {0, 1}, we have a² + 1 mod 4 ∈ {1, 2}. -/
theorem not_four_dvd_sq_succ (a : ℕ) : ¬(2 * 2 ∣ a * a + 1) := by
  intro ⟨k, hk⟩
  rcases Nat.even_or_odd a with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · -- a = m+m: (m+m)² + 1 = 4m² + 1 = 4k is impossible (1 ≢ 0 mod 4)
    have : (m + m) * (m + m) + 1 = 4 * (m * m) + 1 := by ring
    rw [this] at hk; set n := m * m; omega
  · -- a = 2m+1: (2m+1)² + 1 = 4m²+4m+2 = 4k is impossible (2 ≢ 0 mod 4)
    have : (2 * m + 1) * (2 * m + 1) + 1 = 4 * (m * m + m) + 2 := by ring
    rw [this] at hk; set n := m * m + m; omega

/-- If p is prime and p² | a² + 1, then p ≠ 2. -/
theorem prime_sq_dvd_sq_succ_ne_two {p a : ℕ} (hp : p.Prime)
    (hdvd : p * p ∣ a * a + 1) : p ≠ 2 := by
  intro heq; rw [heq] at hdvd; exact not_four_dvd_sq_succ a hdvd

/-- If p is prime and p² | a² + 1, then p ≡ 1 (mod 4).
    This is the key step in Van Doorn's density argument: -1 must be a quadratic
    residue mod p, which by the first supplement forces p ≡ 1 (mod 4). -/
theorem prime_sq_dvd_sq_succ_mod_four {p a : ℕ} (hp : p.Prime)
    (hdvd : p * p ∣ a * a + 1) : p % 4 = 1 := by
  have hp2 : p ≠ 2 := prime_sq_dvd_sq_succ_ne_two hp hdvd
  -- p | a² + 1 since p² | a² + 1
  have hpdvd : p ∣ a * a + 1 := dvd_trans ⟨p, rfl⟩ hdvd
  -- Construct: -1 is a square mod p (since a² ≡ -1 mod p)
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hsq : IsSquare (-1 : ZMod p) := by
    use (a : ZMod p)
    -- Cast a * a + 1 to ZMod p and show it equals 0
    have hpdvd' : p ∣ a ^ 2 + 1 := by rwa [sq]
    have hzero : ((a ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_zmod_eq_zero_iff_dvd]; exact hpdvd'
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] at hzero
    have h : (a : ZMod p) ^ 2 = -1 := by
      have h0 : (a : ZMod p) ^ 2 + 1 = 0 := hzero
      calc (a : ZMod p) ^ 2 = (a : ZMod p) ^ 2 + 1 - 1 := by ring
        _ = 0 - 1 := by rw [h0]
        _ = -1 := by ring
    rw [sq] at h; exact h.symm
  -- Apply first supplement to quadratic reciprocity: IsSquare (-1) ↔ p % 4 ≠ 3
  have hne3 : p % 4 ≠ 3 := ZMod.exists_sq_eq_neg_one_iff.mp hsq
  -- p is odd prime, so p % 4 ∈ {1, 3}; exclude 3
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hmod : p % 4 = 1 ∨ p % 4 = 3 := by
    obtain ⟨m, hm⟩ := hodd
    have : p ≥ 3 := by have := hp.two_le; omega
    omega
  exact hmod.resolve_right hne3

/-- Van Doorn's key constraint: for any set with the non-squarefree product property,
    every element a must satisfy a² ≡ -1 (mod p²) for some prime p ≡ 1 (mod 4).
    The full density bound follows from a union bound: each such p contributes ≤ 2/p²
    density, giving |A|/N ≤ 2·Σ_{p≡1(4)} 1/p² ≈ 0.108. -/
theorem vanDoorn_constraint (A : Finset ℕ) (hA : HasNonSqfreeProductProp A)
    (a : ℕ) (ha : a ∈ A) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 1 ∧ p * p ∣ a * a + 1 := by
  obtain ⟨p, hp, hdvd⟩ := diagonal_constraint A hA a ha
  exact ⟨p, hp, prime_sq_dvd_sq_succ_mod_four hp hdvd, hdvd⟩

/- ## Van Doorn's Density Argument: Counting Solutions

The full Van Doorn bound proceeds:
1. x² = -1 has at most 2 solutions in ZMod p (field theory) — proved below
2. Hensel lifting: each solution mod p lifts uniquely to mod p² (2a ≠ 0 for odd p)
3. Each prime p ≡ 1 (mod 4) contributes ≤ 2/p² density to A
4. Union bound: |A|/N ≤ 2 Σ_{p≡1(4)} 1/p² ≈ 0.108
Steps 2-4 require Hensel's lemma and real analysis, remaining in the axiom. -/

/-- In ZMod p (a field for prime p), x² = -1 has at most 2 solutions:
    if a² = -1 and b² = -1, then b = a or b = -a.
    This is the algebraic core of Van Doorn's density counting. -/
theorem sq_neg_one_unique {p : ℕ} (hp : Nat.Prime p)
    {a b : ZMod p} (ha : a * a = -(1 : ZMod p)) (hb : b * b = -(1 : ZMod p)) :
    b = a ∨ b = -a := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have heq : a * a = b * b := by rw [ha, hb]
  have h : (a - b) * (a + b) = 0 := by
    calc (a - b) * (a + b) = a * a - b * b := by ring
      _ = 0 := sub_eq_zero.mpr heq
  rcases mul_eq_zero.mp h with hsub | hadd
  · left; exact (sub_eq_zero.mp hsub).symm
  · right; exact (neg_eq_of_add_eq_zero_left hadd).symm

/-- Corollary: if p² | a²+1 and p² | b²+1, then a ≡ b or a ≡ -b (mod p).
    The set {n : p² | n²+1} falls into at most 2 residue classes mod p.
    Hensel lifting extends this to 2 classes mod p² (not formalized). -/
theorem sq_dvd_succ_mod_congruence {p a b : ℕ} (hp : Nat.Prime p)
    (ha : p * p ∣ a * a + 1) (hb : p * p ∣ b * b + 1) :
    (a : ZMod p) = (b : ZMod p) ∨ (a : ZMod p) = -(b : ZMod p) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have cast_neg_one : ∀ x : ℕ, p * p ∣ x * x + 1 →
      (x : ZMod p) * (x : ZMod p) = -(1 : ZMod p) := by
    intro x hx
    have hpdvd : p ∣ x * x + 1 := dvd_trans ⟨p, rfl⟩ hx
    have hpdvd' : p ∣ x ^ 2 + 1 := by rwa [sq]
    have hzero : ((x ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_zmod_eq_zero_iff_dvd]; exact hpdvd'
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] at hzero
    have h : (x : ZMod p) ^ 2 = -1 := by
      have h0 : (x : ZMod p) ^ 2 + 1 = 0 := hzero
      calc (x : ZMod p) ^ 2 = (x : ZMod p) ^ 2 + 1 - 1 := by ring
        _ = 0 - 1 := by rw [h0]
        _ = -1 := by ring
    rwa [sq] at h
  exact sq_neg_one_unique hp (cast_neg_one b hb) (cast_neg_one a ha)

/- ## Deep Results (Axiomatized) -/

/-- Van Doorn's upper bound: |A|/N ≤ 2 Σ_{p ≡ 1 (4)} 1/p² ≈ 0.108.
    So maxNonSqfreeSet(N) ≤ ⌊0.108 · N⌋ + O(1). -/
/-- Sawhney's theorem: for sufficiently large N, the maximum is exactly
    ⌊N/25⌋, achieved only by {n ≡ 7 (mod 25)} or {n ≡ 18 (mod 25)}. -/
/-- Structural result: any extremal set for large N is contained in
    {n ≡ 7 (mod 25)} or {n ≡ 18 (mod 25)}. -/
