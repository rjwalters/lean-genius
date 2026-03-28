/-
Erdős Problem #421: Distinct Products in Dense Sequences

**Problem Statement (OPEN)**

Is there a sequence 1 ≤ d₁ < d₂ < ... with density 1 such that all products
∏_{u ≤ i ≤ v} dᵢ are distinct?

**Known Results:**
- Selfridge: exists sequence with density > 1/e - ε for any ε > 0

**Status:** OPEN

**Reference:** [ErGr80, p.84]

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open Set Finset BigOperators Nat Filter

namespace Erdos421

/-
# Part 1: Basic Definitions

Define strictly increasing sequences and density.
-/

-- A sequence d : ℕ → ℕ starting from 1
-- We want d strictly increasing: d(0) < d(1) < d(2) < ...

-- Strictly increasing sequence
def IsStrictlyIncreasing (d : ℕ → ℕ) : Prop := StrictMono d

-- Sequence starts at least 1
def StartsAtOne (d : ℕ → ℕ) : Prop := 1 ≤ d 0

-- Valid sequence: strictly increasing starting at 1
def IsValidSequence (d : ℕ → ℕ) : Prop :=
  IsStrictlyIncreasing d ∧ StartsAtOne d

/-
# Part 2: Density of Sequences

Density 1 means the sequence contains "almost all" integers asymptotically.
-/

-- Counting function: number of terms ≤ n
open Classical in
noncomputable def countingFunc (d : ℕ → ℕ) (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter (fun k => k ∈ Set.range d) |>.card

-- Alternative: for strictly increasing d, count is max {i : d(i) ≤ n}
open Classical in
noncomputable def indexUpTo (d : ℕ → ℕ) (n : ℕ) : ℕ :=
  if h : ∃ i, n < d i then Nat.find h else 0

-- Density definition: limit of countingFunc(n)/n as n → ∞
def HasDensity (S : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (fun n => (S ∩ Finset.range (n + 1)).toFinite.toFinset.card / (n + 1 : ℝ))
    atTop (nhds δ)

-- Density 1 means the sequence has natural density 1
def HasDensityOne (d : ℕ → ℕ) : Prop := HasDensity (Set.range d) 1

/-
# Part 3: Interval Products

Products of the form ∏_{u ≤ i ≤ v} d_i.
-/

-- Product over an interval [u, v]
def intervalProduct (d : ℕ → ℕ) (u v : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc u v, d i

-- All interval products
def AllIntervalProducts (d : ℕ → ℕ) : Set ℕ :=
  {p | ∃ u v : ℕ, u ≤ v ∧ p = intervalProduct d u v}

-- The set of valid pairs (u, v)
def ValidPairs : Set (ℕ × ℕ) := {p | p.1 ≤ p.2}

-- Map from pairs to products
def productMap (d : ℕ → ℕ) : ℕ × ℕ → ℕ :=
  fun p => intervalProduct d p.1 p.2

/-
# Part 4: Distinctness of Products

All interval products must be distinct.
-/

-- Products are distinct: different pairs give different products
def HasDistinctProducts (d : ℕ → ℕ) : Prop :=
  ValidPairs.InjOn (productMap d)

-- Equivalent: for all (u₁,v₁) ≠ (u₂,v₂), products differ
def HasDistinctProductsAlt (d : ℕ → ℕ) : Prop :=
  ∀ u₁ v₁ u₂ v₂, u₁ ≤ v₁ → u₂ ≤ v₂ → (u₁, v₁) ≠ (u₂, v₂) →
    intervalProduct d u₁ v₁ ≠ intervalProduct d u₂ v₂

-- Equivalence of definitions
theorem distinct_equiv (d : ℕ → ℕ) :
    HasDistinctProducts d ↔ HasDistinctProductsAlt d := by
  constructor
  · intro h u₁ v₁ u₂ v₂ huv₁ huv₂ hne heq
    have : (u₁, v₁) = (u₂, v₂) := h huv₁ huv₂ heq
    exact hne this
  · intro h p₁ hp₁ p₂ hp₂ heq
    by_contra hne
    exact h p₁.1 p₁.2 p₂.1 p₂.2 hp₁ hp₂ hne heq

/-
# Part 4b: Structural Properties of Interval Products
-/

-- Single-element product equals the sequence value
@[simp]
theorem intervalProduct_single (d : ℕ → ℕ) (u : ℕ) :
    intervalProduct d u u = d u := by
  simp [intervalProduct, Finset.Icc_self]

-- Product over empty interval (u > v) is 1
theorem intervalProduct_empty (d : ℕ → ℕ) {u v : ℕ} (h : v < u) :
    intervalProduct d u v = 1 := by
  simp [intervalProduct, Finset.Icc_eq_empty (by omega : ¬u ≤ v)]

-- Valid sequences have all terms ≥ 1
theorem valid_seq_pos (d : ℕ → ℕ) (hd : IsValidSequence d) (i : ℕ) :
    1 ≤ d i := by
  obtain ⟨hmono, hstart⟩ := hd
  cases i with
  | zero => exact hstart
  | succ n =>
    calc 1 ≤ d 0 := hstart
    _ ≤ d (n + 1) := le_of_lt (hmono (Nat.zero_lt_succ n))

-- Valid sequences are injective (from StrictMono)
theorem valid_seq_injective (d : ℕ → ℕ) (hd : IsValidSequence d) :
    Function.Injective d :=
  hd.1.injective

-- Interval products of valid sequences are positive
theorem intervalProduct_pos (d : ℕ → ℕ) (hd : IsValidSequence d) (u v : ℕ) :
    0 < intervalProduct d u v := by
  simp only [intervalProduct]
  apply Finset.prod_pos
  intro i _
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (valid_seq_pos d hd i)

-- Strictly increasing implies d(i) ≥ i + 1
theorem valid_seq_ge_succ (d : ℕ → ℕ) (hd : IsValidSequence d) (i : ℕ) :
    i + 1 ≤ d i := by
  induction i with
  | zero => exact hd.2
  | succ n ih =>
    have hlt := hd.1 (show n < n + 1 by omega)
    omega

/-
# Part 4c: Natural Numbers Fail Distinctness

The sequence d(i) = i + 1 has density 1 but fails HasDistinctProducts.
This demonstrates the difficulty: the densest natural sequence already fails.
-/

-- The natural-number sequence: d(i) = i + 1
def natSeq : ℕ → ℕ := fun i => i + 1

theorem natSeq_valid : IsValidSequence natSeq := by
  refine ⟨fun a b hab => ?_, ?_⟩
  · simp [natSeq]; omega
  · simp [natSeq, StartsAtOne]

-- natSeq fails distinctness: product [0,1] = 1*2 = 2 = product [1,1]
-- Two distinct valid pairs map to the same product value.
theorem natSeq_not_distinct : ¬ HasDistinctProducts natSeq := by
  intro h
  -- productMap natSeq (0,1) = ∏ i ∈ Icc 0 1, (i+1) = 1*2 = 2
  -- productMap natSeq (1,1) = ∏ i ∈ Icc 1 1, (i+1) = 2
  -- Both (0,1) and (1,1) are in ValidPairs, so h forces them equal
  have : (0, 1) = (1, 1) := h (show (0 : ℕ) ≤ 1 by omega) (le_refl 1)
    (show productMap natSeq (0, 1) = productMap natSeq (1, 1) by native_decide)
  simp at this

/-
# Part 4d: Powers of 2 Also Fail Distinctness

The sequence d(i) = 2^i has distinct factorizations but NOT distinct interval
products. Example: ∏[0,2] = 2^0 * 2^1 * 2^2 = 8 = 2^3 = ∏[3,3].
The exponent sums 0+1+2 = 3 collide.
-/

-- Powers of 2 sequence
def pow2Seq : ℕ → ℕ := fun i => 2 ^ i

theorem pow2Seq_valid : IsValidSequence pow2Seq := by
  refine ⟨fun a b hab => ?_, ?_⟩
  · exact Nat.pow_lt_pow_right (by omega) hab
  · simp [pow2Seq, StartsAtOne]

-- pow2Seq also fails: product [0,2] = 1*2*4 = 8 = product [3,3] = 8
theorem pow2Seq_not_distinct : ¬ HasDistinctProducts pow2Seq := by
  intro h
  have : (0, 2) = (3, 3) := h (show (0 : ℕ) ≤ 2 by omega) (le_refl 3)
    (show productMap pow2Seq (0, 2) = productMap pow2Seq (3, 3) by native_decide)
  simp at this

/-
# Part 4e: The Gap Between Density 0 and Density 1

Primes have distinct products (by unique factorization) but density 0.
Natural numbers have density 1 but non-distinct products.
The challenge is achieving both simultaneously.
-/

-- For distinct products, intervals of the same length cannot share a product.
-- The number of pairs (u,v) with u ≤ v ≤ n-1 is n*(n+1)/2.
-- All these products must be distinct, yet bounded by d(n-1)^n.
-- This constrains how slowly d can grow.
theorem distinct_products_growth_lower (d : ℕ → ℕ) (hd : IsValidSequence d)
    (_hdist : HasDistinctProducts d) (n : ℕ) (hn : 0 < n) :
    n ≤ d (n - 1) := by
  -- For a valid sequence with distinct products, consider the n single-element
  -- intervals [0,0], [1,1], ..., [n-1,n-1].
  -- Their products are d(0), d(1), ..., d(n-1), all distinct (since d is injective).
  -- Since d is strictly increasing starting from ≥ 1, d(n-1) ≥ n.
  have := valid_seq_ge_succ d hd (n - 1)
  omega

/-
# Part 4f: Advanced Structural Properties

Deeper structural results about sequences with distinct products.
-/

/-- Interval products split at a midpoint: ∏[u,v] = ∏[u,w] * ∏[w+1,v]. -/
theorem intervalProduct_split (d : ℕ → ℕ) {u w v : ℕ} (huw : u ≤ w) (hwv : w < v) :
    intervalProduct d u v = intervalProduct d u w * intervalProduct d (w + 1) v := by
  simp only [intervalProduct]
  have hunion : Finset.Icc u w ∪ Finset.Icc (w + 1) v = Finset.Icc u v := by
    ext i; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc u w) (Finset.Icc (w + 1) v) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    simp only [Finset.mem_Icc] at hi1 hi2; omega
  rw [← hunion, Finset.prod_union hdisj]

/-- The product of the first n terms of a valid sequence is at least n!.
    Follows from d(i) ≥ i+1 for all i. -/
theorem total_product_ge_factorial (d : ℕ → ℕ) (hd : IsValidSequence d) (n : ℕ) :
    n ! ≤ ∏ i ∈ Finset.range n, d i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, Finset.prod_range_succ]
    exact Nat.mul_le_mul (valid_seq_ge_succ d hd n) ih

/-- For distinct products, d(0) ≥ 2. If d(0) = 1, then
    intervalProduct [0,1] = 1 * d(1) = d(1) = intervalProduct [1,1],
    contradicting distinctness. -/
theorem first_term_ge_two (d : ℕ → ℕ) (hd : IsValidSequence d)
    (hdist : HasDistinctProducts d) : 2 ≤ d 0 := by
  by_contra h
  push_neg at h
  have hd0 : d 0 = 1 := by
    have := hd.2; omega
  -- intervalProduct [0,1] = d(0) * d(1) = d(1)
  have h01 : productMap d (0, 1) = d 1 := by
    simp only [productMap, intervalProduct]
    have hIcc : Finset.Icc 0 1 = {0, 1} := by
      ext i; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    rw [hIcc, Finset.prod_pair (by omega : (0 : ℕ) ≠ 1), hd0, one_mul]
  -- intervalProduct [1,1] = d(1)
  have h11 : productMap d (1, 1) = d 1 := by
    simp [productMap]
  -- Same product, different valid pairs → contradiction
  have hpairs : (0, 1) ≠ (1, 1 : ℕ × ℕ) := by simp
  exact hpairs (hdist (show (0 : ℕ) ≤ 1 by omega) le_rfl (h01.trans h11.symm))

/-- For distinct products, d(i) ≥ i + 2 for all i (strengthening valid_seq_ge_succ).
    Proof: d(0) ≥ 2 and d strictly increasing with d(i) ≥ i+1, so d(i) ≥ i+2. -/
theorem distinct_products_stronger_growth (d : ℕ → ℕ) (hd : IsValidSequence d)
    (hdist : HasDistinctProducts d) (i : ℕ) :
    i + 2 ≤ d i := by
  induction i with
  | zero => exact first_term_ge_two d hd hdist
  | succ n ih =>
    have hlt := hd.1 (show n < n + 1 by omega)
    omega

/-- With distinct products, the product of first n terms grows at least as fast as (n+1)!.
    This is strictly stronger than n! because d(i) ≥ i+2. -/
theorem total_product_ge_shifted_factorial (d : ℕ → ℕ) (hd : IsValidSequence d)
    (hdist : HasDistinctProducts d) (n : ℕ) :
    (n + 1) ! ≤ ∏ i ∈ Finset.range n, d i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, Finset.prod_range_succ]
    exact Nat.mul_le_mul (distinct_products_stronger_growth d hd hdist n) ih

/-
# Part 5: The Main Conjecture

Existence of a density-1 sequence with distinct products.
-/

-- The main conjecture
def ErdosConjecture421 : Prop :=
  ∃ d : ℕ → ℕ, IsValidSequence d ∧ HasDensityOne d ∧ HasDistinctProducts d

-- Alternative statement using the formal-conjectures style
theorem erdos_421_statement :
    ErdosConjecture421 ↔
    ∃ d : ℕ → ℕ, StrictMono d ∧ 1 ≤ d 0 ∧ HasDensity (Set.range d) 1 ∧
      ValidPairs.InjOn (productMap d) := by
  simp only [ErdosConjecture421, IsValidSequence, IsStrictlyIncreasing,
    StartsAtOne, HasDensityOne, HasDistinctProducts, and_assoc]

/-
# Part 6: Selfridge's Construction

Selfridge showed a sequence exists with density > 1/e - ε.
-/

-- Selfridge's bound: achievable density
noncomputable def selfridgeDensity : ℝ := 1 / Real.exp 1  -- 1/e ≈ 0.3679

-- Selfridge's result: for any ε > 0, exists sequence with distinct products
-- and density > 1/e - ε
axiom selfridge_construction : ∀ ε > 0, ∃ d : ℕ → ℕ,
  IsValidSequence d ∧ HasDistinctProducts d ∧
  ∃ δ : ℝ, δ > selfridgeDensity - ε ∧ HasDensity (Set.range d) δ

-- Selfridge achieves density 1/e asymptotically
theorem selfridge_achieves_one_over_e :
    ∀ ε > 0, ∃ d : ℕ → ℕ, IsValidSequence d ∧ HasDistinctProducts d ∧
    ∃ δ : ℝ, δ > 1 / Real.exp 1 - ε ∧ HasDensity (Set.range d) δ :=
  selfridge_construction

/-
# Part 7: Upper Bounds and Obstructions

Why can't we easily achieve density 1?
-/

-- If d has distinct products, there are constraints on gaps
-- Heuristically: many products means many distinct values, limiting growth

-- Number of interval products up to length n is ~n²/2
def numProductsUpToLength (n : ℕ) : ℕ := n * (n + 1) / 2

-- For products to be distinct, they must fit in the range of possible values
-- This constrains how dense the sequence can be

/-
# Part 8: Simple Examples

Illustrate the definitions with examples.
-/

-- Natural numbers have density 1 but products are NOT distinct
-- e.g., 1*2*3 = 6 and 2*3 = 6 (but wait, those are different intervals...)
-- Actually: d_i = i+1, product [0,2] = 1*2*3 = 6, product [1,2] = 2*3 = 6
-- But [0,2] ≠ [1,2] as pairs, so they need different products

-- For natural numbers d(i) = i + 1:
-- intervalProduct [0,0] = 1
-- intervalProduct [1,1] = 2
-- intervalProduct [0,1] = 1*2 = 2  -- same as [1,1]!
-- So natural numbers fail distinctness

-- Primes might work better (each product is unique by prime factorization)
-- But primes have density 0, not 1

/-
# Part 9: Related Problem 786

Problem 786 discusses Selfridge's construction in detail.
-/

/-- **Related: Erdős Problem #786.** Selfridge's construction of covering
    systems with large minimum modulus relates to the density of primes
    in arithmetic progressions and sieving arguments. A covering system
    with minimum modulus m₀ is a finite collection of arithmetic
    progressions whose moduli are all ≥ m₀ that cover every integer. -/
def RelatedProblem786 : Prop :=
  ∀ m₀ : ℕ, m₀ > 1 →
    ∃ (k : ℕ) (residues moduli : Fin k → ℕ),
      (∀ i, moduli i ≥ m₀) ∧
      (∀ n : ℤ, ∃ i, n % (moduli i : ℤ) = residues i)

/-
# Part 10: Counting Constraints on Distinct Products

The key counting argument: among the first n terms, there are n(n+1)/2 valid
interval pairs, and all their products must be distinct positive integers.
This constrains how small the maximum product (= ∏ all terms) can be.
-/

/-- The number of valid pairs (u,v) with u ≤ v and both in {0, ..., n-1}
    is exactly n*(n+1)/2. Uses `Finset.range n` for correct n=0 handling. -/
theorem numValidPairs_eq (n : ℕ) :
    ((Finset.range n).product (Finset.range n)).filter
      (fun p => p.1 ≤ p.2) |>.card = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- Decompose: filtered pairs on range(n+1) = filtered pairs on range(n)
    --   ∪ {(u, n) : u ∈ range(n+1)} (n+1 new pairs with second component = n)
    set S := ((Finset.range (n + 1)).product (Finset.range (n + 1))).filter (fun p => p.1 ≤ p.2)
    set S_old := ((Finset.range n).product (Finset.range n)).filter (fun p => p.1 ≤ p.2)
    set S_new := (Finset.range (n + 1)).image (fun u => (u, n))
    have h_eq : S = S_old ∪ S_new := by
      ext ⟨a, b⟩
      simp only [S, S_old, S_new, Finset.mem_union, Finset.mem_filter, Finset.mem_product,
                  Finset.mem_range, Finset.mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨ha, hb⟩, hab⟩
        rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hb) with rfl | hb_lt
        · right; exact ⟨a, by omega, rfl, rfl⟩
        · left; exact ⟨⟨by omega, hb_lt⟩, hab⟩
      · rintro (⟨⟨ha, hb⟩, hab⟩ | ⟨u, hu, rfl, rfl⟩)
        · exact ⟨⟨by omega, by omega⟩, hab⟩
        · exact ⟨⟨hu, by omega⟩, by omega⟩
    have h_disj : Disjoint S_old S_new := by
      rw [Finset.disjoint_left]
      intro ⟨a, b⟩ h_old h_new
      simp only [S_old, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h_old
      simp only [S_new, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at h_new
      obtain ⟨⟨_, hb⟩, _⟩ := h_old
      obtain ⟨_, _, _, rfl⟩ := h_new
      omega
    have h_new_card : S_new.card = n + 1 := by
      rw [Finset.card_image_of_injective _ (fun a b h => by
        simp only [Prod.mk.injEq] at h; exact h.1)]
      exact Finset.card_range (n + 1)
    rw [h_eq, Finset.card_union_of_disjoint h_disj, ih, h_new_card]
    -- n*(n+1)/2 + (n+1) = (n+1)*(n+2)/2
    have heven : ∀ m : ℕ, 2 ∣ m * (m + 1) := by
      intro m
      rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩ <;> rw [hk]
      · exact ⟨k * (k + k + 1), by ring⟩
      · exact ⟨(2 * k + 1) * (k + 1), by ring⟩
    have h1 := Nat.div_mul_cancel (heven n)
    have h2 := Nat.div_mul_cancel (heven (n + 1))
    have h3 : 2 * (n * (n + 1) / 2 + (n + 1)) = 2 * ((n + 1) * (n + 2) / 2) := by
      calc 2 * (n * (n + 1) / 2 + (n + 1))
          = n * (n + 1) / 2 * 2 + 2 * (n + 1) := by omega
        _ = n * (n + 1) + 2 * (n + 1) := by rw [h1]
        _ = (n + 1) * (n + 2) := by ring
        _ = (n + 1) * (n + 2) / 2 * 2 := h2.symm
        _ = 2 * ((n + 1) * (n + 2) / 2) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) h3

/-- Adjacent products d(i)*d(i+1) grow at least quadratically for valid
    sequences with distinct products: d(i)*d(i+1) ≥ (i+2)*(i+3). -/
theorem adjacent_product_bound (d : ℕ → ℕ) (hd : IsValidSequence d)
    (hdist : HasDistinctProducts d) (i : ℕ) :
    (i + 2) * (i + 3) ≤ d i * d (i + 1) := by
  have h1 := distinct_products_stronger_growth d hd hdist i
  have h2 := distinct_products_stronger_growth d hd hdist (i + 1)
  exact Nat.mul_le_mul h1 h2

/-- Consecutive products are strictly larger than single-element products
    at lower indices: d(u)*d(u+1) > d(u) when d(u+1) ≥ 2. -/
theorem consecutive_product_gt_single (d : ℕ → ℕ) (hd : IsValidSequence d)
    (hdist : HasDistinctProducts d) (u : ℕ) :
    d u < d u * d (u + 1) := by
  have h := distinct_products_stronger_growth d hd hdist (u + 1)
  have hpos : 0 < d u := Nat.lt_of_lt_of_le Nat.zero_lt_one (valid_seq_pos d hd u)
  calc d u = d u * 1 := (Nat.mul_one _).symm
    _ < d u * d (u + 1) := Nat.mul_lt_mul_left hpos (by omega)

/-- If d has distinct products, single-element products and 2-element products
    never collide: for any w and any u, d(w) ≠ d(u)*d(u+1).
    This is because d(u)*d(u+1) ≥ (u+2)*(u+3) ≥ 6, while d(w) = w+2 gives
    d(u)*d(u+1) ≥ 2*d(u+1) > d(u+1) ≥ d(w) for w ≤ u+1, and for w > u+1,
    d(w) only catches up when w is large but then the pair (u,u+1) already
    maps differently via InjOn. -/
theorem single_ne_pair_product (d : ℕ → ℕ) (hd : IsValidSequence d)
    (hdist : HasDistinctProducts d) (w u : ℕ) :
    intervalProduct d w w ≠ intervalProduct d u (u + 1) := by
  intro heq
  -- In HasDistinctProducts (InjOn), same product forces same pair
  have hw : w ≤ w := le_refl w
  have hu : u ≤ u + 1 := Nat.le_succ u
  have hpairs := hdist hw hu heq
  -- But (w, w) ≠ (u, u+1) since snd differs
  simp at hpairs

/-- Product with a longer interval strictly dominates the shorter one
    extending from the same start: ∏[u,v] < ∏[u,v+1] for valid sequences.
    Proof: ∏[u,v+1] = ∏[u,v] * d(v+1) ≥ ∏[u,v] * 2 > ∏[u,v]. -/
theorem product_strict_mono_right (d : ℕ → ℕ) (hd : IsValidSequence d)
    (hdist : HasDistinctProducts d) {u v : ℕ} (huv : u ≤ v) :
    intervalProduct d u v < intervalProduct d u (v + 1) := by
  rw [intervalProduct_split d huv (Nat.lt_succ_of_le (le_refl v)),
      intervalProduct_single]
  have hprod_pos := intervalProduct_pos d hd u v
  have hd_ge2 := distinct_products_stronger_growth d hd hdist (v + 1)
  calc intervalProduct d u v
      = intervalProduct d u v * 1 := (Nat.mul_one _).symm
    _ < intervalProduct d u v * d (v + 1) :=
        Nat.mul_lt_mul_left hprod_pos (by omega)

/-- For distinct products, the maximum product among all intervals in [0, n-1]
    (which is ∏[0, n-1]) must be at least n*(n+1)/2, because n*(n+1)/2 distinct
    positive integers require the maximum to be at least that large.

    This gives a concrete lower bound on how fast the total product must grow,
    constraining the achievable density of the sequence. -/
theorem total_product_lower_from_counting (d : ℕ → ℕ) (hd : IsValidSequence d)
    (hdist : HasDistinctProducts d) (n : ℕ) (hn : 2 ≤ n) :
    n * (n + 1) / 2 ≤ intervalProduct d 0 (n - 1) := by
  -- The total product ∏[0,n-1] = ∏ d(i), i ∈ [0,n-1] = ∏ d(i), i ∈ range n
  -- We already know ∏ d(i) ≥ (n+1)! by total_product_ge_shifted_factorial
  -- And (n+1)! ≥ n(n+1)/2 for n ≥ 2
  have hfact := total_product_ge_shifted_factorial d hd hdist n
  -- Convert between Icc-based product and range-based product
  have hprod_eq : intervalProduct d 0 (n - 1) = ∏ i ∈ Finset.range n, d i := by
    simp only [intervalProduct]
    congr 1
    ext i; simp only [Finset.mem_Icc, Finset.mem_range]; omega
  rw [hprod_eq]
  -- (n+1)! ≥ n*(n+1)/2 for n ≥ 2
  calc n * (n + 1) / 2
      ≤ (n + 1)! := by
        induction n with
        | zero => simp
        | succ m ih =>
          rw [Nat.factorial_succ]
          cases m with
          | zero => simp
          | succ k =>
            -- (k+2)*(k+3)/2 ≤ (k+3)*(k+2)!
            -- Since (k+2)! ≥ (k+2)/2 ≥ 1 for k ≥ 0
            have : (k + 2) ! ≥ 1 := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
            nlinarith [Nat.factorial_pos (k + 2)]
    _ ≤ ∏ i ∈ Finset.range n, d i := hfact

/-
# Part 11: Problem Status

The problem remains OPEN.
-/

-- The problem is open
def erdos_421_status : String := "OPEN"

-- Summary of what's known
-- Best construction: Selfridge with density > 1/e - ε
-- Open: Can we achieve density 1?

-- OEIS sequences
-- A389544, A390848 are related

/-
# Summary

**Problem:** Find a strictly increasing sequence d₁ < d₂ < ... starting from 1
with density 1 such that all products ∏_{u ≤ i ≤ v} d_i are distinct.

**Known:**
- Selfridge achieves density > 1/e - ε for any ε > 0
- Gap between 1/e and 1 remains

**Unknown:**
- Can density 1 be achieved?
- What is the supremum of achievable densities?

**Difficulty:** Balancing density (wanting many integers) against distinctness
(needing products to spread out).
-/

end Erdos421
