/-
  Erdős Problem #485 — Open Question 2: Combinatorial Proof via Sumsets

  Source: https://erdosproblems.com/485
  Parent: Erdos485Problem.lean (f(k) → ∞, solved by Schinzel 1987)

  Open Question: Is there a combinatorial (non-algebraic) proof that f(k) → ∞,
  e.g., via sumset bounds?

  Background:
  The known proofs of f(k) → ∞ (Schinzel 1987, Schinzel-Zannier 2009) use
  algebraic methods: height theory on algebraic varieties, properties of
  resultants, and the Mahler measure. These are non-constructive and don't
  yield effective bounds through combinatorial reasoning.

  A combinatorial proof would connect polynomial squaring to SUMSET structure:
  - support(P²) relates to the sumset A + A where A = support(P)
  - The Cauchy-Davenport / sumset bound: |A + A| ≥ 2|A| - 1
  - If no coefficient cancellation occurs, this gives termCount(P²) ≥ 2k - 1

  The obstacle: coefficient CANCELLATION. When cross-terms in the convolution
  sum have opposite signs, they can cancel, reducing support(P²) below |A + A|.
  The core open question is whether cancellation can be controlled well enough
  for a purely combinatorial proof.

  This file formalizes:
  1. The convolution structure of polynomial squaring
  2. The sumset containment: support(P²) ⊆ support(P) + support(P)
  3. The positive-coefficient case: no cancellation, so f_+(k) ≥ 2k - 1
  4. The cancellation barrier and why sumsets alone don't suffice
  5. The sumset lower bound |A + A| ≥ 2|A| - 1

  Axiom count: 0 (all results are structural combinatorial facts)
  Original formalization for Lean Genius.
-/

import Mathlib

set_option maxHeartbeats 800000

namespace Erdos485OQ02

open Polynomial Finset BigOperators

/-
## Part I: Definitions
-/

/-- The number of nonzero terms (monomials) in a polynomial. -/
noncomputable def termCount {R : Type*} [Semiring R] (p : Polynomial R) : ℕ :=
  p.support.card

/-- f(k) = minimum number of terms in P(x)² over all P with exactly k nonzero terms. -/
noncomputable def f (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ p : Polynomial ℚ, termCount p = k ∧ termCount (p ^ 2) = n}

/-
## Part II: Convolution Structure of Polynomial Squaring

The coefficient of P² at position n is:
  coeff(P², n) = Σ_{a+b=n} coeff(P, a) · coeff(P, b)

This is the Cauchy convolution. The key observation for the combinatorial
approach is that this sum involves PRODUCTS of coefficients, which can
cancel when terms have opposite signs.
-/

/-- The coefficient of P² at n equals the convolution sum over the antidiagonal.
    This is the fundamental algebraic identity connecting squaring to additive
    structure of the support. -/
theorem coeff_sq_convolution (P : Polynomial ℚ) (n : ℕ) :
    (P ^ 2).coeff n = ∑ ij ∈ Finset.antidiagonal n,
      P.coeff ij.1 * P.coeff ij.2 := by
  rw [sq, Polynomial.coeff_mul]

/-- If all coefficients of P are nonneg, then all coefficients of P² are nonneg.
    This is the key structural fact: no cancellation can occur. -/
theorem sq_coeff_nonneg (P : Polynomial ℚ) (hP : ∀ n, 0 ≤ P.coeff n) :
    ∀ n, 0 ≤ (P ^ 2).coeff n := by
  intro n
  rw [coeff_sq_convolution]
  exact Finset.sum_nonneg fun ij _ => mul_nonneg (hP ij.1) (hP ij.2)

/-
## Part III: Support and Sumset Connection

The support of P² is contained in the sumset support(P) + support(P).
For positive-coefficient polynomials, equality holds.
-/

/-- Support of P² is contained in the Minkowski sum of support(P) with itself.
    If n ∈ support(P²), then n = a + b for some a, b ∈ support(P).

    This follows because coeff(P², n) = Σ_{a+b=n} c_a · c_b, and if this is
    nonzero, some pair (a, b) with a + b = n must have c_a · c_b ≠ 0,
    meaning a, b ∈ support(P). -/
theorem support_sq_subset_sumset (P : Polynomial ℚ) :
    (P ^ 2).support ⊆ P.support + P.support := by
  intro n hn
  rw [Polynomial.mem_support_iff] at hn
  rw [coeff_sq_convolution] at hn
  -- The sum is nonzero, so some summand must be nonzero
  by_contra hmem
  apply hn
  apply Finset.sum_eq_zero
  intro ij hij
  rw [Finset.mem_antidiagonal] at hij
  -- Either ij.1 or ij.2 is outside support(P), otherwise n ∈ sumset
  by_cases h1 : P.coeff ij.1 = 0
  · simp [h1]
  · by_cases h2 : P.coeff ij.2 = 0
    · simp [h2]
    · exfalso; apply hmem
      rw [Finset.mem_add]
      exact ⟨ij.1, Polynomial.mem_support_iff.mpr h1,
              ij.2, Polynomial.mem_support_iff.mpr h2, hij⟩

/-- Upper bound: the number of terms in P² is at most the sumset size.
    termCount(P²) ≤ |support(P) + support(P)|. -/
theorem termCount_sq_le_sumset (P : Polynomial ℚ) :
    termCount (P ^ 2) ≤ (P.support + P.support).card :=
  Finset.card_le_card (support_sq_subset_sumset P)

/-
## Part IV: Positive Coefficient Case — The Combinatorial Proof Works

For polynomials with all nonneg coefficients, cancellation cannot occur.
Every element of the sumset A + A actually appears in support(P²), so
termCount(P²) = |A + A| ≥ 2|A| - 1.

This gives a COMPLETE combinatorial proof that f_+(k) → ∞, where f_+(k)
restricts to positive-coefficient polynomials.
-/

/-- If P has all nonneg coefficients and a, b ∈ support(P), then
    a + b ∈ support(P²). The convolution sum at a + b includes
    the term c_a · c_b > 0, and all other terms are ≥ 0. -/
theorem sumset_elem_in_sq_support_of_nonneg (P : Polynomial ℚ)
    (hP : ∀ n, 0 ≤ P.coeff n)
    {a b : ℕ} (ha : a ∈ P.support) (hb : b ∈ P.support) :
    a + b ∈ (P ^ 2).support := by
  rw [Polynomial.mem_support_iff, coeff_sq_convolution]
  -- The single term c_a · c_b > 0, and all terms are ≥ 0, so the sum > 0
  have hab_pos : 0 < P.coeff a * P.coeff b :=
    mul_pos (lt_of_le_of_ne (hP a) (Ne.symm (Polynomial.mem_support_iff.mp ha)))
            (lt_of_le_of_ne (hP b) (Ne.symm (Polynomial.mem_support_iff.mp hb)))
  have hle : P.coeff a * P.coeff b ≤
      ∑ ij ∈ Finset.antidiagonal (a + b), P.coeff ij.1 * P.coeff ij.2 :=
    Finset.single_le_sum (fun ij _ => mul_nonneg (hP ij.1) (hP ij.2))
      (Finset.mem_antidiagonal.mpr rfl)
  exact (lt_of_lt_of_le hab_pos hle).ne'

/-- For nonneg-coefficient polynomials, support(P²) equals the sumset exactly.
    Combined with support_sq_subset_sumset, this gives equality. -/
theorem support_sq_eq_sumset_of_nonneg (P : Polynomial ℚ)
    (hP : ∀ n, 0 ≤ P.coeff n) :
    (P ^ 2).support = P.support + P.support := by
  ext n
  constructor
  · exact fun hn => support_sq_subset_sumset P hn
  · intro hn
    rw [Finset.mem_add] at hn
    obtain ⟨a, ha, b, hb, hab⟩ := hn
    rw [← hab]
    exact sumset_elem_in_sq_support_of_nonneg P hP ha hb

/-
## Part V: Sumset Lower Bound

The fundamental combinatorial inequality: for any nonempty finite set
A ⊆ ℕ, we have |A + A| ≥ 2|A| - 1.

Proof sketch: Let A = {a₀ < a₁ < ··· < a_{k-1}}. The elements
  a₀ + a₀ < a₀ + a₁ < ··· < a₀ + a_{k-1} < a₁ + a_{k-1} < ··· < a_{k-1} + a_{k-1}
are all distinct and lie in A + A. There are 2k - 1 of them.

This is a special case of the Cauchy-Davenport theorem for ℤ
(or more precisely, the ordered additive group ℕ).
-/

/-- For any nonempty finite set A ⊆ ℕ, |A + A| ≥ 2|A| - 1.

    This is provable from first principles using the min/max chain argument.
    The key idea: the map i ↦ min(A) + aᵢ injects A into A + A,
    and the map j ↦ aⱼ + max(A) injects A into A + A.
    These two images overlap in exactly one element (min + max = max + min),
    giving at least 2|A| - 1 distinct elements. -/
theorem sumset_card_lower_bound (A : Finset ℕ) (hA : A.Nonempty) :
    (A + A).card ≥ 2 * A.card - 1 := by
  -- Left injection: a ↦ min(A) + a; right injection: a ↦ a + max(A)
  -- These overlap in exactly {min(A) + max(A)}, giving 2|A| - 1 distinct elements.
  have hLsub : A.image (A.min' hA + ·) ⊆ A + A := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact Finset.add_mem_add (Finset.min'_mem A hA) ha
  have hRsub : A.image (· + A.max' hA) ⊆ A + A := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact Finset.add_mem_add ha (Finset.max'_mem A hA)
  have hLcard : (A.image (A.min' hA + ·)).card = A.card :=
    Finset.card_image_of_injective A (fun _ _ h => by omega)
  have hRcard : (A.image (· + A.max' hA)).card = A.card :=
    Finset.card_image_of_injective A (fun _ _ h => by omega)
  have hIcard : (A.image (A.min' hA + ·) ∩ A.image (· + A.max' hA)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    simp only [Finset.mem_inter, Finset.mem_image] at hx hy
    obtain ⟨⟨a₁, ha₁, ha₁eq⟩, b₁, hb₁, hb₁eq⟩ := hx
    obtain ⟨⟨a₂, ha₂, ha₂eq⟩, b₂, hb₂, hb₂eq⟩ := hy
    have := Finset.min'_le A b₁ hb₁
    have := Finset.le_max' A a₁ ha₁
    have := Finset.min'_le A b₂ hb₂
    have := Finset.le_max' A a₂ ha₂
    omega
  have hUcard := Finset.card_union_add_card_inter
    (A.image (A.min' hA + ·)) (A.image (· + A.max' hA))
  have h1 := Finset.card_le_card (Finset.union_subset hLsub hRsub)
  omega

/-
## Part VI: Combining — The Positive-Coefficient Result

For polynomials with nonneg coefficients, the combinatorial proof
of f_+(k) ≥ 2k - 1 is complete:

  termCount(P²) = |support(P) + support(P)|    (Part IV)
                ≥ 2 · |support(P)| - 1          (Part V)
                = 2k - 1
-/

/-- For polynomials with all nonneg coefficients and k ≥ 1 terms,
    the square has at least 2k - 1 terms.

    This is the combinatorial lower bound: no cancellation occurs,
    so the sumset bound applies directly. -/
theorem termCount_sq_nonneg_lower (P : Polynomial ℚ) (k : ℕ)
    (hk : k ≥ 1)
    (htc : termCount P = k)
    (hP : ∀ n, 0 ≤ P.coeff n) :
    termCount (P ^ 2) ≥ 2 * k - 1 := by
  unfold termCount at *
  rw [support_sq_eq_sumset_of_nonneg P hP, ← htc]
  apply sumset_card_lower_bound
  exact Finset.card_pos.mp (by omega)

/-
## Part VII: The Cancellation Barrier

Why the sumset approach does NOT immediately extend to general polynomials:

When P has mixed-sign coefficients, the convolution sum
  coeff(P², n) = Σ_{a+b=n} c_a · c_b
can equal zero even when some c_a · c_b ≠ 0, because positive and negative
terms can cancel.

Example: P = 1 - x² - (1/2)x⁴
  support(P) = {0, 2, 4}, so |A| = 3
  |A + A| = |{0, 2, 4, 6, 8}| = 5 ≥ 2·3 - 1 = 5 ✓

  But P² = 1 - 2x² + (5/4)x⁸ - ... and the x⁴ coefficient cancels:
    coeff(P², 4) = c₀·c₄ + c₂·c₂ + c₄·c₀ = (-1/2) + 1 + (-1/2) = 0

  So support(P²) ⊊ A + A: the cancellation removed one sumset element.

The fundamental challenge: controlling how many sumset elements can be
lost to cancellation. If the number of cancellations is o(|A + A|),
then f(k) → ∞ follows combinatorially.
-/

/-- The maximum number of potential cancellation positions in P² is bounded
    by |A + A|, which is at most |A|² = k². This is the trivial bound.
    A combinatorial proof of f(k) → ∞ requires showing cancellations
    use strictly fewer than |A + A| - 1 positions. -/
theorem cancellation_positions_bound (P : Polynomial ℚ) :
    (P.support + P.support).card ≤ P.support.card ^ 2 := by
  rw [sq]
  exact Finset.card_image₂_le _ _ _

/-- The number of terms in P² is at most the sumset size, which is at most k².
    So termCount(P²) ≤ k² always. This gives the trivial upper bound on f. -/
theorem termCount_sq_upper (P : Polynomial ℚ) (k : ℕ)
    (htc : termCount P = k) :
    termCount (P ^ 2) ≤ k ^ 2 := by
  calc termCount (P ^ 2)
      ≤ (P.support + P.support).card := termCount_sq_le_sumset P
    _ ≤ P.support.card ^ 2 := cancellation_positions_bound P
    _ = k ^ 2 := by rw [htc]

/-
## Summary

**Status: OPEN QUESTION — Partially Resolved**

The combinatorial approach via sumsets succeeds for positive-coefficient
polynomials: f_+(k) ≥ 2k - 1 (proved above, modulo the sumset bound).

For general polynomials, the approach faces the CANCELLATION BARRIER:
coefficient cancellation can reduce support(P²) below the sumset bound.

**What a full combinatorial proof would need:**
1. A bound on the number of "cancellable" positions in A + A
2. Show that cancellable positions are o(|A + A|) as |A| → ∞
3. This would give f(k) → ∞ purely from sumset structure

**Known obstacles:**
- Cancellation depends on algebraic relations between coefficients,
  not just the additive structure of the support
- The Schinzel-Zannier proof uses MULTIPLICATIVE structure (heights)
  that has no obvious combinatorial analogue
- No purely combinatorial proof of f(k) → ∞ is currently known

**Connections to additive combinatorics:**
- The problem is related to Freiman-Ruzsa theory: sets with small
  sumsets have additive structure
- Plünnecke-Ruzsa gives |A + A| ≤ K·|A| ⟹ |nA - mA| ≤ K^{n+m}·|A|
- But the reverse direction (bounding cancellation from sumset size)
  is the harder and less-studied direction

**References:**
- Schinzel, Zannier (2009): algebraic proof via heights
- Tao, Vu (2006): Additive Combinatorics, for sumset bounds
- Freiman (1973): structure theory for sets with small sumsets
-/

end Erdos485OQ02
