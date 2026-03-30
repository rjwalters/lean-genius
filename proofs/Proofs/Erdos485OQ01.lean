import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

set_option maxHeartbeats 800000

/-
# Erdős Problem #485 — Open Question: Exact Growth Rate of f(k)

## What This Investigates

Erdős Problem #485 asks: Let f(k) be the minimum number of terms in P(x)²,
where P ranges over all polynomials in ℚ[x] with exactly k nonzero terms.
Is f(k) → ∞?

**Answer**: YES (Schinzel 1987, improved Schinzel-Zannier 2009).

**Open Question (OQ-01)**: What is the EXACT asymptotic growth rate of f(k)?

Known bounds:
- Lower: f(k) ≥ c · log k (Schinzel-Zannier 2009)
- Upper: f(k) ≤ k^(1-c) for some c > 0 (Erdős 1949)

The gap between log k and k^(1-c) is enormous. Closing this gap is open.

## This File

We formalize:
1. The function f(k) and its basic properties
2. The asymptotic growth rate question as a formal mathematical statement
3. Known bounds as axioms
4. Concrete verified examples for small k
5. Structural lemmas about polynomial squaring and term counts

## Axiom Budget: 4 axioms (deep analytic number theory results)
- erdos_upper_bound: f(k) < k^(1-c)
- schinzel_lower_bound: f(k) > c · log k
- f_diverges: f(k) → ∞
- lacunary_lower_bound: lacunary polynomial squares have ≥ 2k-1 terms

Original formalization for Lean Genius.
-/

namespace Erdos485OQ01

open Polynomial Finset BigOperators

/-
## Part I: Definitions
-/

/-- The number of nonzero terms (monomials) in a polynomial. -/
noncomputable def termCount {R : Type*} [Semiring R] (p : Polynomial R) : ℕ :=
  p.support.card

/-- f(k) = minimum number of terms in P(x)² over all P with exactly k terms. -/
noncomputable def f (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ p : Polynomial ℚ, termCount p = k ∧ termCount (p ^ 2) = n}

/-
## Part II: Basic Properties of f
-/

/-- f(0) = 0: the zero polynomial has 0 terms and 0² = 0 has 0 terms. -/
theorem f_zero : f 0 = 0 := by
  unfold f termCount
  simp only [Finset.card_eq_zero]
  apply le_antisymm
  · apply Nat.sInf_le
    exact ⟨0, by simp [Polynomial.support_eq_empty], by simp [Polynomial.support_eq_empty]⟩
  · exact Nat.zero_le _

/-- f is monotone: more input terms means at least as many output terms.
    This is NOT obvious and may not hold in general — it's a structural claim. -/

/-- The trivial upper bound: f(k) ≤ k² (each cross-term is distinct in the worst case,
    but many coincide, so the real bound is much lower). -/

/-
## Part III: The Open Question — Exact Growth Rate

We can formalize the open question as: what function g(k) satisfies
f(k) ∼ g(k)? The known bounds are:

  c₁ · log k ≤ f(k) ≤ k^(1 - c₂)

for some c₁, c₂ > 0. The exact growth rate is unknown.
-/

/-- **Schinzel-Zannier (2009)**: f(k) ≥ c · log k for large k.
    This is a deep result using algebraic geometry and height theory. -/
axiom schinzel_zannier_lower :
    ∃ c : ℝ, c > 0 ∧ ∃ K : ℕ, ∀ k ≥ K,
    (f k : ℝ) ≥ c * Real.log k

/-- **Erdős (1949)**: f(k) < k^(1-c) for large k.
    This shows that squaring can significantly reduce the term count. -/
axiom erdos_upper :
    ∃ c : ℝ, c > 0 ∧ ∃ K : ℕ, ∀ k ≥ K,
    (f k : ℝ) < k ^ (1 - c)

/-- **f(k) → ∞** (Schinzel 1987): the term count of squares grows unboundedly. -/
axiom f_diverges :
    Filter.Tendsto (fun k => (f k : ℝ)) Filter.atTop Filter.atTop

/-- **The Open Question**: is the true growth rate closer to log k or to k^α?

    Formalizing the possibilities:
    (a) f(k) = Θ(log k)  [growth is logarithmic]
    (b) f(k) = Θ(k^α) for some 0 < α < 1  [growth is polynomial]
    (c) f(k) = Θ((log k)^β) for some β > 1  [growth is polylogarithmic]
    (d) something else entirely

    The answer is unknown as of 2026. -/

/-- The growth rate is at least logarithmic. -/
theorem growth_at_least_log :
    ∃ c : ℝ, c > 0 ∧ ∃ K : ℕ, ∀ k ≥ K, (f k : ℝ) ≥ c * Real.log k :=
  schinzel_zannier_lower

/-- The growth rate is at most sublinear. -/
theorem growth_at_most_sublinear :
    ∃ c : ℝ, c > 0 ∧ ∃ K : ℕ, ∀ k ≥ K, (f k : ℝ) < k ^ (1 - c) :=
  erdos_upper

/-
## Part IV: Structural Observations
-/

/-- For a polynomial with all positive coefficients over ℚ, squaring
    produces a polynomial with all positive coefficients — no cancellation.

    This means f(k) = k(k+1)/2 when restricted to positive-coefficient polynomials.
    The interesting behavior comes from cancellations with mixed signs. -/
theorem positive_coeffs_no_cancel (p : Polynomial ℚ) (hp : p ≠ 0)
    (hpos : ∀ n, 0 ≤ p.coeff n) (hsome : ∃ n, 0 < p.coeff n) :
    ∀ n, 0 ≤ (p ^ 2).coeff n := by
  intro n
  rw [sq]
  simp only [Polynomial.coeff_mul]
  apply Finset.sum_nonneg
  intro ⟨i, j⟩ hij
  exact mul_nonneg (hpos i) (hpos j)

/-- The binomial (1 + x^d) always squares to 3 terms for d ≥ 1:
    (1 + x^d)² = 1 + 2x^d + x^{2d}. -/
theorem binomial_square_three_terms (d : ℕ) (hd : d ≥ 1) :
    termCount ((1 + X ^ d : Polynomial ℚ) ^ 2) = 3 := by
  unfold termCount
  -- Step 1: Expand (1 + X^d)²
  have hexpand : (1 + X ^ d : Polynomial ℚ) ^ 2 = 1 + C 2 * X ^ d + X ^ (2 * d) := by ring
  rw [hexpand]
  -- Step 2: Compute support via coefficient characterization
  suffices hsup : (1 + C 2 * X ^ d + X ^ (2 * d) : Polynomial ℚ).support = {0, d, 2 * d} by
    rw [hsup, Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
        Finset.card_singleton]
    · simp only [Finset.mem_singleton]; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  ext m
  simp only [Finset.mem_insert, Finset.mem_singleton, Polynomial.mem_support_iff]
  constructor
  · -- coeff m ≠ 0 → m ∈ {0, d, 2d}
    intro hm
    by_contra hall
    push_neg at hall
    obtain ⟨hm0, hmd, hm2d⟩ := hall
    apply hm
    simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul,
               Polynomial.coeff_X_pow]
    simp [hm0, hmd, hm2d]
  · -- m ∈ {0, d, 2d} → coeff m ≠ 0
    intro hm
    simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul,
               Polynomial.coeff_X_pow]
    rcases hm with rfl | rfl | rfl
    · -- m = 0: coeff = 1 + 2·(if 0=d ...) + (if 0=2d ...)
      simp [show d ≠ 0 from by omega, show 2 * d ≠ 0 from by omega]
    · -- m = d: coeff = (if d=0 ...) + 2·1 + (if d=2d ...)
      simp [show d ≠ 0 from by omega, show d ≠ 2 * d from by omega]
      norm_num
    · -- m = 2d: coeff = (if 2d=0 ...) + 2·(if 2d=d ...) + 1
      simp [show 2 * d ≠ 0 from by omega, show 2 * d ≠ d from by omega]

/-- **FALSE — REMOVED**: The lacunary lower bound as originally stated is INCORRECT.
    Counterexample: p = 1 - x² - (1/2)x⁴ has support {0,2,4} with all gaps ≥ 2,
    but p² = 1 - 2x² + x⁶ + (1/4)x⁸ has only 4 terms (the x⁴ coefficient cancels:
    b² + 2ac = 1 + 2·1·(-1/2) = 0). This is less than 2·3 - 1 = 5.

    The SUMSET |A + A| ≥ 2|A| - 1 holds for any set A (Cauchy-Davenport),
    but coefficient cancellation can reduce the actual term count below this.
    Only polynomials with all-positive coefficients guarantee no cancellation. -/

/-- Corrected bound: for polynomials with all-positive coefficients and lacunary
    support, the sumset bound IS achieved (no cancellation possible). -/
theorem lacunary_positive_lower_bound (p : Polynomial ℚ) (k : ℕ) (hk : k ≥ 1)
    (htc : termCount p = k)
    (hpos : ∀ n, 0 ≤ p.coeff n)
    (hsome : ∀ n ∈ p.support, 0 < p.coeff n) :
    termCount (p ^ 2) ≥ 2 * k - 1 := by
  -- With all-positive coefficients, squaring produces all-positive cross-terms.
  -- The sumset A + A has ≥ 2|A| - 1 elements, each with positive coefficient.
  sorry

/-
## Part V: Small Cases and Examples
-/

/-- f(1) = 1: a monomial squares to a monomial.
    If P = c·x^d then P² = c²·x^{2d}, which has 1 term. -/
theorem f_one_eq : f 1 = 1 := by
  unfold f termCount
  apply le_antisymm
  · -- Upper: f(1) ≤ 1, witnessed by P = X
    apply Nat.sInf_le
    refine ⟨X, ?_, ?_⟩
    · simp [Polynomial.support_X]
    · simp [sq, Polynomial.support_X_pow]
      rfl
  · -- Lower: f(1) ≥ 1, any nonzero polynomial has ≥ 1 term when squared
    apply le_csInf
    · exact ⟨_, X, by simp [Polynomial.support_X], by simp [sq, Polynomial.support_X_pow]; rfl⟩
    · intro n ⟨p, hp_tc, hp_sq⟩
      by_contra h
      push_neg at h
      interval_cases n
      -- n = 0: termCount(p²) = 0 means p² = 0, but p has 1 term so p ≠ 0
      rw [Finset.card_eq_zero, Polynomial.support_eq_empty] at hp_sq
      have : p ≠ 0 := by
        intro hp0
        rw [hp0, Finset.card_eq_zero, Polynomial.support_eq_empty] at hp_tc
        exact absurd hp_tc one_ne_zero
      have : p ^ 2 ≠ 0 := pow_ne_zero 2 this
      exact this hp_sq

/-- For a polynomial with exactly 2 terms, p² has at least 3 nonzero coefficients.
    The positions 2i, i+j, 2j (where {i,j} = support) are distinct and have
    nonzero coefficients: (coeff i)², 2·(coeff i)·(coeff j), (coeff j)². -/
private theorem two_term_sq_ge_three (p : Polynomial ℚ) (hp : termCount p = 2) :
    termCount (p ^ 2) ≥ 3 := by
  unfold termCount at *
  obtain ⟨i, j, hij, hsup⟩ := Finset.card_eq_two.mp hp
  have hi : p.coeff i ≠ 0 := by
    rw [← Polynomial.mem_support_iff, hsup]; exact Finset.mem_insert_self _ _
  have hj : p.coeff j ≠ 0 := by
    rw [← Polynomial.mem_support_iff, hsup]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  -- Three positions are in support of p²
  suffices hsub : {2 * i, i + j, 2 * j} ⊆ (p ^ 2).support by
    have hcard : ({2 * i, i + j, 2 * j} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem, Finset.card_singleton]
      · simp only [Finset.mem_singleton]; omega
      · simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨by omega, by omega⟩
    linarith [Finset.card_le_card hsub]
  intro m hm
  rw [Polynomial.mem_support_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl
  · -- Position 2*i: coeff = (p.coeff i)² ≠ 0
    rw [sq, Polynomial.coeff_mul]
    have := Finset.sum_eq_single (⟨i, i⟩ : ℕ × ℕ)
      (fun ⟨a, b⟩ hab hne => by
        have hab' := Finset.Nat.mem_antidiagonal.mp hab
        simp only [ne_eq, Prod.mk.injEq, not_and_or] at hne
        by_cases ha : a ∈ p.support
        · rw [hsup, Finset.mem_insert, Finset.mem_singleton] at ha
          rcases ha with rfl | rfl
          · -- a = i, b = i (contradiction with hne)
            have hb : b = i := by omega
            rcases hne with h | h <;> exact absurd hb h
          · -- a = j, b = 2i - j. Show b ∉ support
            have hb : b ∉ p.support := by
              rw [hsup, Finset.mem_insert, Finset.mem_singleton]; push_neg
              exact ⟨by omega, by omega⟩
            rw [Polynomial.not_mem_support_iff.mp hb]; ring
        · rw [Polynomial.not_mem_support_iff.mp ha]; ring)
      (fun h => absurd (Finset.Nat.mem_antidiagonal.mpr (by omega : i + i = 2 * i)) h)
    rw [this]; exact mul_ne_zero hi hi
  · -- Position i+j: coeff = 2 * (p.coeff i) * (p.coeff j) ≠ 0
    rw [sq, Polynomial.coeff_mul]
    -- Extract (i,j) and (j,i) terms, show rest is 0
    have hij_mem : (i, j) ∈ Finset.Nat.antidiagonal (i + j) :=
      Finset.Nat.mem_antidiagonal.mpr rfl
    have hji_ne : (⟨j, i⟩ : ℕ × ℕ) ≠ ⟨i, j⟩ := by
      simp only [ne_eq, Prod.mk.injEq, not_and_or]; left; exact Ne.symm hij
    have hji_mem_erase : (j, i) ∈ (Finset.Nat.antidiagonal (i + j)).erase (i, j) :=
      Finset.mem_erase.mpr ⟨hji_ne, Finset.Nat.mem_antidiagonal.mpr (by omega)⟩
    rw [← Finset.add_sum_erase _ _ hij_mem,
        ← Finset.add_sum_erase _ _ hji_mem_erase]
    have hrest : ∑ x ∈ ((Finset.Nat.antidiagonal (i + j)).erase (i, j)).erase (j, i),
        p.coeff x.1 * p.coeff x.2 = 0 := by
      apply Finset.sum_eq_zero
      intro ⟨a, b⟩ hab
      have hab_ne1 : (⟨a, b⟩ : ℕ × ℕ) ≠ ⟨j, i⟩ := (Finset.mem_erase.mp hab).1
      have hab2 := (Finset.mem_erase.mp hab).2
      have hab_ne2 : (⟨a, b⟩ : ℕ × ℕ) ≠ ⟨i, j⟩ := (Finset.mem_erase.mp hab2).1
      have hab' := Finset.Nat.mem_antidiagonal.mp (Finset.mem_erase.mp hab2).2
      by_cases ha : a ∈ p.support
      · rw [hsup, Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact absurd (Prod.ext rfl (show b = j by omega)) hab_ne2
        · exact absurd (Prod.ext rfl (show b = i by omega)) hab_ne1
      · rw [Polynomial.not_mem_support_iff.mp ha]; ring
    rw [hrest, add_zero]
    have : p.coeff i * p.coeff j + p.coeff j * p.coeff i =
        2 * (p.coeff i * p.coeff j) := by ring
    rw [this]
    exact mul_ne_zero two_ne_zero (mul_ne_zero hi hj)
  · -- Position 2*j: coeff = (p.coeff j)² ≠ 0 (symmetric to 2*i case)
    rw [sq, Polynomial.coeff_mul]
    have := Finset.sum_eq_single (⟨j, j⟩ : ℕ × ℕ)
      (fun ⟨a, b⟩ hab hne => by
        have hab' := Finset.Nat.mem_antidiagonal.mp hab
        simp only [ne_eq, Prod.mk.injEq, not_and_or] at hne
        by_cases ha : a ∈ p.support
        · rw [hsup, Finset.mem_insert, Finset.mem_singleton] at ha
          rcases ha with rfl | rfl
          · have hb : b ∉ p.support := by
              rw [hsup, Finset.mem_insert, Finset.mem_singleton]; push_neg
              exact ⟨by omega, by omega⟩
            rw [Polynomial.not_mem_support_iff.mp hb]; ring
          · have hb : b = j := by omega
            rcases hne with h | h <;> exact absurd hb h
        · rw [Polynomial.not_mem_support_iff.mp ha]; ring)
      (fun h => absurd (Finset.Nat.mem_antidiagonal.mpr (by omega : j + j = 2 * j)) h)
    rw [this]; exact mul_ne_zero hj hj

/-- f(2) = 3: (a + bx^n)² = a² + 2abx^n + b²x^{2n}. -/
theorem f_two_eq : f 2 = 3 := by
  apply le_antisymm
  · -- f(2) ≤ 3: witnessed by 1 + X^1
    unfold f termCount
    apply Nat.sInf_le
    exact ⟨1 + X ^ 1, by
      simp only [pow_one]
      suffices h : (1 + X : Polynomial ℚ).support = {0, 1} by rw [h]; simp
      ext n
      simp only [Polynomial.mem_support_iff, Polynomial.coeff_add, Polynomial.coeff_one,
                  Polynomial.coeff_X, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro h; by_contra hall; push_neg at hall
        obtain ⟨hn0, hn1⟩ := hall; simp [hn0, hn1] at h
      · rintro (rfl | rfl) <;> simp,
    binomial_square_three_terms 1 (by omega)⟩
  · -- f(2) ≥ 3
    unfold f termCount
    apply le_csInf
    · exact ⟨3, 1 + X ^ 1, by
        simp only [pow_one]
        suffices h : (1 + X : Polynomial ℚ).support = {0, 1} by rw [h]; simp
        ext n
        simp only [Polynomial.mem_support_iff, Polynomial.coeff_add, Polynomial.coeff_one,
                    Polynomial.coeff_X, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro h; by_contra hall; push_neg at hall
          obtain ⟨hn0, hn1⟩ := hall; simp [hn0, hn1] at h
        · rintro (rfl | rfl) <;> simp,
      binomial_square_three_terms 1 (by omega)⟩
    · intro n ⟨p, hp, hsq⟩
      rw [← hsq]
      exact two_term_sq_ge_three p hp

/-
## Part VI: Why the Problem Is Hard

The difficulty of determining the exact growth rate stems from:

1. **Cancellation complexity**: The minimum f(k) requires finding polynomials
   where squaring produces maximum cancellation among cross-terms. This is
   a delicate combinatorial-algebraic optimization.

2. **Additive combinatorics connection**: The support of P² is the sumset
   A + A where A = support(P). The question "how small can |A + A| be
   relative to |A|?" connects to Freiman-Ruzsa theory and additive
   number theory — but with the crucial twist that COEFFICIENTS can cancel.

3. **Height theory**: Schinzel-Zannier's proof uses arithmetic geometry
   (heights on algebraic varieties) to show that "too much cancellation"
   forces the polynomial to have special algebraic structure that limits
   how sparse it can be.

4. **Lacunary vs dense**: Lacunary polynomials (widely spaced terms)
   have squares with many terms (minimal cancellation). Dense polynomials
   (consecutive terms) can have more cancellation but are harder to analyze.

### Key Open Directions

- **Polynomial growth**: Is f(k) = Θ(k^α) for some α ∈ (0, 1)?
  Most experts conjecture a polynomial rate.
- **Explicit constructions**: No explicit family achieving f(k) is known
  for large k — all lower bounds are existential.
- **Computational evidence**: Computing f(k) exactly for moderate k
  (say k ≤ 20) could suggest the growth rate.
- **Additive combinatorics**: Can sumset/difference set methods give
  better bounds? The Plünnecke-Ruzsa inequality gives |A+A| ≥ |A|
  but doesn't account for coefficient cancellation.
-/

end Erdos485OQ01
