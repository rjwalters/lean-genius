/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f9a81b95-bfdb-4434-abe8-3f233c70e750

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem f_pos (k : ℕ) (hk : k ≥ 1) : f k ≥ 1

- theorem f_one : f 1 = 1

- theorem f_two : f 2 = 3
-/

/-
  Erdős Problem #485: Minimum Terms in Squared Polynomials

  Source: https://erdosproblems.com/485
  Status: SOLVED (Schinzel 1987, improved by Schinzel-Zannier 2009)

  Statement:
  Let f(k) be the minimum number of terms in P(x)², where P ∈ ℚ[x] ranges over
  all polynomials with exactly k non-zero terms. Is it true that f(k) → ∞
  as k → ∞?

  Answer: YES

  History:
  - Rényi-Rédei (1947): First investigated the problem
  - Erdős (1949): Proved f(k) < k^(1-c) for some c > 0
  - Erdős-Rényi: Conjectured f(k) → ∞
  - Schinzel (1987): Proved f(k) > (log log k) / log 2
  - Schinzel-Zannier (2009): Improved to f(k) ≫ log k

  Key Insight:
  The question asks whether squaring a polynomial can always reduce the number
  of terms. The answer is no: as the polynomial gets more terms, its square
  must also have more terms (asymptotically).

  Reference: Hayman (1974), Problem 4.4
-/

import Mathlib


namespace Erdos485

open Polynomial Finset BigOperators

/- ## Term Count for Polynomials -/

/--
The number of non-zero terms (monomials) in a polynomial.
This is the cardinality of the support.
-/
noncomputable def termCount {R : Type*} [Semiring R] (p : Polynomial R) : ℕ :=
  p.support.card

/--
A polynomial has exactly k non-zero terms.
-/
def hasTerms {R : Type*} [Semiring R] (p : Polynomial R) (k : ℕ) : Prop :=
  termCount p = k

/- ## The Function f(k) -/

/--
f(k) is the minimum number of terms in P(x)² over all polynomials P
with exactly k non-zero terms.
-/
noncomputable def f (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ p : Polynomial ℚ, hasTerms p k ∧ termCount (p ^ 2) = n}

/- ## Basic Properties -/

/-- A polynomial with k terms squares to at least 1 term (if k ≥ 1). -/
theorem f_pos (k : ℕ) (hk : k ≥ 1) : f k ≥ 1 := by
  refine' le_csInf _ _;
  · refine' ⟨ _, ⟨ ∑ i ∈ Finset.range k, Polynomial.X ^ ( 2 * i ), _, rfl ⟩ ⟩;
    unfold Erdos485.hasTerms termCount;
    rw [ Finset.card_eq_of_bijective ];
    use fun i hi => 2 * i;
    · aesop;
    · aesop;
    · aesop;
  · unfold Erdos485.hasTerms Erdos485.termCount; aesop

/-- f(1) = 1: A monomial squares to a monomial. -/
theorem f_one : f 1 = 1 := by
  refine' le_antisymm _ _;
  · refine' csInf_le _ _ <;> norm_num [ Erdos485.hasTerms ];
    use Polynomial.X; simp +decide [ Erdos485.termCount ] ;
    norm_num [ Polynomial.support_X, Polynomial.support_X_pow ];
  · exact f_pos 1 le_rfl

/-- f(2) = 3: (a + bx^n)² = a² + 2abx^n + b²x^{2n} has 3 terms. -/
theorem f_two : f 2 = 3 := by
  refine' le_antisymm _ _ <;> norm_num [ Erdos485.f ];
  · refine' Nat.sInf_le _;
    -- Consider the polynomial $p(x) = x + 1$.
    use Polynomial.X + 1;
    unfold Erdos485.hasTerms Erdos485.termCount;
    constructor <;> ring_nf;
    · rw [ Finset.card_eq_two ];
      norm_num [ Finset.ext_iff, Polynomial.mem_support_iff ];
      exact ⟨ 0, 1, by norm_num, fun a => by rw [ Polynomial.coeff_one, Polynomial.coeff_X ] ; aesop ⟩;
    · rw [ Finset.card_eq_three ];
      norm_num [ Finset.ext_iff, Polynomial.mem_support_iff ];
      exact ⟨ 0, 1, by norm_num, 2, by norm_num, by norm_num, fun a => by erw [ Polynomial.coeff_one, Polynomial.coeff_X ] ; aesop ⟩;
  · refine' le_csInf _ _ <;> norm_num [ Erdos485.hasTerms, Erdos485.termCount ];
    · refine' ⟨ _, ⟨ Polynomial.X + 1, _, rfl ⟩ ⟩;
      refine' Finset.card_eq_two.mpr ⟨ 0, 1, _, _ ⟩ <;> norm_num [ Polynomial.coeff_one, Polynomial.coeff_X ];
      ext ( _ | _ | n ) <;> simp +decide [ Polynomial.coeff_one, Polynomial.coeff_X ];
    · intro a ha;
      -- Let $a(x) = c_1 x^{d_1} + c_2 x^{d_2}$ with $c_1, c_2 \neq 0$ and $d_1 < d_2$.
      obtain ⟨c1, c2, d1, d2, hc1, hc2, hd⟩ : ∃ c1 c2 : ℚ, ∃ d1 d2 : ℕ, c1 ≠ 0 ∧ c2 ≠ 0 ∧ d1 < d2 ∧ a = Polynomial.C c1 * Polynomial.X ^ d1 + Polynomial.C c2 * Polynomial.X ^ d2 := by
        rw [ Finset.card_eq_two ] at ha;
        rcases ha with ⟨ x, y, hxy, h ⟩ ; rw [ Polynomial.as_sum_support a ] ; simp_all +decide [ Finset.sum_pair ] ;
        cases lt_or_gt_of_ne hxy <;> [ exact ⟨ a.coeff x, by replace h := Finset.ext_iff.mp h x; aesop, a.coeff y, by replace h := Finset.ext_iff.mp h y; aesop, x, y, ‹_›, by simp +decide [ ← Polynomial.C_mul_X_pow_eq_monomial ] ⟩ ; exact ⟨ a.coeff y, by replace h := Finset.ext_iff.mp h y; aesop, a.coeff x, by replace h := Finset.ext_iff.mp h x; aesop, y, x, ‹_›, by simp +decide [ ← Polynomial.C_mul_X_pow_eq_monomial, add_comm ] ⟩ ];
      -- Expanding $a(x)^2$, we get $c_1^2 x^{2d_1} + 2c_1c_2 x^{d_1+d_2} + c_2^2 x^{2d_2}$.
      have h_expand : a^2 = Polynomial.C (c1^2) * Polynomial.X ^ (2 * d1) + Polynomial.C (2 * c1 * c2) * Polynomial.X ^ (d1 + d2) + Polynomial.C (c2^2) * Polynomial.X ^ (2 * d2) := by
        rw [ hd.2 ] ; ring;
        exact Polynomial.funext fun x => by norm_num; ring;
      -- The support of $a(x)^2$ is $\{2d_1, d_1 + d_2, 2d_2\}$.
      have h_support : (a^2).support ⊇ {2 * d1, d1 + d2, 2 * d2} := by
        simp_all +decide [ Finset.insert_subset_iff ];
        norm_num [ sq, mul_assoc, Polynomial.coeff_C, Polynomial.coeff_X_pow ];
        grind;
      exact le_trans ( by rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> norm_num <;> omega ) ( Finset.card_mono h_support )

/- ## Upper Bounds (Erdős 1949) -/

/-- **Erdős (1949)**: There exists c > 0 such that f(k) < k^(1-c) for large k.
This shows that squaring can significantly reduce the term count.
Deep constructive argument — axiomatized. -/
/- ## The Main Result: f(k) → ∞ -/

/-- **Schinzel (1987)**: f(k) > (log log k) / log 2 for sufficiently large k.
Deep algebraic argument — axiomatized. -/
/-- **Schinzel-Zannier (2009)**: f(k) ≫ log k. That is, there exists c > 0
such that f(k) ≥ c * log k for sufficiently large k.
Deep algebraic argument — axiomatized. -/
axiom schinzel_zannier_improved :
    ∃ c : ℝ, c > 0 ∧ ∃ K : ℕ, ∀ k ≥ K,
    (f k : ℝ) ≥ c * Real.log k

/-- **Erdős Problem #485 (SOLVED)**: f(k) → ∞ as k → ∞.
Follows from `schinzel_zannier_improved`: f(k) ≥ c·log(k) → ∞.
The derivation requires `Filter.Tendsto` machinery for ℕ via ℝ — axiomatized. -/
/- ## Examples -/

/-- Example: (1 + x)² = 1 + 2x + x² has 3 terms. -/
/-- Example: (1 + x + x²)² = 1 + 2x + 3x² + 2x³ + x⁴ has 5 terms. -/
/- ## Related Concepts -/

/-- The general version: g(k, n) = minimum terms in P(x)^n for P with k terms.
Schinzel's result extends to this general case. -/
noncomputable def g (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ p : Polynomial ℚ, hasTerms p k ∧ termCount (p ^ n) = m}

/-- For any n ≥ 1, g(k, n) → ∞ as k → ∞.
Extension of Schinzel's result — axiomatized. -/
/- ## Sparse Polynomials -/

/--
A polynomial is sparse if it has few terms relative to its degree.
The study of f(k) is part of sparse polynomial theory.
-/
def isSparse (p : Polynomial ℚ) (c : ℝ) : Prop :=
  (termCount p : ℝ) ≤ c * Real.log (p.natDegree + 1)

/--
Multiplying sparse polynomials can produce denser results.
This is related to the f(k) problem.
-/
/- ## Lacunary Polynomials -/

/--
A lacunary polynomial has large gaps between exponents.
For example, 1 + x^10 + x^100 is lacunary.
-/
def isLacunary (p : Polynomial ℚ) : Prop :=
  ∃ gaps : List ℕ, gaps.length = termCount p - 1 ∧
  ∀ g ∈ gaps, g ≥ 2

/--
Squaring a lacunary polynomial tends to produce more terms due to
fewer cancellations between cross-terms.
-/
/- ## Summary

**Problem Status: SOLVED**

Erdős Problem #485 asks whether f(k) → ∞, where f(k) is the minimum number
of terms in P(x)² for polynomials P with exactly k terms.

**Answer: YES**

The conjecture of Erdős and Rényi was confirmed by:
- Schinzel (1987): Proved f(k) > (log log k) / log 2
- Schinzel-Zannier (2009): Improved to f(k) ≫ log k

**Key Ideas**:
- Squaring cannot indefinitely compress the term count
- There are only finitely many "efficient" polynomials (where squaring
  significantly reduces terms) of each size
- The result extends to P(x)^n for any n ≥ 1

**Open Questions**:
- What is the exact asymptotic growth rate of f(k)?
- Are there explicit constructions achieving the minimum f(k)?

**References**:
- Rényi, Rédei (1947): First investigation
- Erdős (1949): Upper bound f(k) < k^(1-c)
- Schinzel (1987): Lower bound f(k) > (log log k) / log 2
- Schinzel, Zannier (2009): Improved bound f(k) ≫ log k
- Hayman (1974): Problem 4.4
-/

end Erdos485