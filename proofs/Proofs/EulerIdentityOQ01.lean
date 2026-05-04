/-
# Euler's Formula via Taylor Series Splitting

## Research Question (OQ-01)

Can the full Taylor series proof — showing ∑ (ix)^n/n! splits into cosine
and sine series — be formalized as a standalone theorem without relying on
`Complex.exp_mul_I` directly?

## Answer

Yes. The proof follows three steps:
1. exp(ix) = ∑ (ix)^n/n! (from Mathlib's power series definition)
2. Split into even and odd indices:
   Even: (ix)^{2k}/(2k)! = (-1)^k x^{2k}/(2k)! = cos(x) term
   Odd: (ix)^{2k+1}/(2k+1)! = i·(-1)^k x^{2k+1}/(2k+1)! = i·sin(x) term
3. Therefore exp(ix) = cos(x) + i·sin(x)

## Axiom Budget

2 axioms:
1. The even/odd tsum splitting: ∑_n a_n = ∑_k a_{2k} + ∑_k a_{2k+1}
2. Identification of the real-valued even/odd subseries with cos and sin

Source: Extension of the Euler Identity formalization (OQ-01)
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

open Complex Real
open scoped Nat

namespace EulerIdentityOQ01

-- ============================================================================
-- § 1. POWER SERIES TERMS
-- ============================================================================

/-- The general term of the exponential series: z^n / n! -/
noncomputable def expTerm (z : ℂ) (n : ℕ) : ℂ := z ^ n / n.factorial

/-- The even-index term of exp(ix): (ix)^{2k}/(2k)! = (-1)^k x^{2k}/(2k)! -/
noncomputable def evenTerm (x : ℝ) (k : ℕ) : ℂ :=
  ((-1 : ℂ) ^ k * (x : ℂ) ^ (2 * k)) / (2 * k).factorial

/-- The odd-index term of exp(ix): (ix)^{2k+1}/(2k+1)! = i·(-1)^k x^{2k+1}/(2k+1)! -/
noncomputable def oddTerm (x : ℝ) (k : ℕ) : ℂ :=
  (I * (-1 : ℂ) ^ k * (x : ℂ) ^ (2 * k + 1)) / (2 * k + 1).factorial

-- ============================================================================
-- § 2. ALGEBRAIC IDENTITIES: Powers of i
-- ============================================================================

/-- i^{2k} = (-1)^k. The key identity for the even terms. -/
theorem I_pow_even (k : ℕ) : (I : ℂ) ^ (2 * k) = (-1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, pow_add, ih, I_sq]
    ring

/-- i^{2k+1} = i·(-1)^k. The key identity for the odd terms. -/
theorem I_pow_odd (k : ℕ) : (I : ℂ) ^ (2 * k + 1) = I * (-1) ^ k := by
  rw [pow_succ, I_pow_even]; ring

/-- i^4 = 1: the fourth power of i is unity. -/
theorem I_pow_four : (I : ℂ) ^ 4 = 1 := by
  have : (I : ℂ) ^ 4 = (I ^ 2) ^ 2 := by ring
  rw [this, I_sq]; ring

/-- Powers of i are periodic with period 4: i^(n+4) = i^n. -/
theorem I_pow_cycle (n : ℕ) : (I : ℂ) ^ (n + 4) = I ^ n := by
  rw [pow_add, I_pow_four, mul_one]

/-- The zeroth term of the exponential series equals 1. -/
theorem expTerm_zero (z : ℂ) : expTerm z 0 = 1 := by
  simp [expTerm]

/-- Consecutive terms satisfy expTerm z (n+1) = expTerm z n · z / (n+1). -/
theorem expTerm_succ_div (z : ℂ) (n : ℕ) :
    expTerm z (n + 1) = expTerm z n * z / (n + 1) := by
  simp only [expTerm, pow_succ, Nat.factorial_succ, Nat.cast_mul]
  field_simp
  ring

/-- The even-indexed exp term equals the cosine series term.
    (ix)^{2k}/(2k)! = (-1)^k x^{2k}/(2k)! -/
theorem expTerm_even (x : ℝ) (k : ℕ) :
    expTerm (↑x * I) (2 * k) = evenTerm x k := by
  simp only [expTerm, evenTerm]
  rw [mul_pow, show (↑x : ℂ) ^ (2 * k) * I ^ (2 * k) = I ^ (2 * k) * (↑x) ^ (2 * k) from
    by ring, I_pow_even]

/-- The odd-indexed exp term equals the sine series term (times i).
    (ix)^{2k+1}/(2k+1)! = i·(-1)^k x^{2k+1}/(2k+1)! -/
theorem expTerm_odd (x : ℝ) (k : ℕ) :
    expTerm (↑x * I) (2 * k + 1) = oddTerm x k := by
  simp only [expTerm, oddTerm]
  rw [mul_pow, show (↑x : ℂ) ^ (2 * k + 1) * I ^ (2 * k + 1) =
    I ^ (2 * k + 1) * (↑x) ^ (2 * k + 1) from by ring, I_pow_odd]
  ring

-- ============================================================================
-- § 3. TSUM SPLITTING (Axiomatized)
-- ============================================================================

/-- **Axiom 1: Even/odd splitting of absolutely convergent series.**

    For any absolutely convergent series ∑_n a_n over ℂ:
      ∑_n a_n = ∑_k a_{2k} + ∑_k a_{2k+1}

    This is a standard result from the theory of rearrangements:
    every absolutely convergent series can be split into even- and
    odd-indexed subseries, and the sums add up.

    Not yet a one-liner in Mathlib: requires `HasSum.even_add_odd` or
    manual construction via `Equiv.sumCompl` on even/odd naturals. -/
axiom tsum_even_add_odd {a : ℕ → ℂ} (ha : Summable a) :
    ∑' n, a n = (∑' k, a (2 * k)) + (∑' k, a (2 * k + 1))

-- ============================================================================
-- § 4. IDENTIFICATION WITH COS AND SIN (Axiomatized)
-- ============================================================================

/-- **Axiom 2: The cosine Taylor series.**

    cos(x) = ∑_k (-1)^k x^{2k} / (2k)!

    This is the standard power series definition of cos. In Mathlib,
    Complex.cos is defined as (exp(iz) + exp(-iz))/2, so proving this
    from the power series requires work. An independent proof via the
    ODE y'' = -y can also be used. -/
axiom cos_eq_tsum (x : ℝ) :
    (↑(cos x) : ℂ) = ∑' k, evenTerm x k

/-- **Axiom 2b: The sine Taylor series.**

    sin(x) = ∑_k (-1)^k x^{2k+1} / (2k+1)!

    Same situation as cos: Mathlib defines sin from exp, so the
    power series identity requires derivation. -/
axiom sin_eq_tsum (x : ℝ) :
    (↑(sin x) : ℂ) * I = ∑' k, oddTerm x k

-- ============================================================================
-- § 5. THE MAIN THEOREM
-- ============================================================================

/-- Summability of the exponential series (from Mathlib). -/
theorem expSeries_summable (z : ℂ) : Summable (expTerm z) := by
  have h := NormedSpace.expSeries_summable (𝕂 := ℂ) z
  exact h.congr fun n => by simp [expTerm, NormedSpace.expSeries, smul_eq_mul, div_eq_mul_inv]

/-- **Euler's Formula via Taylor Series (OQ-01).**

    e^{ix} = cos(x) + i·sin(x)

    Proof by Taylor series splitting:
    1. exp(ix) = ∑_n (ix)^n/n!
    2. = ∑_k (ix)^{2k}/(2k)! + ∑_k (ix)^{2k+1}/(2k+1)!    [even/odd split]
    3. = ∑_k (-1)^k x^{2k}/(2k)! + i·∑_k (-1)^k x^{2k+1}/(2k+1)!    [powers of i]
    4. = cos(x) + i·sin(x)    [Taylor series identification]

    This proof does NOT use `Complex.exp_mul_I` — it derives Euler's formula
    from first principles (power series). -/
theorem euler_formula_taylor (x : ℝ) :
    exp (↑x * I) = ↑(cos x) + ↑(sin x) * I := by
  -- Step 1: exp(ix) = ∑_n (ix)^n/n!
  have exp_eq : exp (↑x * I) = ∑' n, expTerm (↑x * I) n := by
    rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
    apply tsum_congr; intro n
    simp [expTerm, smul_eq_mul, div_eq_mul_inv]
  rw [exp_eq]
  -- Step 2: Split into even and odd terms
  rw [tsum_even_add_odd (expSeries_summable _)]
  -- Step 3: Rewrite even terms as cos, odd terms as i·sin
  conv_lhs =>
    arg 1; ext k; rw [expTerm_even]
  conv_lhs =>
    arg 2; ext k; rw [expTerm_odd]
  -- Step 4: Identify with cos and sin
  rw [← cos_eq_tsum, ← sin_eq_tsum]
  ring

/-- **Euler's Identity** from the Taylor series proof.
    e^{iπ} + 1 = 0. -/
theorem euler_identity_taylor : exp (↑π * I) + 1 = 0 := by
  have h := euler_formula_taylor π
  simp [cos_pi, sin_pi] at h
  linarith

-- ============================================================================
-- § 6. WHAT REMAINS TO FORMALIZE
-- ============================================================================

/-
## Axiom Elimination Roadmap

### Axiom 1 (tsum_even_add_odd):
- **Need:** Split ∑ a_n = ∑ a_{2k} + ∑ a_{2k+1} for summable series
- **Approach:** Use the bijection ℕ ≃ ℕ ⊕ ℕ sending n to (n/2, n%2),
  then apply `tsum_sum_compl` or `Equiv.tsum_eq`
- **Mathlib has:** `HasSum.sigma`, `Equiv.summable_iff`, `tsum_equiv`
- **Difficulty:** LOW (≈50 lines, mostly API wrangling)

### Axioms 2/2b (cos_eq_tsum, sin_eq_tsum):
- **Need:** Show cos(x) equals the even subseries, sin(x) the odd
- **Approach A:** From Mathlib's definition cos = (exp(iz)+exp(-iz))/2,
  expand both exponentials as power series and collect terms
- **Approach B:** From the ODE characterization y'' = -y, show the
  power series solution equals cos/sin
- **Approach C:** Use TaylorSinCosConvergence.lean's results about
  sin/cos partial sums converging
- **Difficulty:** MODERATE (≈150-200 lines)

### Total estimate: ≈200-250 lines to eliminate all axioms

## Note on Independence

This proof is logically independent of `Complex.exp_mul_I` — it derives
Euler's formula from the power series. However, in Mathlib, cos and sin
are DEFINED from exp, so a truly independent proof would need to either:
(a) define cos/sin via their Taylor series (as we do here), or
(b) define them via the ODE y'' = -y

Option (a) is implemented in this file via the cos_eq_tsum/sin_eq_tsum
axioms, which could be proved from TaylorSinCosConvergence.lean's results.
-/

end EulerIdentityOQ01
