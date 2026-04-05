import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Algebra.GeomSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-
# Euler Product Formula from Geometric Series

## What This Proves

For Re(s) > 1, the Riemann zeta function satisfies:

  ζ(s) = ∑_{n=1}^{∞} n^{-s} = ∏_{p prime} (1 - p^{-s})^{-1}

The key insight: each Euler factor is a **geometric series**:

  (1 - p^{-s})^{-1} = ∑_{k=0}^{∞} (p^{-s})^k

This converges because |p^{-s}| = p^{-Re(s)} < p^0 = 1 for Re(s) > 1.

## Proof Strategy

1. **Norm bound**: ‖(p : ℂ)^(-s)‖ = p^(-Re(s)) < 1 for prime p, Re(s) > 1.
   Uses |z^w| = |z|^{w.re} · exp(-w.im · arg z) with arg(positive real) = 0.

2. **Geometric series**: `tsum_geometric_of_norm_lt_one` gives the sum formula.

3. **Euler product**: `riemannZeta_eulerProduct_tprod` gives ζ(s) = ∏_p (1 - p^{-s})^{-1}.

4. **Bridge**: Combining 2 and 3 gives ζ(s) = ∏_p ∑_k (p^{-s})^k.

## Historical Context

Euler (1737) discovered: the Dirichlet series and prime product are equal.
Every positive integer n factors uniquely into prime powers, so every term n^{-s}
appears exactly once when the product ∏_p ∑_{k≥0} p^{-ks} is formally expanded.
The rigorous proof requires absolute convergence, which holds for Re(s) > 1
since p^{-Re(s)} ≤ 2^{-Re(s)} < 1 for all primes p.

## Status: 0 sorries, 0 axioms

## Mathlib Dependencies

- `riemannZeta_eulerProduct_tprod` : Main Euler product formula
- `tsum_geometric_of_norm_lt_one` : Geometric series sum in normed rings
- `summable_geometric_of_norm_lt_one` : Geometric series summability
- `Complex.abs_cpow_mul_exp_log_re` : |z^w| formula
- `Complex.arg_ofReal_of_nonneg` : arg of nonneg real = 0
- `Real.rpow_lt_rpow_of_exponent_lt` : b > 1 implies b^x increasing in x
-/

set_option maxHeartbeats 400000

noncomputable section

open Complex Real Nat Filter Topology BigOperators

namespace GeometricSeriesOQ03

/-! ## Part 1: Basic Estimates for Primes -/

/-- A prime p has (p : ℝ) ≥ 2. -/
lemma prime_cast_ge_two (p : Nat.Primes) : (2 : ℝ) ≤ (p : ℝ) := by
  exact_mod_cast p.prop.two_le

/-- A prime p has (p : ℝ) > 1. -/
lemma prime_cast_gt_one (p : Nat.Primes) : (1 : ℝ) < (p : ℝ) :=
  lt_of_lt_of_le one_lt_two (prime_cast_ge_two p)

/-- A prime p has (p : ℝ) > 0. -/
lemma prime_cast_pos (p : Nat.Primes) : (0 : ℝ) < (p : ℝ) :=
  lt_trans zero_lt_one (prime_cast_gt_one p)

/-! ## Part 2: Norm Formula for Complex Prime Powers -/

/-- For a prime p and s : ℂ, ‖(p : ℂ)^s‖ = (p : ℝ)^s.re.

**Proof**: The complex power formula gives |z^w| = |z|^{w.re} · exp(-w.im · arg z).
For z = (p : ℂ) (a positive real), arg z = 0, so the exp factor is 1.
Then |p^s| = p^{s.re}. -/
lemma prime_cpow_norm_eq (p : Nat.Primes) (s : ℂ) :
    ‖(p : ℂ) ^ s‖ = (p : ℝ) ^ s.re := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := prime_cast_pos p
  -- Cast p through ℝ → ℂ
  have hcast : (p : ℂ) = ((p : ℝ) : ℂ) := by norm_cast
  have hp_ne : ((p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp_pos.ne'
  rw [Complex.norm_eq_abs, hcast]
  -- Apply the complex power norm formula: |z^w| = |z|^{w.re} · exp(-w.im · z.arg)
  rw [Complex.abs_cpow_mul_exp_log_re hp_ne]
  -- For a positive real, arg = 0: exp(-(w.im · 0)) = exp(0) = 1
  have harg : ((p : ℝ) : ℂ).arg = 0 :=
    Complex.arg_ofReal_of_nonneg (le_of_lt hp_pos)
  -- Simplify: the exp factor vanishes, and abs of positive real = itself
  simp [harg, Complex.abs_ofReal, abs_of_pos hp_pos]

/-! ## Part 3: Convergence of Each Euler Factor -/

/-- For prime p and Re(s) > 1, the real power (p : ℝ)^(-Re(s)) < 1.

Since p > 1 and -Re(s) < 0, we have p^(-Re(s)) < p^0 = 1 by monotonicity. -/
lemma prime_rpow_neg_lt_one (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    (p : ℝ) ^ (-s.re) < 1 := by
  -- For base b > 1, the function b^x is strictly increasing in x
  -- So b^(-Re s) < b^0 = 1 since -Re s < 0
  calc (p : ℝ) ^ (-s.re)
      < (p : ℝ) ^ (0 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (prime_cast_gt_one p) (by linarith)
    _ = 1 := Real.rpow_zero _

/-- **Key Convergence Lemma**: ‖(p : ℂ)^(-s)‖ < 1 for prime p and Re(s) > 1.

This is the essential condition for the geometric series ∑_k ((p : ℂ)^(-s))^k
to converge to the Euler factor (1 - p^{-s})^{-1}. -/
theorem prime_cpow_norm_lt_one (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ < 1 := by
  rw [prime_cpow_norm_eq, Complex.neg_re]
  exact prime_rpow_neg_lt_one p hs

/-! ## Part 4: Geometric Series Identity for Each Euler Factor -/

/-- For Re(s) > 1 and prime p, the geometric series in (p : ℂ)^(-s) is summable. -/
theorem euler_factor_summable (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun k : ℕ => ((p : ℂ) ^ (-s)) ^ k) :=
  summable_geometric_of_norm_lt_one (prime_cpow_norm_lt_one p hs)

/-- **The Geometric Series Identity for Each Euler Factor**:

  ∑_{k=0}^{∞} ((p : ℂ)^{-s})^k = (1 - (p : ℂ)^{-s})^{-1}   for Re(s) > 1

By `tsum_geometric_of_norm_lt_one` with ratio r = (p : ℂ)^(-s), since ‖r‖ < 1. -/
theorem euler_factor_eq_geom_series (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    ∑' k : ℕ, ((p : ℂ) ^ (-s)) ^ k = (1 - (p : ℂ) ^ (-s))⁻¹ :=
  tsum_geometric_of_norm_lt_one (prime_cpow_norm_lt_one p hs)

/-- Each Euler factor equals the geometric series (equivalent form). -/
theorem geom_series_eq_euler_factor (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    (1 - (p : ℂ) ^ (-s))⁻¹ = ∑' k : ℕ, ((p : ℂ) ^ (-s)) ^ k :=
  (euler_factor_eq_geom_series p hs).symm

/-- Each Euler factor is nonzero for Re(s) > 1. -/
theorem euler_factor_ne_zero (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    (1 - (p : ℂ) ^ (-s))⁻¹ ≠ 0 := by
  apply inv_ne_zero.mpr
  rw [sub_ne_zero]
  intro heq
  have : ‖(p : ℂ) ^ (-s)‖ = 1 := by rw [heq]; simp
  linarith [prime_cpow_norm_lt_one p hs]

/-! ## Part 5: The Euler Product Formula and Main Bridge Theorem -/

/-- **The Euler Product Formula** (from Mathlib):

  ∏_{p prime} (1 - p^{-s})^{-1} = ζ(s)   for Re(s) > 1

The full proof in Mathlib uses the fundamental theorem of arithmetic and
absolute convergence of the Dirichlet series. -/
theorem euler_product_formula {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s :=
  riemannZeta_eulerProduct_tprod hs

/-- **Main Bridge Theorem**: The Riemann zeta function as a product of geometric series.

For Re(s) > 1:
  ζ(s) = ∏_{p prime} ∑_{k=0}^{∞} ((p : ℂ)^{-s})^k

**Mathematical story**: The Euler factor for prime p is the geometric series with
ratio r = p^{-s}. The product over all primes, via unique factorization, equals
the Dirichlet series ζ(s) = ∑_{n≥1} n^{-s}. -/
theorem zeta_eq_prod_geom_series {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, ∑' k : ℕ, ((p : ℂ) ^ (-s)) ^ k = riemannZeta s := by
  -- Each geometric series equals the corresponding Euler factor
  simp_rw [euler_factor_eq_geom_series _ hs]
  -- The product of Euler factors equals ζ(s)
  exact euler_product_formula hs

/-! ## Part 6: Quantitative Norm Bounds -/

/-- For prime p and Re(s) > 1: ‖(p : ℂ)^(-s)‖ ≤ 2^(-Re(s)).

Proof: p ≥ 2 ⟹ p^(Re s) ≥ 2^(Re s) ⟹ p^(-Re s) = (p^(Re s))⁻¹ ≤ (2^(Re s))⁻¹ = 2^(-Re s). -/
theorem prime_cpow_norm_le_two (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ (2 : ℝ) ^ (-s.re) := by
  rw [prime_cpow_norm_eq, Complex.neg_re]
  have hs_pos : (0 : ℝ) < s.re := lt_trans one_pos hs
  -- Rewrite as inverses
  rw [Real.rpow_neg (le_of_lt (prime_cast_pos p)),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  -- 2^s.re ≤ p^s.re since 2 ≤ p and s.re ≥ 0
  -- Hence (p^s.re)⁻¹ ≤ (2^s.re)⁻¹
  apply inv_le_inv_of_le (Real.rpow_pos_of_pos (by norm_num) s.re)
  exact Real.rpow_le_rpow (by norm_num) (prime_cast_ge_two p) (le_of_lt hs_pos)

/-- For Re(s) > 1: ‖(p : ℂ)^(-s)‖ < 1/2 for all primes p.

Since Re(s) > 1, the exponent -Re(s) < -1, giving 2^(-Re(s)) < 2^(-1) = 1/2. -/
theorem prime_cpow_norm_lt_half (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ < 1 / 2 :=
  calc ‖(p : ℂ) ^ (-s)‖
      ≤ (2 : ℝ) ^ (-s.re) := prime_cpow_norm_le_two p hs
    _ < (2 : ℝ) ^ (-(1 : ℝ)) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) (by linarith)
    _ = 1 / 2 := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_one]; norm_num

/-! ## Part 7: Non-Vanishing Corollary -/

/-- ζ(s) ≠ 0 for Re(s) > 1 (direct application of Mathlib's result). -/
theorem zeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re hs

end GeometricSeriesOQ03
