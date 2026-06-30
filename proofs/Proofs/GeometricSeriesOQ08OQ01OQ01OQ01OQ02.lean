import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Proofs.GeometricSeriesOQ08OQ01OQ01OQ01

/-
# The infinite-limit recurrence: ∑_{k≥0} kᵐ·xᵏ for |x| < 1

## What This Proves

Fix a real ratio `x` with `|x| < 1`.  The **infinite m-th moment**

  infMoment m x  :=  ∑_{k=0}^{∞} kᵐ·xᵏ

(the convergent weighted geometric series) satisfies the single
binomial-convolution recurrence

  (1 − x) · infMoment m x  =  0ᵐ  +  x · ∑_{i=0}^{m−1} C(m,i) · infMoment i x.   (★∞)

This is exactly the `n → ∞` limit of the finite master recurrence

  (1 − x) · momentSum m n x  =  0ᵐ − nᵐ·xⁿ + x · ∑_{i<m} C(m,i) · momentSum i n x

proved in the parent `geometric-series-oq-08-oq-01-oq-01-oq-01`: for `|x| < 1`
the finite partial sums `momentSum m n x` converge to `infMoment m x`, while the
boundary term `nᵐ·xⁿ` — being the general term of a convergent series — vanishes
in the limit.  The boundary correction that the finite sum had to carry simply
**washes out**, leaving the clean closed recurrence (★∞).

## Why This Is the Right Statement

Recurrence (★∞) is a *first-order-in-m convolution*: it expresses the `m`-th
moment through **all** lower moments using the Pascal/binomial weights `C(m,i)`,
with no derivatives and no special functions.  It is complementary to the two
explicit closed forms already in the gallery:

  * the **Stirling** form `geometric-series-oq-07-oq-01`
    (`∑ nᵐrⁿ = ∑ₖ S(m,k)·k!·rᵏ/(1−r)^{k+1}`), and
  * the **Frobenius / Eulerian-polynomial** form
    `geometric-series-oq-07-oq-01-oq-01` (`= Aₘ(r)/(1−r)^{m+1}`).

Those give `infMoment m` in one shot; (★∞) instead *characterises* the whole
sequence `(infMoment m)ₘ` by a recursion, and is the cleanest bridge from the
finite theory to the infinite one.  Solving (★∞) for small `m` recovers the
gallery's explicit sums:

  infMoment 0 x = 1/(1−x)
  infMoment 1 x = x/(1−x)²            (the infinite arithmetico-geometric sum)
  infMoment 2 x = x(1+x)/(1−x)³       (the infinite second moment ∑ k²xᵏ)

## Why This Is Not Already in Mathlib

Mathlib records summability of `∑ nᵏ rⁿ` (`summable_pow_mul_geometric_of_norm_lt_one`)
and the value of the plain geometric series, but neither the moment sum `∑ kᵐxᵏ`
as a named object nor any recurrence linking the infinite moments across `m`.

## Proof Strategy

1. **Summability.** `summable_pow_mul_geometric_of_norm_lt_one m (‖x‖<1)` gives
   `Summable (fun k ↦ kᵐ·xᵏ)` for every `m`.
2. **Convergence of partial sums.** `HasSum.tendsto_sum_nat` turns summability
   into `momentSum m n x → infMoment m x` (the partial sums are exactly the
   parent's `momentSum`).
3. **Boundary vanishes.** `Summable.tendsto_atTop_zero` gives `nᵐ·xⁿ → 0`, since
   that is the general term of the summable series of step 1.
4. **Pass to the limit.** Both sides of the parent's finite recurrence are
   sequences in `n`; taking `n → ∞` (LHS by continuity of `(1−x)·•`, RHS by
   linearity of limits over the finite inner sum) and using uniqueness of limits
   yields (★∞).
5. **Specialisations** solve (★∞) at `m = 0, 1, 2`, recovering the gallery's
   explicit closed forms.

All results depend only on `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace GeometricSeriesOQ08OQ01OQ01OQ01OQ02

open Finset Filter Topology
open GeometricSeriesOQ08OQ01OQ01OQ01 (momentSum momentSum_recurrence)

/-- The **infinite m-th moment** `∑_{k=0}^{∞} kᵐ·xᵏ` of a real geometric series. -/
noncomputable def infMoment (m : ℕ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, (k : ℝ) ^ m * x ^ k

/-- For `|x| < 1`, every moment series `∑ kᵐ·xᵏ` is summable. -/
theorem summable_moment (m : ℕ) {x : ℝ} (hx : |x| < 1) :
    Summable (fun k : ℕ => (k : ℝ) ^ m * x ^ k) :=
  summable_pow_mul_geometric_of_norm_lt_one m (by rwa [Real.norm_eq_abs])

/-- The finite moment sums converge to the infinite moment:
`momentSum m n x → infMoment m x` as `n → ∞` (for `|x| < 1`). -/
theorem tendsto_momentSum (m : ℕ) {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun n => momentSum m n x) atTop (𝓝 (infMoment m x)) := by
  simpa only [momentSum, infMoment] using (summable_moment m hx).hasSum.tendsto_sum_nat

/-- The boundary term of the finite recurrence vanishes in the limit:
`nᵐ·xⁿ → 0` as `n → ∞` (it is the general term of a convergent series). -/
theorem tendsto_boundary (m : ℕ) {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ m * x ^ n) atTop (𝓝 0) :=
  (summable_moment m hx).tendsto_atTop_zero

/-- **Master infinite recurrence (★∞).** For `|x| < 1`, over the reals,

  `(1 − x)·infMoment m x = 0ᵐ + x·∑_{i<m} C(m,i)·infMoment i x`.

This is the `n → ∞` limit of the parent's finite recurrence: the boundary term
`nᵐ·xⁿ` vanishes, leaving a clean binomial-convolution recursion that expresses
the `m`-th infinite moment through all lower moments. -/
theorem infMoment_recurrence (m : ℕ) {x : ℝ} (hx : |x| < 1) :
    (1 - x) * infMoment m x
      = (0 : ℝ) ^ m + x * ∑ i ∈ Finset.range m, (m.choose i : ℝ) * infMoment i x := by
  -- The two sides of the finite recurrence agree term-by-term.
  have hEq : ∀ n, (1 - x) * momentSum m n x
      = (0 : ℝ) ^ m - (n : ℝ) ^ m * x ^ n
        + x * ∑ i ∈ Finset.range m, (m.choose i : ℝ) * momentSum i n x :=
    fun n => momentSum_recurrence m n x
  -- LHS: `(1 − x)·momentSum m n x → (1 − x)·infMoment m x`.
  have hL : Tendsto (fun n => (1 - x) * momentSum m n x) atTop
      (𝓝 ((1 - x) * infMoment m x)) :=
    (tendsto_momentSum m hx).const_mul (1 - x)
  -- The inner finite sum converges term-by-term.
  have hInner : Tendsto
      (fun n => ∑ i ∈ Finset.range m, (m.choose i : ℝ) * momentSum i n x) atTop
      (𝓝 (∑ i ∈ Finset.range m, (m.choose i : ℝ) * infMoment i x)) :=
    tendsto_finset_sum _ fun i _ => (tendsto_momentSum i hx).const_mul _
  -- RHS converges to `0ᵐ − 0 + x·∑ C(m,i)·infMoment i x`.
  have hR : Tendsto
      (fun n : ℕ => (0 : ℝ) ^ m - (n : ℝ) ^ m * x ^ n
        + x * ∑ i ∈ Finset.range m, (m.choose i : ℝ) * momentSum i n x) atTop
      (𝓝 ((0 : ℝ) ^ m - 0
        + x * ∑ i ∈ Finset.range m, (m.choose i : ℝ) * infMoment i x)) :=
    ((tendsto_const_nhds.sub (tendsto_boundary m hx)).add (hInner.const_mul x))
  rw [sub_zero] at hR
  -- LHS and RHS are the same sequence, so their limits agree.
  exact tendsto_nhds_unique hL (hR.congr fun n => (hEq n).symm)

/-- For `m ≥ 1` the `0ᵐ` term drops, leaving the pure convolution recurrence
`(1 − x)·infMoment (m+1) x = x·∑_{i≤m} C(m+1,i)·infMoment i x`. -/
theorem infMoment_recurrence_succ (m : ℕ) {x : ℝ} (hx : |x| < 1) :
    (1 - x) * infMoment (m + 1) x
      = x * ∑ i ∈ Finset.range (m + 1), ((m + 1).choose i : ℝ) * infMoment i x := by
  have h := infMoment_recurrence (m + 1) hx
  simpa using h

/-- Solving (★∞) at `m = 0`: `infMoment 0 x = 1/(1 − x)` (the plain geometric
series), recovered from the recurrence (its `0⁰ = 1` constant term). -/
theorem infMoment_zero {x : ℝ} (hx : |x| < 1) :
    infMoment 0 x = (1 - x)⁻¹ := by
  have hne : (1 - x) ≠ 0 := by
    have : x < 1 := (abs_lt.mp hx).2
    linarith
  have h := infMoment_recurrence 0 hx
  simp only [pow_zero, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero] at h
  field_simp at h ⊢
  linarith [h]

/-- Solving (★∞) at `m = 1`: `infMoment 1 x = x/(1 − x)²`, the infinite
arithmetico-geometric sum `∑ k·xᵏ` (gallery `geometric-series-oq-08-oq-01`). -/
theorem infMoment_one {x : ℝ} (hx : |x| < 1) :
    infMoment 1 x = x / (1 - x) ^ 2 := by
  have hne : (1 - x) ≠ 0 := by
    have : x < 1 := (abs_lt.mp hx).2
    linarith
  have h := infMoment_recurrence 1 hx
  simp only [pow_one, Finset.range_one, Finset.sum_singleton,
    Nat.cast_one, one_mul, Nat.choose_zero_right] at h
  rw [infMoment_zero hx] at h
  field_simp at h ⊢
  linarith [h]

/-- Solving (★∞) at `m = 2`: `infMoment 2 x = x(1 + x)/(1 − x)³`, the infinite
second moment `∑ k²·xᵏ` (gallery `geometric-series-oq-08-oq-01-oq-01`). -/
theorem infMoment_two {x : ℝ} (hx : |x| < 1) :
    infMoment 2 x = x * (1 + x) / (1 - x) ^ 3 := by
  have hne : (1 - x) ≠ 0 := by
    have : x < 1 := (abs_lt.mp hx).2
    linarith
  have h := infMoment_recurrence 2 hx
  rw [Finset.sum_range_succ, Finset.sum_range_one] at h
  simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_ofNat, Nat.cast_one,
    one_mul] at h
  rw [infMoment_zero hx, infMoment_one hx] at h
  have hpow : (0 : ℝ) ^ 2 = 0 := by norm_num
  rw [hpow] at h
  field_simp at h ⊢
  ring_nf at h ⊢
  linarith [h]

end GeometricSeriesOQ08OQ01OQ01OQ01OQ02
