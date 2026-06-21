import Mathlib.Algebra.GeomSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-
# Second-Order Arithmetico-Geometric Sums: ∑ k²·xᵏ and its Infinite Limit

## What This Proves
The **finite** closed form for the *second-order* arithmetico-geometric sum
∑_{k<n} k²·xᵏ over an arbitrary commutative ring, with an explicit truncation
defect, the field form, and the bridge that recovers the infinite second
moment x(1+x)/(1−x)³ as the n → ∞ limit.

This fills the missing cell in the moment × truncation grid for the geometric
series:
- parent oq-08 (zeroth moment, finite defect): ∑_{k<n} xᵏ vs (1−x)⁻¹
- sibling oq-08-oq-01 (first moment, finite): ∑_{k<n} k·xᵏ, closed via (1−x)²
- sibling oq-07 (second moment, **infinite** only): ∑_{n≥0} n²·rⁿ = r(1+r)/(1−r)³
- **this entry** (second moment, **finite**): ∑_{k<n} k²·xᵏ, closed via (1−x)³,
  with the explicit defect polynomial — the finite/defect form that oq-07
  (infinite tsum) does not provide.

The master identity (valid in ANY `CommRing`, no division) is

    (1 − x)³ · ∑_{k<n} k²·xᵏ
        = x + x² − xⁿ·(n² + (1 + 2n − 2n²)·x + (n−1)²·x²).

The polynomial tail Q(n,x) = n² + (1+2n−2n²)x + (n−1)²x² is exactly the
truncation defect: it captures everything the finite sum is missing relative
to the infinite series x(1+x)/(1−x)³. The induction step reduces to the
single ring identity Q(n) − x·Q(n+1) = n²·(1−x)³.

## Approach
- **Foundation (from Mathlib):** none beyond `Finset.sum_range_succ`; the core
  identity is a pure polynomial fact discharged by induction + `ring`.
- **Original contribution:** the explicit finite closed form for ∑_{k<n} k²·xᵏ
  with its `n`-dependent defect polynomial, the field form, and the bridge that
  recovers the infinite value as the defect tail vanishes. (The infinite value
  itself coincides with sibling oq-07's `hasSum_sq_mul_geometric`; here it is
  re-obtained as the limit of the finite closed form rather than assumed.)
- **Proof techniques:** induction on `n`, `ring` for the algebraic step,
  `tendsto`/`HasSum` plumbing for the analytic corollary.
-/

namespace GeometricSeriesOQ08OQ04

open Finset BigOperators Filter

-- ============================================================
-- PART 1: The finite closed form over an arbitrary CommRing
-- ============================================================

variable {R : Type*} [CommRing R]

/-- The defect polynomial: the degree-2 tail multiplying `xⁿ`.
`Q n x = n² + (1 + 2n − 2n²)·x + (n−1)²·x²`. -/
def defectPoly (n : ℕ) (x : R) : R :=
  (n : R) ^ 2 + (1 + 2 * n - 2 * (n : R) ^ 2) * x + ((n : R) - 1) ^ 2 * x ^ 2

/-- **Master identity** (no division, any `CommRing`):
`(1 − x)³ · ∑_{k<n} k²·xᵏ = x + x² − xⁿ · Q(n,x)`. -/
theorem cube_one_sub_mul_sum_sq_mul_pow (x : R) (n : ℕ) :
    (1 - x) ^ 3 * ∑ k ∈ range n, (k : R) ^ 2 * x ^ k
      = x + x ^ 2 - x ^ n * defectPoly n x := by
  induction n with
  | zero => simp [defectPoly]
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      -- Reduce to the ring identity  Q(n) − x·Q(n+1) = n²·(1−x)³,
      -- packaged as the goal after expanding `defectPoly` and `xⁿ⁺¹`.
      simp only [defectPoly, pow_succ, Nat.cast_succ]
      ring

-- ============================================================
-- PART 2: Field form
-- ============================================================

variable {K : Type*} [Field K]

/-- **Field closed form.** When `x ≠ 1`,
`∑_{k<n} k²·xᵏ = (x + x² − xⁿ·Q(n,x)) / (1 − x)³`. -/
theorem sum_sq_mul_pow_eq_div (x : K) (hx : x ≠ 1) (n : ℕ) :
    ∑ k ∈ range n, (k : K) ^ 2 * x ^ k
      = (x + x ^ 2 - x ^ n * defectPoly n x) / (1 - x) ^ 3 := by
  have hne : (1 - x) ^ 3 ≠ 0 := by
    have : (1 : K) - x ≠ 0 := sub_ne_zero.mpr (fun h => hx h.symm)
    exact pow_ne_zero 3 this
  rw [eq_div_iff hne, mul_comm]
  exact cube_one_sub_mul_sum_sq_mul_pow x n

-- ============================================================
-- PART 3: A few sanity specializations
-- ============================================================

/-- `n = 1`: the sum is empty of nonzero terms (only `k = 0`), so it vanishes,
and the master identity collapses to `0 = 0`. -/
theorem sum_sq_one (x : R) :
    ∑ k ∈ range 1, (k : R) ^ 2 * x ^ k = 0 := by
  simp

/-- `n = 2`: `∑_{k<2} k²·xᵏ = x`. -/
theorem sum_sq_two (x : R) :
    ∑ k ∈ range 2, (k : R) ^ 2 * x ^ k = x := by
  simp [Finset.sum_range_succ]

/-- `n = 3`: `∑_{k<3} k²·xᵏ = x + 4·x²`. -/
theorem sum_sq_three (x : R) :
    ∑ k ∈ range 3, (k : R) ^ 2 * x ^ k = x + 4 * x ^ 2 := by
  simp [Finset.sum_range_succ]; ring

-- ============================================================
-- PART 4: Bridge to the infinite limit  ∑ k²·xᵏ = x(1+x)/(1−x)³
-- ============================================================

/-- The defect tail `xⁿ · Q(n,x)` tends to `0` as `n → ∞` when `|x| < 1`.
This is the analytic content that turns the finite closed form into the
classical infinite value. -/
theorem defect_tendsto_zero {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun n => x ^ n * defectPoly n x) atTop (nhds 0) := by
  -- `xⁿ · (a·n² + b·n + c)` → 0 since geometric decay beats polynomial growth.
  unfold defectPoly
  have hnx : ‖x‖ < 1 := by simpa [Real.norm_eq_abs] using hx
  have h0 : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * x ^ n) atTop (nhds 0) :=
    (summable_pow_mul_geometric_of_norm_lt_one 2 hnx).tendsto_atTop_zero
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ 1 * x ^ n) atTop (nhds 0) :=
    (summable_pow_mul_geometric_of_norm_lt_one 1 hnx).tendsto_atTop_zero
  have h2 : Tendsto (fun n : ℕ => (n : ℝ) ^ 0 * x ^ n) atTop (nhds 0) :=
    (summable_pow_mul_geometric_of_norm_lt_one 0 hnx).tendsto_atTop_zero
  -- Expand `xⁿ · Q` into a sum of `nʲ · xⁿ` pieces, each tending to 0.
  have : (fun n : ℕ => x ^ n *
      ((n : ℝ) ^ 2 + (1 + 2 * n - 2 * (n : ℝ) ^ 2) * x + ((n : ℝ) - 1) ^ 2 * x ^ 2))
      = (fun n : ℕ =>
          (1 - 2 * x + x ^ 2) * ((n : ℝ) ^ 2 * x ^ n)
          + (2 * x - 2 * x ^ 2) * ((n : ℝ) ^ 1 * x ^ n)
          + (x + x ^ 2) * ((n : ℝ) ^ 0 * x ^ n)) := by
    funext n; ring
  rw [this]
  have := ((h0.const_mul (1 - 2 * x + x ^ 2)).add
            (h1.const_mul (2 * x - 2 * x ^ 2))).add
            (h2.const_mul (x + x ^ 2))
  simpa using this

/-- **Infinite value.** For `|x| < 1`,
`∑_{k} k²·xᵏ = x·(1 + x) / (1 − x)³`.
The partial sums converge to the closed form with the defect tail removed. -/
theorem hasSum_sq_mul_pow {x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ => (k : ℝ) ^ 2 * x ^ k) (x * (1 + x) / (1 - x) ^ 3) := by
  have hx1 : x ≠ 1 := fun h => by simp [h] at hx
  have hne : (1 - x) ^ 3 ≠ 0 := pow_ne_zero 3 (sub_ne_zero.mpr (fun h => hx1 h.symm))
  have hnx : ‖x‖ < 1 := by simpa [Real.norm_eq_abs] using hx
  -- absolute summability of `k² xᵏ` (pins down `f` before the rewrite)
  have hsum : Summable (fun k : ℕ => ‖(k : ℝ) ^ 2 * x ^ k‖) :=
    summable_norm_pow_mul_geometric_of_norm_lt_one 2 hnx
  -- A `HasSum` over ℕ is the `atTop` limit of partial sums `∑_{k<n}`.
  rw [hasSum_iff_tendsto_nat_of_summable_norm hsum]
  · -- limit of the field closed form as the defect tail vanishes
    have hform : (fun n => ∑ k ∈ range n, (k : ℝ) ^ 2 * x ^ k)
        = (fun n => (x + x ^ 2 - x ^ n * defectPoly n x) / (1 - x) ^ 3) := by
      funext n; exact sum_sq_mul_pow_eq_div x hx1 n
    rw [hform]
    have hlim : Tendsto (fun n => x + x ^ 2 - x ^ n * defectPoly n x) atTop
        (nhds (x + x ^ 2)) := by
      have := (tendsto_const_nhds (x := x + x ^ 2)).sub (defect_tendsto_zero hx)
      simpa using this
    have : Tendsto (fun n => (x + x ^ 2 - x ^ n * defectPoly n x) / (1 - x) ^ 3)
        atTop (nhds ((x + x ^ 2) / (1 - x) ^ 3)) :=
      hlim.div_const _
    have heq : (x + x ^ 2) / (1 - x) ^ 3 = x * (1 + x) / (1 - x) ^ 3 := by ring
    rwa [heq] at this

end GeometricSeriesOQ08OQ04
