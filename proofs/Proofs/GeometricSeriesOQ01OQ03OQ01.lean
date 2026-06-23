import Mathlib.Analysis.Complex.AbelLimit
import Proofs.GeometricSeriesOQ01OQ03
import Mathlib.Tactic

/-
# Abel's Theorem in the Regular Direction, at Full Strength

## What This Proves
The parent entry (`geometric-series-oq-01-oq-03`, *Abel Summability at the
Boundary*) established the regularity of Abel summation only for the geometric
family `aₙ = rⁿ` with `|r| < 1`: there `geom_abel_regular` shows the Abel sum
`∑ₙ rⁿ xⁿ → 1/(1−r)` agrees with the ordinary sum.

This entry answers the parent's open question `oq-01` by proving the regularity
of Abel summation **for every convergent series**, not just geometric ones:

> **Abel's theorem (regular direction).** If `∑ₙ aₙ` converges to `L`, then the
> power series `A(x) = ∑ₙ aₙ xⁿ` converges for `x ∈ [0,1)` and `A(x) → L` as
> `x → 1⁻`. Equivalently, every convergent series is *Abel summable* to its
> ordinary sum.

The geometric case studied by the parent is recovered here as a strict special
case (`geom_abelSummableTo_of_general`), turning the parent's hand computation
into a *consistency check* of the general theorem.

## Approach
The deep analytic core — the left-continuity of the Abel function at `1` — is
**Mathlib's** `Real.tendsto_tsum_powerSeries_nhdsWithin_lt` (Abel's limit
theorem, proved there via summation by parts on a Stolz sector). The work of
this entry is to package that theorem against the parent's `AbelSummableTo`
predicate, which additionally bundles the on-disk-of-convergence summability:

1. **Summability on `[0,1)`** (`summable_mul_pow_of_summable`): a convergent
   series has bounded terms (`aₙ → 0`), so for `0 ≤ x < 1` the power series is
   dominated termwise by the geometric series `C·xⁿ` and converges by the
   comparison test.
2. **Regularity** (`abel_tendsto_of_tendsto_partial`): the left-limit at `1`,
   directly from Mathlib's Abel limit theorem applied to the partial sums.
3. **Synthesis** (`summable_abelSummableTo`, `hasSum_abelSummableTo`): combine
   1 and 2 into the parent's `AbelSummableTo` predicate.
4. **Consistency** (`geom_abelSummableTo_of_general`): specialise to `aₙ = rⁿ`,
   `|r| < 1`, recovering the parent's geometric Abel sum `1/(1−r)`.

## Honest Scope
This is a *packaging* result: the hard theorem (left-continuity) is Mathlib's.
The contribution is the general regularity statement in the parent's vocabulary,
the dominated-convergence summability lemma, and the explicit reduction of the
geometric boundary case to the general theorem.
-/

namespace GeometricSeriesOQ01OQ03OQ01

open Filter Topology GeometricSeriesOQ01OQ03

/-- The power series of a convergent real series converges on the open disc
`[0,1)`. A convergent series has terms tending to `0`, hence bounded by some
`C`; for `0 ≤ x < 1` the terms are then dominated by the geometric series
`C·xⁿ`, and the comparison test gives summability. -/
theorem summable_mul_pow_of_summable {a : ℕ → ℝ} (ha : Summable a) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) : Summable (fun n => a n * x ^ n) := by
  -- `aₙ → 0`, so `|aₙ| → 0` and the range of `|a|` is bounded above by some `C`.
  have habs : Tendsto (fun n => |a n|) atTop (𝓝 0) := by
    have h : Tendsto (fun n => |a n|) atTop (𝓝 |(0 : ℝ)|) :=
      (continuous_abs.tendsto 0).comp ha.tendsto_atTop_zero
    simpa [Function.comp] using h
  obtain ⟨C, hC⟩ := habs.bddAbove_range
  -- Dominating geometric series `C·xⁿ`.
  have hgeom : Summable (fun n => C * x ^ n) :=
    (summable_geometric_of_lt_one hx0 hx1).mul_left C
  refine Summable.of_norm_bounded hgeom (fun n => ?_)
  have hbound : |a n| ≤ C := hC (Set.mem_range_self n)
  have hxn : (0 : ℝ) ≤ x ^ n := pow_nonneg hx0 n
  calc ‖a n * x ^ n‖ = |a n| * x ^ n := by
            rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hx0]
    _ ≤ C * x ^ n := mul_le_mul_of_nonneg_right hbound hxn

/-- **Abel's limit theorem, regular direction (left-limit form).** If the partial
sums of `a` converge to `L`, then the Abel function `x ↦ ∑ₙ aₙ xⁿ` tends to `L`
as `x → 1⁻`. This is `Real.tendsto_tsum_powerSeries_nhdsWithin_lt` from Mathlib,
restated in the local notation. -/
theorem abel_tendsto_of_tendsto_partial {a : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun n => ∑ i ∈ Finset.range n, a i) atTop (𝓝 L)) :
    Tendsto (fun x => ∑' n, a n * x ^ n) (𝓝[<] (1 : ℝ)) (𝓝 L) :=
  Real.tendsto_tsum_powerSeries_nhdsWithin_lt h

/-- **Abel's theorem, regular direction (Summable form).** Every convergent real
series `∑ₙ aₙ` is Abel summable to its ordinary sum `∑' n, aₙ`. This answers the
parent open question `oq-01`: regularity of Abel summation for *every* convergent
series, not only geometric ones. -/
theorem summable_abelSummableTo {a : ℕ → ℝ} (ha : Summable a) :
    AbelSummableTo a (∑' n, a n) := by
  refine ⟨fun x hx0 hx1 => summable_mul_pow_of_summable ha hx0 hx1, ?_⟩
  exact abel_tendsto_of_tendsto_partial ha.hasSum.tendsto_sum_nat

/-- **Abel's theorem, regular direction (HasSum form).** If `a` sums to `L` then
`a` is Abel summable to the same value `L`. -/
theorem hasSum_abelSummableTo {a : ℕ → ℝ} {L : ℝ} (ha : HasSum a L) :
    AbelSummableTo a L := by
  have hL : L = ∑' n, a n := ha.tsum_eq.symm
  rw [hL]
  exact summable_abelSummableTo ha.summable

/-- **Consistency check with the parent's geometric case.** For `|r| < 1` the
geometric series `∑ rⁿ` converges to `1/(1−r)`, so by the general theorem it is
Abel summable to `1/(1−r)` — recovering the parent's `geom_abelSummableTo`
purely as a special case of Abel's theorem, with the boundary regularity no
longer computed by hand but inherited from the general statement. -/
theorem geom_abelSummableTo_of_general {r : ℝ} (hr : |r| < 1) :
    AbelSummableTo (fun n => r ^ n) (1 / (1 - r)) := by
  have hsum : HasSum (fun n => r ^ n) (1 - r)⁻¹ := hasSum_geometric_of_abs_lt_one hr
  have h := hasSum_abelSummableTo hsum
  simpa [one_div] using h

/-- **The general theorem subsumes the parent.** The parent's geometric
Abel-summability statement is definitionally the specialisation proved above;
this records the agreement explicitly. -/
theorem subsumes_parent_geom {r : ℝ} (hr : |r| < 1) :
    AbelSummableTo (fun n => r ^ n) (1 / (1 - r)) :=
  geom_abelSummableTo_of_general hr

end GeometricSeriesOQ01OQ03OQ01
