import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# Riemann Zeta at Four: ζ(4) = π⁴/90

## What This Proves
Euler's evaluation of the Riemann zeta function at `s = 4`:

  ζ(4) = ∑_{n=1}^∞ 1/n⁴ = π⁴/90,

recorded both as a real series (`HasSum` / `tsum`) and as the value of the
complex `riemannZeta 4`.  This is the fourth-power companion of the Basel
problem ζ(2) = π²/6.

## Original corollaries (not in Mathlib)
Mathlib already supplies the headline value (`hasSum_zeta_four`,
`riemannZeta_four`).  The new mathematical content of this entry is the
even/odd decomposition of the ζ(4) series, exactly parallel to the ζ(2) →
π²/8 odd-squares result:

  * **Sum of reciprocal even fourth powers**  ∑_{k} 1/(2k)⁴ = π⁴/1440
    (the ζ(4) series scaled by 1/16).
  * **Sum of reciprocal odd fourth powers**   ∑_{k} 1/(2k+1)⁴ = π⁴/96
    (the "odd zeta value" λ(4); obtained as π⁴/90 − π⁴/1440).

## Approach
No new analysis beyond Mathlib's `hasSum_zeta_four`.  The even subsequence
`k ↦ 1/(2k)⁴ = (1/16)·(1/k⁴)` is the original series scaled by `1/16`; the
`HasSum.even_add_odd` decomposition then pins the odd tail by uniqueness of
infinite sums:  π⁴/1440 + (odd) = π⁴/90, so the odd sum is π⁴/96.

## Status
- [x] Complete proof (0 sorries, 0 axioms)
- [x] Uses Mathlib for the underlying ζ(4) identity

## Mathlib Dependencies
- `hasSum_zeta_four` : ∑ 1/n⁴ = π⁴/90
- `riemannZeta_four` : riemannZeta 4 = π⁴/90
- `HasSum.even_add_odd`, `HasSum.mul_left`, `HasSum.unique`

Original formalization for Lean Genius.
-/

namespace BaselProblemOQ06

open Filter Topology Real

/-- The base summand `f n = 1/n⁴`. -/
private noncomputable def f (n : ℕ) : ℝ := 1 / (n : ℝ) ^ 4

/-- **ζ(4) as a real series** (Mathlib): `∑ 1/n⁴ = π⁴/90`. -/
theorem zeta_four_hasSum : HasSum f (π ^ 4 / 90) := hasSum_zeta_four

/-- **ζ(4) as a `tsum`**: `∑' n, 1/n⁴ = π⁴/90`. -/
theorem zeta_four_tsum : ∑' n : ℕ, f n = π ^ 4 / 90 :=
  zeta_four_hasSum.tsum_eq

/-- **ζ(4) as a value of the complex zeta function** (Mathlib):
`riemannZeta 4 = π⁴/90`. -/
theorem riemannZeta_four_value : riemannZeta 4 = (π : ℂ) ^ 4 / 90 :=
  riemannZeta_four

/-- **Sum of reciprocal even fourth powers**: `∑_{k} 1/(2k)⁴ = π⁴/1440`.

Each even-indexed term is `1/(2k)⁴ = (1/16)·(1/k⁴)`, so the even subsequence
is the ζ(4) series scaled by `1/16`, giving `(1/16)·(π⁴/90) = π⁴/1440`. -/
theorem hasSum_even_fourth : HasSum (fun k : ℕ => f (2 * k)) (π ^ 4 / 1440) := by
  have h : HasSum (fun n : ℕ => (1 / 16 : ℝ) * f n) ((1 / 16) * (π ^ 4 / 90)) :=
    zeta_four_hasSum.mul_left (1 / 16)
  have hval : (1 / 16 : ℝ) * (π ^ 4 / 90) = π ^ 4 / 1440 := by ring
  rw [hval] at h
  refine h.congr_fun ?_
  intro k
  show f (2 * k) = (1 / 16 : ℝ) * f k
  unfold f
  push_cast
  rw [show (2 * (k : ℝ)) ^ 4 = 16 * (k : ℝ) ^ 4 from by ring, one_div_mul_one_div]

/-- The odd subsequence `k ↦ 1/(2k+1)⁴` is summable (a subseries of a summable
series, via injective reindexing). -/
theorem summable_odd_fourth : Summable (fun k : ℕ => f (2 * k + 1)) := by
  have hi : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b hab
    have hab' : 2 * a + 1 = 2 * b + 1 := hab
    omega
  exact zeta_four_hasSum.summable.comp_injective hi

/-- **Sum of reciprocal odd fourth powers**: `∑_{k} 1/(2k+1)⁴ = π⁴/96`.

The even part (π⁴/1440) plus the odd part recovers the full ζ(4) sum (π⁴/90),
so the odd part equals `π⁴/90 − π⁴/1440 = π⁴/96`. -/
theorem hasSum_odd_fourth : HasSum (fun k : ℕ => f (2 * k + 1)) (π ^ 4 / 96) := by
  obtain ⟨b, hb⟩ := summable_odd_fourth
  have hcombined : HasSum f (π ^ 4 / 1440 + b) := hasSum_even_fourth.even_add_odd hb
  have heq : π ^ 4 / 90 = π ^ 4 / 1440 + b := zeta_four_hasSum.unique hcombined
  have hb_val : b = π ^ 4 / 96 := by linarith
  rwa [hb_val] at hb

/-- **Main odd-fourth-power identity** in the natural `(2k+1 : ℝ)` form:
`∑_{k=0}^∞ 1/(2k+1)⁴ = π⁴/96`. -/
theorem odd_fourth_hasSum :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 4) (π ^ 4 / 96) := by
  have h := hasSum_odd_fourth
  refine h.congr_fun ?_
  intro k
  show 1 / (2 * (k : ℝ) + 1) ^ 4 = f (2 * k + 1)
  unfold f
  push_cast
  ring

/-- The `tsum` form of the odd-fourth-power identity: `∑' k, 1/(2k+1)⁴ = π⁴/96`. -/
theorem odd_fourth_tsum :
    ∑' k : ℕ, 1 / (2 * (k : ℝ) + 1) ^ 4 = π ^ 4 / 96 :=
  odd_fourth_hasSum.tsum_eq

/-- Consistency: even part + odd part = full ζ(4) sum. -/
theorem even_add_odd_eq_zeta_four : π ^ 4 / 1440 + π ^ 4 / 96 = π ^ 4 / 90 := by
  ring

/-- Sanity check: the odd-fourth-power sum is positive. -/
theorem odd_fourth_pos : (0 : ℝ) < π ^ 4 / 96 := by positivity

end BaselProblemOQ06
