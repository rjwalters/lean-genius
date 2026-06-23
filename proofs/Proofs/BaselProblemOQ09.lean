import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

/-
# The Odd-Square Series: ∑ 1/(2k+1)² = π²/8

## What This Proves
The sum of the reciprocals of the *odd* squares equals π²/8:

  ∑_{k=0}^∞ 1/(2k+1)² = 1/1² + 1/3² + 1/5² + ⋯ = π²/8

## Approach (the even/odd split of the Basel sum)
This is the standard corollary of the Basel problem ∑ 1/n² = π²/6.
Split the Basel sum into its even and odd index parts:

  ∑_{n≥1} 1/n²  =  ∑_{k≥1} 1/(2k)²  +  ∑_{k≥0} 1/(2k+1)².

The even part is a rescaled copy of the whole Basel sum:

  ∑_{k} 1/(2k)²  =  (1/4) · ∑_{k} 1/k²  =  (1/4)·(π²/6)  =  π²/24.

Mathlib's `HasSum.even_add_odd` recombines the even and odd subseries into the
full sum, so by uniqueness of sums

  π²/24 + (odd part)  =  π²/6   ⟹   (odd part) = π²/6 − π²/24 = π²/8.

## Provenance
- Foundation: `hasSum_zeta_two` from `Mathlib.NumberTheory.ZetaValues`
  (the Basel identity, already used by the parent `basel-problem` entry).
- Split: `HasSum.even_add_odd` from `Mathlib.Topology.Algebra.InfiniteSum.NatInt`.
- Rescaling: `HasSum.mul_left`; summability of the odd subseries via
  `Summable.comp_injective`; identification of the value via `HasSum.unique`.

This entry answers the open question `basel-problem-oq-09`: it carries out the
even/odd decomposition explicitly rather than quoting the odd-square value.

## Status
- [x] Complete proof, 0 sorries, 0 axioms.

Original formalization for Lean Genius.
-/

namespace BaselProblemOQ09

open Real Filter Topology

/-- The Basel summand `n ↦ 1/n²`, named so that `HasSum.even_add_odd` can unify
the even/odd subseries `fun k ↦ f (2*k)` and `fun k ↦ f (2*k+1)`. -/
private noncomputable def f : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2

/-- The Basel identity, restated for the local summand `f`. -/
private theorem basel_f : HasSum f (π ^ 2 / 6) := by
  exact hasSum_zeta_two

/-- The Basel series is summable. -/
private theorem summable_f : Summable f := basel_f.summable

/-! ## The even part -/

/-- The even-index part of the Basel sum is a rescaled Basel sum:
`∑ₖ 1/(2k)² = (1/4)·(π²/6) = π²/24`. -/
theorem hasSum_even_squares :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ)) ^ 2) (π ^ 2 / 24) := by
  have hfun : (fun k : ℕ => 1 / (2 * (k : ℝ)) ^ 2)
            = (fun k : ℕ => (1 / 4 : ℝ) * f k) := by
    funext k; simp only [f]; ring
  rw [hfun]
  have h := basel_f.mul_left (1 / 4 : ℝ)
  have hval : (1 / 4 : ℝ) * (π ^ 2 / 6) = π ^ 2 / 24 := by ring
  rw [hval] at h
  exact h

/-- The tsum form of the even part. -/
theorem tsum_even_squares : ∑' k : ℕ, 1 / (2 * (k : ℝ)) ^ 2 = π ^ 2 / 24 :=
  hasSum_even_squares.tsum_eq

/-! ## The odd part — the main result -/

/-- **The odd-square series.** The reciprocals of the odd squares sum to π²/8:

  `∑_{k≥0} 1/(2k+1)² = 1 + 1/9 + 1/25 + ⋯ = π²/8`. -/
theorem hasSum_odd_squares :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 2) (π ^ 2 / 8) := by
  -- Even part, written in the `f (2*k)` shape required by `even_add_odd`.
  have heven : HasSum (fun k : ℕ => f (2 * k)) (π ^ 2 / 24) := by
    have hfun : (fun k : ℕ => f (2 * k))
              = (fun k : ℕ => 1 / (2 * (k : ℝ)) ^ 2) := by
      funext k; simp only [f]; push_cast; ring
    rw [hfun]; exact hasSum_even_squares
  -- The odd subseries is summable (an injective reindexing of a summable series).
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b h; dsimp only at h; omega
  have hodd_sum : Summable (fun k : ℕ => f (2 * k + 1)) := by
    have h := summable_f.comp_injective hinj
    simpa [Function.comp] using h
  have hodd : HasSum (fun k : ℕ => f (2 * k + 1)) (∑' k, f (2 * k + 1)) :=
    hodd_sum.hasSum
  -- Recombine even + odd into the full Basel sum, then identify the odd value.
  have hcomb : HasSum f (π ^ 2 / 24 + ∑' k, f (2 * k + 1)) :=
    heven.even_add_odd hodd
  have huniq : π ^ 2 / 24 + ∑' k, f (2 * k + 1) = π ^ 2 / 6 :=
    hcomb.unique basel_f
  have hval : (∑' k, f (2 * k + 1)) = π ^ 2 / 8 := by linarith
  -- Bridge the local `f`-form to the clean statement.
  have hbridge : (fun k : ℕ => f (2 * k + 1))
               = (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 2) := by
    funext k; simp only [f]; push_cast; ring
  rw [hval] at hodd
  rw [hbridge] at hodd
  exact hodd

/-- The tsum form of the main result: `∑' k, 1/(2k+1)² = π²/8`. -/
theorem tsum_odd_squares : ∑' k : ℕ, 1 / (2 * (k : ℝ) + 1) ^ 2 = π ^ 2 / 8 :=
  hasSum_odd_squares.tsum_eq

/-- The odd-square series is summable. -/
theorem summable_odd_squares : Summable (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 2) :=
  hasSum_odd_squares.summable

/-- The value π²/8 is positive. -/
theorem odd_squares_value_pos : (0 : ℝ) < π ^ 2 / 8 := by positivity

/-! ## The decomposition identity

The even and odd parts add back to the full Basel value. -/

/-- The even/odd decomposition of the Basel value: `π²/6 = π²/24 + π²/8`. -/
theorem basel_even_odd_decomposition : π ^ 2 / 6 = π ^ 2 / 24 + π ^ 2 / 8 := by
  ring

/-- The odd part exceeds the even part: `π²/24 < π²/8`
(three quarters of the Basel mass lives on the odd indices). -/
theorem odd_part_gt_even_part : π ^ 2 / 24 < π ^ 2 / 8 := by
  have : (0 : ℝ) < π ^ 2 := by positivity
  linarith

/-! ## Numerical sanity checks -/

/-- The first odd term is `1/1² = 1`. -/
example : (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 2) 0 = 1 := by norm_num

/-- The second odd term is `1/3² = 1/9`. -/
example : (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 2) 1 = 1 / 9 := by norm_num

end BaselProblemOQ09
