import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

/-
# Odd-power Dirichlet λ-values: the general even/odd split and λ(4) = π⁴/96

## What This Proves
The reciprocal sum over the **odd** integers raised to an even power `s` is a fixed
rational multiple of the corresponding ζ-value:

  ∑_{k≥0} 1/(2k+1)^s = (1 − 2^{-s}) · ζ(s).

This is the Dirichlet lambda function λ(s) = (1 − 2^{-s}) ζ(s). The parent entry
`basel-problem-oq-09` carried out the `s = 2` case by hand (∑ 1/(2k+1)² = π²/8).
Here we extract the split as a **single general lemma** `hasSum_odd_pow`, valid for
every exponent, and then read off two clean closed forms:

  s = 4:  ∑_{k≥0} 1/(2k+1)⁴ = (1 − 1/16)·(π⁴/90) = (15/16)·(π⁴/90) = π⁴/96,
  s = 2:  ∑_{k≥0} 1/(2k+1)² = (1 − 1/4)·(π²/6)  = (3/4)·(π²/6)   = π²/8.

## Approach (the even/odd split, once and for all)
For any exponent `s`, split the full p-series `∑_n 1/n^s` into even and odd indices:

  ∑_{n≥0} 1/n^s  =  ∑_{k} 1/(2k)^s  +  ∑_{k} 1/(2k+1)^s.

The even part is a *termwise* rescaling of the whole series, because
`(2k)^s = 2^s · k^s`, so `1/(2k)^s = 2^{-s} · 1/k^s`. Hence

  ∑_{k} 1/(2k)^s  =  2^{-s} · ζ(s).

Mathlib's `HasSum.even_add_odd` recombines the even and odd subseries into the full
series; uniqueness of sums then pins the odd part to `(1 − 2^{-s})·ζ(s)`.

The key economy over the parent: the even part is obtained by `HasSum.mul_left`
applied to the *full* series (the `k = 0` term `1/(2·0)^s = 0` is harmless for
`s ≥ 1`), so no sub-series summability bookkeeping is needed for the even half.

## Provenance
- ζ(4) = π⁴/90: `hasSum_zeta_four` from `Mathlib.NumberTheory.ZetaValues`.
- ζ(2) = π²/6:  `hasSum_zeta_two`  from the same file.
- Split:        `HasSum.even_add_odd` (`Mathlib.Topology.Algebra.InfiniteSum.NatInt`).
- Rescaling:    `HasSum.mul_left`; uniqueness via `HasSum.unique`.

This answers the open question `basel-problem-oq-09-oq-01`: generalize the even/odd
parity split to `λ(2m) = (1 − 2^{-2m}) ζ(2m)` and derive `λ(4) = π⁴/96` from
`hasSum_zeta_four`.

## Status
- [x] Complete proof, 0 sorries, 0 axioms.

Original formalization for Lean Genius.
-/

namespace BaselProblemOQ0901

open Real Filter Topology

/-! ## The general even/odd split

`hasSum_odd_pow` is the engine: from the ζ-value at exponent `s` it produces the
closed form for the odd-index sum, for *any* `s`. Both `λ(2)` and `λ(4)` below are
one-line instances. -/

/-- **General odd-power split.** If the p-series `∑ₙ 1/n^s` sums to `Z`, then the
odd-index subseries sums to `(1 − 2^{-s})·Z`:

  `∑_{k≥0} 1/(2k+1)^s = (1 − 1/2^s) · Z`.

For even `s = 2m` and `Z = ζ(s)` this is the Dirichlet lambda value
`λ(2m) = (1 − 2^{-2m}) ζ(2m)`. -/
theorem hasSum_odd_pow (s : ℕ) {Z : ℝ}
    (h : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ s) Z) :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ s) ((1 - 1 / 2 ^ s) * Z) := by
  -- Name the full summand so `HasSum.even_add_odd` can unify the two subseries.
  set f : ℕ → ℝ := fun n : ℕ => 1 / (n : ℝ) ^ s with hf
  -- The even part is a termwise rescaling of the *whole* series by `2^{-s}`.
  have heven : HasSum (fun k : ℕ => f (2 * k)) ((1 / 2 ^ s) * Z) := by
    have hfun : (fun k : ℕ => f (2 * k))
              = (fun k : ℕ => (1 / 2 ^ s) * f k) := by
      funext k
      simp only [hf]
      push_cast
      rw [mul_pow]
      ring
    rw [hfun]
    exact h.mul_left _
  -- The odd subseries is summable (an injective reindexing of a summable series).
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b hab; dsimp only at hab; omega
  have hodd_sum : Summable (fun k : ℕ => f (2 * k + 1)) := by
    have h := h.summable.comp_injective hinj
    simpa [Function.comp] using h
  have hodd : HasSum (fun k : ℕ => f (2 * k + 1)) (∑' k, f (2 * k + 1)) :=
    hodd_sum.hasSum
  -- Recombine even + odd into the full series, then identify the odd value.
  have hcomb : HasSum f ((1 / 2 ^ s) * Z + ∑' k, f (2 * k + 1)) :=
    heven.even_add_odd hodd
  have huniq : (1 / 2 ^ s) * Z + ∑' k, f (2 * k + 1) = Z := hcomb.unique h
  have hval : (∑' k, f (2 * k + 1)) = (1 - 1 / 2 ^ s) * Z := by
    linear_combination huniq
  -- Bridge the local `f`-form to the clean `1/(2k+1)^s` statement.
  have hbridge : (fun k : ℕ => f (2 * k + 1))
               = (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ s) := by
    funext k; simp only [hf]; push_cast; ring
  rw [hval] at hodd
  rw [hbridge] at hodd
  exact hodd

/-! ## λ(4) = π⁴/96 — the main result -/

/-- **The odd-fourth-power series.** The reciprocals of the odd fourth powers sum to
`π⁴/96`:

  `∑_{k≥0} 1/(2k+1)⁴ = 1 + 1/81 + 1/625 + ⋯ = π⁴/96`.

This is `λ(4) = (1 − 2^{-4}) ζ(4) = (15/16)·(π⁴/90)`, derived from
`hasSum_zeta_four`. -/
theorem hasSum_odd_fourth :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 4) (π ^ 4 / 96) := by
  have h := hasSum_odd_pow 4 hasSum_zeta_four
  have hval : (1 - 1 / 2 ^ 4) * (π ^ 4 / 90) = π ^ 4 / 96 := by ring
  rwa [hval] at h

/-- The tsum form of the main result: `∑' k, 1/(2k+1)⁴ = π⁴/96`. -/
theorem tsum_odd_fourth : ∑' k : ℕ, 1 / (2 * (k : ℝ) + 1) ^ 4 = π ^ 4 / 96 :=
  hasSum_odd_fourth.tsum_eq

/-- The odd-fourth-power series is summable. -/
theorem summable_odd_fourth :
    Summable (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 4) :=
  hasSum_odd_fourth.summable

/-! ## λ(2) = π²/8 — recovering the parent result from the general lemma -/

/-- The parent entry's odd-square value `∑ 1/(2k+1)² = π²/8`, now a one-line instance
of `hasSum_odd_pow` at `s = 2` with `ζ(2) = π²/6`. -/
theorem hasSum_odd_squares :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 2) (π ^ 2 / 8) := by
  have h := hasSum_odd_pow 2 hasSum_zeta_two
  have hval : (1 - 1 / 2 ^ 2) * (π ^ 2 / 6) = π ^ 2 / 8 := by ring
  rwa [hval] at h

/-! ## The even fourth-power part and the decomposition identity -/

/-- The even-index part of the ζ(4) sum is a rescaled ζ(4):
`∑ₖ 1/(2k)⁴ = (1/16)·(π⁴/90) = π⁴/1440`. -/
theorem hasSum_even_fourth :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ)) ^ 4) (π ^ 4 / 1440) := by
  have hfun : (fun k : ℕ => 1 / (2 * (k : ℝ)) ^ 4)
            = (fun k : ℕ => (1 / 16 : ℝ) * (1 / (k : ℝ) ^ 4)) := by
    funext k; rw [mul_pow]; ring
  rw [hfun]
  have h := hasSum_zeta_four.mul_left (1 / 16 : ℝ)
  have hval : (1 / 16 : ℝ) * (π ^ 4 / 90) = π ^ 4 / 1440 := by ring
  rwa [hval] at h

/-- The tsum form of the even part. -/
theorem tsum_even_fourth : ∑' k : ℕ, 1 / (2 * (k : ℝ)) ^ 4 = π ^ 4 / 1440 :=
  hasSum_even_fourth.tsum_eq

/-- The even/odd decomposition of the ζ(4) value: `π⁴/90 = π⁴/1440 + π⁴/96`. -/
theorem zeta_four_even_odd_decomposition :
    π ^ 4 / 90 = π ^ 4 / 1440 + π ^ 4 / 96 := by
  ring

/-- The odd part dominates the even part at exponent 4 even more strongly than at
exponent 2: `π⁴/1440 < π⁴/96` (the odd indices carry 15/16 of the ζ(4) mass). -/
theorem odd_part_gt_even_part_fourth : π ^ 4 / 1440 < π ^ 4 / 96 := by
  have : (0 : ℝ) < π ^ 4 := by positivity
  linarith

/-- The value `π⁴/96` is positive. -/
theorem odd_fourth_value_pos : (0 : ℝ) < π ^ 4 / 96 := by positivity

/-! ## Numerical sanity checks -/

/-- The first odd-fourth term is `1/1⁴ = 1`. -/
example : (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 4) 0 = 1 := by norm_num

/-- The second odd-fourth term is `1/3⁴ = 1/81`. -/
example : (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 4) 1 = 1 / 81 := by norm_num

/-- The third odd-fourth term is `1/5⁴ = 1/625`. -/
example : (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 4) 2 = 1 / 625 := by norm_num

end BaselProblemOQ0901
