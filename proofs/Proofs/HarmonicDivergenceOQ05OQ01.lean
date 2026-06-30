import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic
import Proofs.HarmonicDivergenceOQ05

/-
# The Dyadic Upper Bound `H_{2^n} ≤ 1 + n` (Two-Sided Oresme Sandwich)

## What This Proves

The parent entry `HarmonicDivergenceOQ05` proves the explicit *lower* bound

  `H_{2^n} = ∑_{j=1}^{2^n} 1/j ≥ 1 + n/2`

by grouping the partial sum into dyadic blocks, each of which contributes at
least `1/2`. This entry proves the matching *upper* bound

  `H_{2^n} ≤ 1 + n`,

obtained from the dual observation that each dyadic block of `2^n` terms
contributes **at most `1`** (every term `1/(k+1)` with `2^n ≤ k < 2^{n+1}`
is at most `1/2^n`, and there are `2^n` of them). Together with the parent we
get the complete two-sided sandwich

  `1 + n/2 ≤ H_{2^n} ≤ 1 + n`,

pinning the `2^n`-th harmonic partial sum to a window of width `n/2` around
`1 + 3n/4`. This is the elementary fact behind `H_N ~ log N`: at the dyadic
sampling points `N = 2^n` the partial sum grows exactly linearly in `n` (up to
the factor between `1/2` and `1`), i.e. logarithmically in `N`.

Mathlib has neither the lower nor the upper closed-form bound on the harmonic
partial sums (only the existence-form divergence
`Real.tendsto_sum_range_one_div_nat_succ_atTop`); both directions are derived
here by a self-contained dyadic-block estimate and induction on `n`.

## Indexing convention

We reuse the parent's partial-sum definition
`H N = ∑_{k ∈ range N} 1/(k+1) = 1 + 1/2 + … + 1/N`.

## Status
- [x] Complete proof (0 sorries, 0 axioms)
- [x] Headline `harmonic_two_pow_le` is original to the gallery family
- [x] Corollary: the two-sided sandwich `harmonic_two_pow_sandwich`
-/

namespace HarmonicDivergenceOQ05OQ01

open Finset HarmonicDivergenceOQ05

/-- **Dual dyadic block estimate.** The block of `2^n` terms running from index
`2^n` to `2^{n+1} - 1` contributes at most `1`:

  `1/(2^n+1) + 1/(2^n+2) + … + 1/2^{n+1} ≤ 1`.

Each of the `2^n` terms is at most `1/2^n` (since `k + 1 ≥ 2^n` on the block),
and `2^n · (1/2^n) = 1`. -/
theorem block_le_one (n : ℕ) :
    ∑ k ∈ Finset.Ico (2 ^ n : ℕ) (2 ^ (n + 1)), (1 : ℝ) / (k + 1) ≤ 1 := by
  -- Each term in the block is ≤ 1 / 2^n.
  have hterm : ∀ k ∈ Finset.Ico (2 ^ n : ℕ) (2 ^ (n + 1)),
      (1 : ℝ) / (k + 1) ≤ (1 : ℝ) / 2 ^ n := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hpow_pos : (0 : ℝ) < 2 ^ n := by positivity
    have hle : (2 : ℝ) ^ n ≤ (k : ℝ) + 1 := by
      have : (2 : ℕ) ^ n ≤ k + 1 := by omega
      exact_mod_cast this
    exact one_div_le_one_div_of_le hpow_pos hle
  -- Sum of the constant upper bound over the block equals 1.
  have hconst : ∑ _k ∈ Finset.Ico (2 ^ n : ℕ) (2 ^ (n + 1)), (1 : ℝ) / 2 ^ n = 1 := by
    rw [Finset.sum_const, Nat.card_Ico]
    have hpow : (2 : ℕ) ^ (n + 1) - 2 ^ n = 2 ^ n := by
      have : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
      omega
    rw [hpow, nsmul_eq_mul]
    have hne : (2 : ℝ) ^ n ≠ 0 := by positivity
    push_cast
    field_simp
  calc ∑ k ∈ Finset.Ico (2 ^ n : ℕ) (2 ^ (n + 1)), (1 : ℝ) / (k + 1)
      ≤ ∑ _k ∈ Finset.Ico (2 ^ n : ℕ) (2 ^ (n + 1)), (1 : ℝ) / 2 ^ n :=
        Finset.sum_le_sum hterm
    _ = 1 := hconst

/-- **Dyadic upper bound.** The `2^n`-th partial sum of the harmonic series
satisfies

  `H_{2^n} = ∑_{j=1}^{2^n} 1/j ≤ 1 + n`.

Proof by induction on `n`: the first term contributes `1 = H_{2^0}`, and each of
the next `n` dyadic blocks contributes at most `1` (`block_le_one`). -/
theorem harmonic_two_pow_le (n : ℕ) : H (2 ^ n) ≤ 1 + (n : ℝ) := by
  induction n with
  | zero => simp [H]
  | succ n ih =>
      rw [H_two_pow_succ]
      have hblock := block_le_one n
      push_cast
      have hrw : 1 + ((n : ℝ) + 1) = (1 + (n : ℝ)) + 1 := by ring
      rw [hrw]
      exact add_le_add ih hblock

/-- **Two-sided Oresme sandwich.** Combining the parent's lower bound
`harmonic_two_pow_ge` with the upper bound above, the `2^n`-th harmonic partial
sum is pinned to a window of width `n/2`:

  `1 + n/2 ≤ H_{2^n} ≤ 1 + n`.

This exhibits the logarithmic growth `H_N ~ log N` quantitatively at the dyadic
sampling points `N = 2^n`. -/
theorem harmonic_two_pow_sandwich (n : ℕ) :
    1 + (n : ℝ) / 2 ≤ H (2 ^ n) ∧ H (2 ^ n) ≤ 1 + (n : ℝ) :=
  ⟨harmonic_two_pow_ge n, harmonic_two_pow_le n⟩

/-- **Width of the sandwich.** The lower and upper bounds on `H_{2^n}` differ by
exactly `n/2`, so the dyadic partial sums are localised to an interval of length
`n/2`. -/
theorem harmonic_two_pow_window (n : ℕ) :
    (1 + (n : ℝ)) - (1 + (n : ℝ) / 2) = (n : ℝ) / 2 := by ring

end HarmonicDivergenceOQ05OQ01
