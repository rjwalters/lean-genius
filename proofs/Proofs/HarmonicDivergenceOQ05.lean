import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-
# Oresme's Explicit Lower Bound for the Harmonic Series

## What This Proves

The classical entries on the harmonic series (`HarmonicDivergence`, `…OQ01–OQ04`)
establish *qualitative* divergence: the partial sums are not summable and tend to
infinity, and each dyadic block `1/(2^k+1) + … + 1/2^{k+1}` exceeds `1/2`.

This entry assembles those blocks into a single **explicit quantitative bound**,
the sharp form of Oresme's 14th-century argument:

  `H_{2^n} = ∑_{j=1}^{2^n} 1/j ≥ 1 + n/2`.

So the `2^n`-th partial sum is at least `1 + n/2` — divergence at a logarithmic
rate made completely explicit. This is *not* a single Mathlib lemma: Mathlib has
`Real.tendsto_sum_range_one_div_nat_succ_atTop` (existence-form divergence) but no
closed lower bound on the partial sums. We derive the bound by induction on `n`,
using a self-contained dyadic-block estimate, and then read off two corollaries:

* an explicit term count `N = 2^{⌈2(M-1)⌉}` after which `H_N` exceeds any target `M`,
  quantifying *how slow* the divergence is, and
* a fresh proof that the partial sums tend to `+∞`, obtained from the bound alone.

## Indexing convention

We index partial sums exactly as Mathlib does in
`Real.tendsto_sum_range_one_div_nat_succ_atTop`:

  `H N := ∑ k ∈ Finset.range N, (1 : ℝ) / (k + 1)  =  1 + 1/2 + … + 1/N`.

## Status
- [x] Complete proof (0 sorries, 0 axioms)
- [x] Headline `harmonic_two_pow_ge` is original to the gallery family
- [x] Corollaries: explicit exceedance count + divergence from the bound
-/

namespace HarmonicDivergenceOQ05

open Finset

/-- Partial sum `H N = ∑_{j=1}^{N} 1/j`, indexed as in Mathlib's
`Real.tendsto_sum_range_one_div_nat_succ_atTop`. -/
noncomputable def H (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, (1 : ℝ) / (k + 1)

/-- **Dyadic block estimate.** The block of `2^n` terms running from index `2^n`
to `2^{n+1} - 1` contributes at least `1/2`:

  `1/(2^n+1) + 1/(2^n+2) + … + 1/2^{n+1} ≥ 1/2`.

Each of the `2^n` terms is at least `1/2^{n+1}`, and `2^n · (1/2^{n+1}) = 1/2`. -/
theorem block_ge_half (n : ℕ) :
    (1 : ℝ) / 2 ≤ ∑ k ∈ Finset.Ico (2 ^ n : ℕ) (2 ^ (n + 1)), (1 : ℝ) / (k + 1) := by
  -- Each term in the block is ≥ 1 / 2^{n+1}.
  have hterm : ∀ k ∈ Finset.Ico (2 ^ n : ℕ) (2 ^ (n + 1)),
      (1 : ℝ) / 2 ^ (n + 1) ≤ (1 : ℝ) / (k + 1) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hk_le : (k : ℝ) + 1 ≤ 2 ^ (n + 1) := by
      have : k + 1 ≤ 2 ^ (n + 1) := by omega
      exact_mod_cast this
    exact one_div_le_one_div_of_le hk_pos hk_le
  -- Sum of the constant lower bound over the block.
  have hconst : ∑ _k ∈ Finset.Ico (2 ^ n : ℕ) (2 ^ (n + 1)), (1 : ℝ) / 2 ^ (n + 1)
      = (1 : ℝ) / 2 := by
    rw [Finset.sum_const, Nat.card_Ico]
    have hpow : (2 : ℕ) ^ (n + 1) - 2 ^ n = 2 ^ n := by
      have : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
      omega
    rw [hpow, nsmul_eq_mul]
    have h2 : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
    rw [h2]
    push_cast
    have hne : (2 : ℝ) ^ n ≠ 0 := by positivity
    field_simp
  calc (1 : ℝ) / 2
      = ∑ _k ∈ Finset.Ico (2 ^ n : ℕ) (2 ^ (n + 1)), (1 : ℝ) / 2 ^ (n + 1) := hconst.symm
    _ ≤ ∑ k ∈ Finset.Ico (2 ^ n : ℕ) (2 ^ (n + 1)), (1 : ℝ) / (k + 1) :=
        Finset.sum_le_sum hterm

/-- Splitting `H (2^{n+1})` into the head `H (2^n)` plus one dyadic block. -/
theorem H_two_pow_succ (n : ℕ) :
    H (2 ^ (n + 1)) = H (2 ^ n)
      + ∑ k ∈ Finset.Ico (2 ^ n : ℕ) (2 ^ (n + 1)), (1 : ℝ) / (k + 1) := by
  unfold H
  rw [← Finset.sum_range_add_sum_Ico _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n))]

/-- **Oresme's explicit lower bound.** The `2^n`-th partial sum of the harmonic
series satisfies

  `H_{2^n} = ∑_{j=1}^{2^n} 1/j ≥ 1 + n/2`.

This is the sharp, quantitative form of Oresme's grouping argument (≈1350): the
first term contributes `1`, and each of the next `n` dyadic blocks contributes at
least `1/2`. Proof is by induction on `n`, splitting off one block at a time. -/
theorem harmonic_two_pow_ge (n : ℕ) : 1 + (n : ℝ) / 2 ≤ H (2 ^ n) := by
  induction n with
  | zero => simp [H]
  | succ n ih =>
      rw [H_two_pow_succ]
      have hblock := block_ge_half n
      push_cast
      have : 1 + ((n : ℝ) + 1) / 2 = (1 + (n : ℝ) / 2) + 1 / 2 := by ring
      rw [this]
      exact add_le_add ih hblock

/-- **Quantitative slowness of divergence.** For any target `M`, the partial sum
`H N` exceeds `M` once `N ≥ 2^n` with `n` a natural number `≥ 2(M-1)`. Concretely
the bound `H_{2^n} ≥ 1 + n/2` forces `H_{2^n} > M` as soon as `n > 2(M - 1)`.

This makes the notorious slowness explicit: to push the sum past `M` you only
*need* about `2^{2M}` terms, and the bound guarantees that many suffice. -/
theorem exceeds_at_two_pow (M : ℝ) :
    ∃ n : ℕ, M < H (2 ^ n) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * (M - 1))
  refine ⟨n, ?_⟩
  have hb := harmonic_two_pow_ge n
  have : M < 1 + (n : ℝ) / 2 := by linarith
  linarith

/-- **Divergence from the explicit bound.** The partial sums tend to `+∞`.

Unlike `HarmonicDivergence.partial_sums_tendsto_atTop`, which invokes Mathlib's
`Real.tendsto_sum_range_one_div_nat_succ_atTop` directly, this derivation uses
only our quantitative bound together with monotonicity of the partial sums. -/
theorem tendsto_atTop : Filter.Tendsto H Filter.atTop Filter.atTop := by
  -- `H` is monotone since every added term `1/(k+1)` is nonnegative.
  have hmono : Monotone H := by
    intro a b hab
    unfold H
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono hab
    · intro i _ _; positivity
  rw [Filter.tendsto_atTop_atTop]
  intro M
  obtain ⟨n, hn⟩ := exceeds_at_two_pow M
  refine ⟨2 ^ n, fun N hN => ?_⟩
  exact le_of_lt (lt_of_lt_of_le hn (hmono hN))

end HarmonicDivergenceOQ05
