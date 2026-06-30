import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-
# Explicit Dyadic-Block Bounds for the `p`-Series Partial Sums

## What This Proves

The parent entry `HarmonicDivergenceOQ05` makes Oresme's grouping argument for the
harmonic series (`p = 1`) completely explicit:

  `H_{2^n} = ∑_{j=1}^{2^n} 1/j ≥ 1 + n/2`.

Here we generalise the **dyadic-block** technique to the full real `p`-series

  `H_p(N) = ∑_{j=1}^{N} 1/j^p`,

and extract *two-sided* explicit bounds on the dyadic partial sums `H_p(2^n)`:

* **Divergent regime `0 < p ≤ 1`.**  Every dyadic block still contributes at least
  `1/2`, so the Oresme bound survives unchanged:

    `H_p(2^n) ≥ 1 + n/2`   (hence `H_p → ∞`).

* **Convergent regime `p > 1`.**  Every dyadic block is now majorised by the
  geometric term `(2^{1-p})^m`, giving a *uniform explicit ceiling*

    `H_p(2^n) ≤ 1 + 1/(1 - 2^{1-p})`   for all `n`,

  so the partial sums are bounded — the quantitative heart of the `p`-series
  convergence test, with an explicit constant.

Mathlib has the qualitative `p`-series dichotomy
(`Real.summable_one_div_nat_rpow`) but no explicit dyadic partial-sum bounds; the
constants `1 + n/2` and `1 + 1/(1 - 2^{1-p})` are original to this gallery family.
The exponent is a genuine real `p`, handled with `Real.rpow`.

## Indexing convention

As in the parent and in `Real.tendsto_sum_range_one_div_nat_succ_atTop`:

  `Hp p N := ∑ k ∈ Finset.range N, (1 : ℝ) / (k + 1) ^ p`   (`^` is `Real.rpow`).

## Status
- [x] Complete proof (0 sorries, 0 axioms)
- [x] Lower bound `Hp_two_pow_ge` (divergence, `p ≤ 1`)
- [x] Upper bound `Hp_two_pow_le` (uniform ceiling, `p > 1`)
-/

namespace HarmonicDivergenceOQ05OQ02

open Finset

/-- `p`-series partial sum `H_p(N) = ∑_{j=1}^{N} 1/j^p`, with a real exponent `p`
handled through `Real.rpow`. Indexed exactly as the parent's harmonic `H`. -/
noncomputable def Hp (p : ℝ) (N : ℕ) : ℝ :=
    ∑ k ∈ Finset.range N, (1 : ℝ) / ((k : ℝ) + 1) ^ p

/-- Splitting `H_p(2^{n+1})` into the head `H_p(2^n)` plus one dyadic block
`∑_{k = 2^n}^{2^{n+1}-1} 1/(k+1)^p`. -/
theorem Hp_two_pow_succ (p : ℝ) (n : ℕ) :
    Hp p (2 ^ (n + 1)) = Hp p (2 ^ n)
      + ∑ k ∈ Finset.Ico (2 ^ n : ℕ) (2 ^ (n + 1)), (1 : ℝ) / ((k : ℝ) + 1) ^ p := by
  unfold Hp
  rw [← Finset.sum_range_add_sum_Ico _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n))]

/-- `H_p` is monotone in the number of terms (each summand `1/(k+1)^p` is `≥ 0`). -/
theorem Hp_mono (p : ℝ) : Monotone (Hp p) := by
  intro a b hab
  unfold Hp
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
  intro i _ _
  positivity

/-! ### Divergent regime `0 < p ≤ 1` -/

/-- **Dyadic block lower bound (`p ≤ 1`).** For `0 < p ≤ 1` each of the `2^n` terms
of the block at level `n` is at least `1/(2^{n+1})^p ≥ 1/2^{n+1}` (raising the base
`2^{n+1} ≥ 1` to the *smaller* exponent `p ≤ 1` can only shrink it), so the whole
block contributes at least `2^n · 1/2^{n+1} = 1/2`. -/
theorem block_ge_half {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (n : ℕ) :
    (1 : ℝ) / 2 ≤
      ∑ k ∈ Finset.Ico (2 ^ n : ℕ) (2 ^ (n + 1)), (1 : ℝ) / ((k : ℝ) + 1) ^ p := by
  have hterm : ∀ k ∈ Finset.Ico (2 ^ n : ℕ) (2 ^ (n + 1)),
      (1 : ℝ) / 2 ^ (n + 1) ≤ (1 : ℝ) / ((k : ℝ) + 1) ^ p := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk_le : (k : ℝ) + 1 ≤ (2 : ℝ) ^ (n + 1) := by
      have : k + 1 ≤ 2 ^ (n + 1) := by omega
      exact_mod_cast this
    have hbase1 : (1 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
    have step1 : ((k : ℝ) + 1) ^ p ≤ ((2 : ℝ) ^ (n + 1)) ^ p :=
      Real.rpow_le_rpow (by positivity) hk_le hp0.le
    have step2 : ((2 : ℝ) ^ (n + 1)) ^ p ≤ ((2 : ℝ) ^ (n + 1)) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase1 hp1
    rw [Real.rpow_one] at step2
    have hkp_pos : (0 : ℝ) < ((k : ℝ) + 1) ^ p := Real.rpow_pos_of_pos (by positivity) _
    exact one_div_le_one_div_of_le hkp_pos (le_trans step1 step2)
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
    _ ≤ ∑ k ∈ Finset.Ico (2 ^ n : ℕ) (2 ^ (n + 1)), (1 : ℝ) / ((k : ℝ) + 1) ^ p :=
        Finset.sum_le_sum hterm

/-- **Generalised Oresme lower bound (`0 < p ≤ 1`).** The `2^n`-th partial sum of the
`p`-series satisfies `H_p(2^n) ≥ 1 + n/2`. So for `p ≤ 1` the `p`-series diverges at
least as fast as the harmonic series — the parent bound (`p = 1`) as the boundary case. -/
theorem Hp_two_pow_ge {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (n : ℕ) :
    1 + (n : ℝ) / 2 ≤ Hp p (2 ^ n) := by
  induction n with
  | zero => simp [Hp, Real.one_rpow]
  | succ n ih =>
      rw [Hp_two_pow_succ]
      have hblock := block_ge_half hp0 hp1 n
      push_cast
      have hsplit : 1 + ((n : ℝ) + 1) / 2 = (1 + (n : ℝ) / 2) + 1 / 2 := by ring
      rw [hsplit]
      exact add_le_add ih hblock

/-- **Divergence in the regime `0 < p ≤ 1`.** For any target `M` some dyadic partial
sum exceeds it. -/
theorem Hp_exceeds {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (M : ℝ) :
    ∃ n : ℕ, M < Hp p (2 ^ n) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * (M - 1))
  refine ⟨n, ?_⟩
  have hb := Hp_two_pow_ge hp0 hp1 n
  have : M < 1 + (n : ℝ) / 2 := by linarith
  linarith

/-- **Divergence of the `p`-series partial sums for `0 < p ≤ 1`.** -/
theorem Hp_tendsto_atTop {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Filter.Tendsto (Hp p) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro M
  obtain ⟨n, hn⟩ := Hp_exceeds hp0 hp1 M
  exact ⟨2 ^ n, fun N hN => le_of_lt (lt_of_lt_of_le hn (Hp_mono p hN))⟩

/-! ### Convergent regime `p > 1` -/

/-- The algebraic core of the geometric majorisation: `2^n / (2^n)^p = (2^{1-p})^n`. -/
private lemma two_pow_div_rpow (p : ℝ) (n : ℕ) :
    (2 : ℝ) ^ n / ((2 : ℝ) ^ n) ^ p = ((2 : ℝ) ^ (1 - p)) ^ n := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (1 - p)) n, ← Real.rpow_natCast (2 : ℝ) n,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- **Dyadic block geometric upper bound (`p ≥ 0`).** Each of the `2^n` terms of the
block at level `n` is at most `1/(2^n)^p` (the base `k+1 ≥ 2^n` raised to `p ≥ 0`),
so the block is `≤ 2^n / (2^n)^p = (2^{1-p})^n`. For `p > 1` the ratio `2^{1-p} < 1`
makes this a convergent geometric majorant. -/
theorem block_le_geom {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    ∑ k ∈ Finset.Ico (2 ^ n : ℕ) (2 ^ (n + 1)), (1 : ℝ) / ((k : ℝ) + 1) ^ p
      ≤ ((2 : ℝ) ^ (1 - p)) ^ n := by
  have hterm : ∀ k ∈ Finset.Ico (2 ^ n : ℕ) (2 ^ (n + 1)),
      (1 : ℝ) / ((k : ℝ) + 1) ^ p ≤ (1 : ℝ) / ((2 : ℝ) ^ n) ^ p := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have h2n_le : (2 : ℝ) ^ n ≤ (k : ℝ) + 1 := by
      have hnat : (2 : ℕ) ^ n ≤ k + 1 := by omega
      calc (2 : ℝ) ^ n = (((2 : ℕ) ^ n : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = (k : ℝ) + 1 := by push_cast; ring
    have hbpos : (0 : ℝ) < ((2 : ℝ) ^ n) ^ p := Real.rpow_pos_of_pos (by positivity) _
    have hmono : ((2 : ℝ) ^ n) ^ p ≤ ((k : ℝ) + 1) ^ p :=
      Real.rpow_le_rpow (by positivity) h2n_le hp
    exact one_div_le_one_div_of_le hbpos hmono
  have hconst : ∑ _k ∈ Finset.Ico (2 ^ n : ℕ) (2 ^ (n + 1)), (1 : ℝ) / ((2 : ℝ) ^ n) ^ p
      = ((2 : ℝ) ^ (1 - p)) ^ n := by
    rw [Finset.sum_const, Nat.card_Ico]
    have hpow : (2 : ℕ) ^ (n + 1) - 2 ^ n = 2 ^ n := by
      have : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
      omega
    rw [hpow, nsmul_eq_mul]
    rw [← two_pow_div_rpow p n]
    push_cast
    have hbpos : (0 : ℝ) < ((2 : ℝ) ^ n) ^ p := Real.rpow_pos_of_pos (by positivity) _
    field_simp
  calc ∑ k ∈ Finset.Ico (2 ^ n : ℕ) (2 ^ (n + 1)), (1 : ℝ) / ((k : ℝ) + 1) ^ p
      ≤ ∑ _k ∈ Finset.Ico (2 ^ n : ℕ) (2 ^ (n + 1)), (1 : ℝ) / ((2 : ℝ) ^ n) ^ p :=
        Finset.sum_le_sum hterm
    _ = ((2 : ℝ) ^ (1 - p)) ^ n := hconst

/-- Closed bound for a finite geometric sum with ratio `0 ≤ r < 1`:
`∑_{i<n} r^i ≤ 1/(1-r)`. -/
private lemma geom_partial_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, r ^ i ≤ 1 / (1 - r) := by
  have hmul : (∑ i ∈ Finset.range n, r ^ i) * (1 - r) = 1 - r ^ n := by
    have h := geom_sum_mul r n
    linear_combination -h
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - r), hmul]
  have : (0 : ℝ) ≤ r ^ n := by positivity
  linarith

/-- **Uniform explicit ceiling for the convergent `p`-series (`p > 1`).**
For every `n`,

  `H_p(2^n) ≤ 1 + 1/(1 - 2^{1-p})`.

The dyadic partial sums are bounded by a constant independent of `n`: the head term
`1` plus the geometric majorant of the blocks, ratio `2^{1-p} < 1`. This is the
quantitative content of `p`-series convergence with an explicit bound. -/
theorem Hp_two_pow_le {p : ℝ} (hp : 1 < p) (n : ℕ) :
    Hp p (2 ^ n) ≤ 1 + 1 / (1 - (2 : ℝ) ^ (1 - p)) := by
  set r : ℝ := (2 : ℝ) ^ (1 - p) with hr
  have hr0 : 0 ≤ r := le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hstep : Hp p (2 ^ n) ≤ 1 + ∑ i ∈ Finset.range n, r ^ i := by
    induction n with
    | zero => simp [Hp, Real.one_rpow]
    | succ n ih =>
        rw [Hp_two_pow_succ, Finset.sum_range_succ]
        have hblock : ∑ k ∈ Finset.Ico (2 ^ n : ℕ) (2 ^ (n + 1)),
            (1 : ℝ) / ((k : ℝ) + 1) ^ p ≤ r ^ n := by
          rw [hr]; exact block_le_geom (le_of_lt (lt_trans one_pos hp)) n
        linarith [ih, hblock]
  have hgeo : ∑ i ∈ Finset.range n, r ^ i ≤ 1 / (1 - r) := geom_partial_le hr0 hr1 n
  linarith [hstep, hgeo]

/-- **Bounded partial sums for `p > 1`.** Every partial sum `H_p N` is `≤` the
uniform ceiling, so the increasing sequence of partial sums is bounded above — the
boundedness underlying convergence of the `p`-series. -/
theorem Hp_bddAbove {p : ℝ} (hp : 1 < p) (N : ℕ) :
    Hp p N ≤ 1 + 1 / (1 - (2 : ℝ) ^ (1 - p)) := by
  have hN : N ≤ 2 ^ N := Nat.le_of_lt (Nat.lt_two_pow_self)
  exact le_trans (Hp_mono p hN) (Hp_two_pow_le hp N)

end HarmonicDivergenceOQ05OQ02
