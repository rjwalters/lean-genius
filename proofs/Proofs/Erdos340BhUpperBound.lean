/-
# Erdős Problem #340 (oq-05 follow-up): the analytic `O(N^{1/h})` upper bound for `B_h` sets

The companion file `Erdos340GreedySidonOQ05.lean` establishes two complementary facts about
`B_h` subsets `A ⊆ {1, …, N}` (a `B_h` set is one whose `h`-fold sumsets are as distinct as
possible — `IsBh h A`):

* the **greedy lower bound** `exists_isBh_rpow_lower`: the bounded greedy algorithm produces
  such a set with `|A| ≥ C₁ · N^{1/(2h-1)}`;
* the **combinatorial counting bound** `IsBh.choose_card_le`: `C(|A|, h) ≤ h · N`, because the
  `C(|A|, h)` many `h`-element subset-sums are distinct and confined to `[1, h·N]`.

What was missing is the *analytic* form of the second one — the matching **upper bound**
`|A| ≤ C₂ · N^{1/h}` that the literature states alongside the lower bound.  This file supplies
it as a fully verified, `0`-axiom theorem (`IsBh.card_le_rpow`), with the explicit constant
`C₂ = (h - 1) + (h · h!)^{1/h}`.

Together with `exists_isBh_rpow_lower`, this brackets the maximal size `σ_h(N)` of a `B_h` set
inside `[1, N]`:

  `C₁ · N^{1/(2h-1)} ≤ σ_h(N) ≤ C₂ · N^{1/h}`.

The gap between the exponents `1/(2h-1)` and `1/h` is *exactly* the open quantitative content
of Erdős #340 for general `h`.  (For `h = 2` this is `1/3` vs `1/2` — the classical Sidon gap;
whether the greedy `1/3` exponent can be improved toward the counting `1/2` upper bound is the
unsolved problem, and is **not** addressed here.)

## The argument

`IsBh.choose_card_le` gives `C(k, h) ≤ h · N` with `k = |A|`.  Mathlib's binomial lower bound
`Nat.pow_le_choose` gives the reverse `(k + 1 - h)^h / h! ≤ C(k, h)`, so combining,

  `(k + 1 - h)^h ≤ h! · h · N`.

Taking `h`-th roots (`rpow (1/h)`, monotone on `[0, ∞)`),

  `k + 1 - h ≤ (h! · h)^{1/h} · N^{1/h}`,

and the elementary `ℕ` inequality `k ≤ (k + 1 - h) + (h - 1)` (valid even when `k < h`, where
the truncated subtraction is `0`) lets us absorb the additive `h - 1` into `(h - 1) · N^{1/h}`
using `N^{1/h} ≥ 1`, yielding `k ≤ C₂ · N^{1/h}`.
-/
import Proofs.Erdos340GreedySidonOQ05

namespace Erdos340Bh

open Finset
open scoped Nat

/-- **Analytic `O(N^{1/h})` upper bound for `B_h` sets** — companion to the greedy lower bound
`exists_isBh_rpow_lower`.

There is an explicit constant `C > 0` (depending only on `h`) such that every `B_h` set
`A ⊆ {1, …, N}` satisfies

  `|A| ≤ C · N^{1/h}`.

The constant is `C = (h - 1) + (h · h!)^{1/h}`.  Proved `0`-axiom from the combinatorial
counting bound `IsBh.choose_card_le` (`C(|A|, h) ≤ h·N`) and Mathlib's binomial lower bound
`Nat.pow_le_choose`.

Paired with `exists_isBh_rpow_lower` (an achievable `|A| ≥ C' · N^{1/(2h-1)}`), this brackets
the maximal `B_h` size in `[1, N]`; the exponent gap `1/(2h-1)` vs `1/h` is the open core of
Erdős #340. -/
theorem IsBh.card_le_rpow {h : ℕ} (hh : 1 ≤ h) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 N → IsBh h A →
      (A.card : ℝ) ≤ C * (N : ℝ) ^ ((h : ℝ)⁻¹) := by
  have hh0 : (h : ℕ) ≠ 0 := by omega
  have hexp_ne : ((h : ℝ)⁻¹) ≠ 0 := by
    have : (0 : ℝ) < (h : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hh0
    positivity
  -- The constant `C₂coef = (h · h!)^{1/h}`, depending only on `h`.
  set C₂coef : ℝ := (((h ! * h : ℕ) : ℝ)) ^ ((h : ℝ)⁻¹) with hC2
  have hcoefbase_pos : (0 : ℝ) < ((h ! * h : ℕ) : ℝ) := by
    have : 0 < h ! * h := Nat.mul_pos (Nat.factorial_pos h) (by omega)
    exact_mod_cast this
  have hC2pos : 0 < C₂coef := by rw [hC2]; exact Real.rpow_pos_of_pos hcoefbase_pos _
  have hh1R : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  refine ⟨((h : ℝ) - 1) + C₂coef, by linarith [hC2pos], ?_⟩
  intro N A hAN hA
  rcases Nat.eq_zero_or_pos N with hN0 | hN1
  · -- `N = 0`: then `A ⊆ Icc 1 0 = ∅`, so `|A| = 0`, and the RHS is `C · 0^{1/h} = 0`.
    subst hN0
    have hAe : A = ∅ := by
      rw [Finset.Icc_eq_empty (by omega)] at hAN
      exact Finset.subset_empty.mp hAN
    simp [hAe, Real.zero_rpow hexp_ne]
  -- Main case `N ≥ 1`.
  have hcc : Nat.choose A.card h ≤ h * N := hA.choose_card_le hh hAN
  set k : ℕ := A.card with hk
  -- Mathlib's binomial lower bound, over `ℝ`.
  have hpc : ((k + 1 - h : ℕ) : ℝ) ^ h / (h ! : ℝ) ≤ (Nat.choose k h : ℝ) :=
    Nat.pow_le_choose (α := ℝ) h k
  have hfp : (0 : ℝ) < (h ! : ℝ) := by exact_mod_cast Nat.factorial_pos h
  -- `(k+1-h)^h ≤ h! · choose k h`.
  have hqh_le_choose : ((k + 1 - h : ℕ) : ℝ) ^ h ≤ (h ! : ℝ) * (Nat.choose k h : ℝ) := by
    rw [div_le_iff₀ hfp] at hpc; linarith [hpc]
  have hccR : (Nat.choose k h : ℝ) ≤ (h : ℝ) * (N : ℝ) := by exact_mod_cast hcc
  -- `(k+1-h)^h ≤ h! · (h · N)`.
  have hqh_le : ((k + 1 - h : ℕ) : ℝ) ^ h ≤ (h ! : ℝ) * ((h : ℝ) * (N : ℝ)) :=
    le_trans hqh_le_choose (mul_le_mul_of_nonneg_left hccR (le_of_lt hfp))
  -- Take `h`-th roots.
  set q : ℝ := ((k + 1 - h : ℕ) : ℝ) with hqdef
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  set Nexp : ℝ := (N : ℝ) ^ ((h : ℝ)⁻¹) with hNexpdef
  have hbase_eq : (h ! : ℝ) * ((h : ℝ) * (N : ℝ)) = ((h ! * h : ℕ) : ℝ) * (N : ℝ) := by
    push_cast; ring
  have hroot : q ≤ C₂coef * Nexp := by
    have hstep : q ≤ ((h ! : ℝ) * ((h : ℝ) * (N : ℝ))) ^ ((h : ℝ)⁻¹) := by
      calc q = (q ^ h) ^ ((h : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hq0 hh0).symm
        _ ≤ ((h ! : ℝ) * ((h : ℝ) * (N : ℝ))) ^ ((h : ℝ)⁻¹) :=
            Real.rpow_le_rpow (by positivity) hqh_le (by positivity)
    rw [hbase_eq, Real.mul_rpow (by positivity) (by positivity)] at hstep
    rw [hC2, hNexpdef]; exact hstep
  -- `k ≤ (k+1-h) + (h-1)` in `ℕ`, transported to `ℝ`.
  have hk_nat : k ≤ (k + 1 - h) + (h - 1) := by omega
  have hcast_h1 : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by
    rw [Nat.cast_sub hh, Nat.cast_one]
  have hk_real : (k : ℝ) ≤ q + ((h : ℝ) - 1) := by
    have h0 : (k : ℝ) ≤ ((k + 1 - h : ℕ) : ℝ) + ((h - 1 : ℕ) : ℝ) := by exact_mod_cast hk_nat
    rw [hcast_h1] at h0; rw [hqdef]; exact h0
  -- `N^{1/h} ≥ 1`, so the additive `h-1` is absorbed.
  have hNexp_ge1 : (1 : ℝ) ≤ Nexp := by
    rw [hNexpdef]
    calc (1 : ℝ) = (1 : ℝ) ^ ((h : ℝ)⁻¹) := (Real.one_rpow _).symm
      _ ≤ (N : ℝ) ^ ((h : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hN1) (by positivity)
  have habs : ((h : ℝ) - 1) ≤ ((h : ℝ) - 1) * Nexp :=
    le_mul_of_one_le_right (by
      have : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
      linarith) hNexp_ge1
  have hexpand : (((h : ℝ) - 1) + C₂coef) * Nexp = ((h : ℝ) - 1) * Nexp + C₂coef * Nexp := by
    ring
  rw [hexpand]
  linarith [hk_real, hroot, habs]

end Erdos340Bh
