/-
  Erdős Problem #46 — Monochromatic Unit-Fraction Representations:
  the cost of large minimum denominators (0-axiom).

  Companion to `Erdos46Problem.lean`, which defines `IsUnitFractionRepr S`
  (`∀ n ∈ S, 2 ≤ n` and `∑_{n∈S} 1/n = 1`) and develops a large "construction"
  toolkit — telescoping, divisor-sum, greedy over/undershoot, and the two-sided
  `bracket_one` approximations of `1` by representations whose denominators all
  exceed a prescribed `N`.  Those results attack the *existence* of an exact
  representation of `1` with minimum denominator `> N`.

  This file supplies the complementary **lower bound / obstruction** side, which
  the construction toolkit does not address: it quantifies the unavoidable cost of
  pushing the minimum denominator up.

  * `card_ge_of_forall_gt` — if every denominator of a unit-fraction
    representation of `1` exceeds `N`, then the representation uses at least
    `N + 1` terms.  (Each term is `≤ 1/(N+1)`, and they sum to `1`.)  So the
    "minimum denominator `> N`" goal is genuinely expensive: it forces the
    cardinality to grow at least linearly in `N`.

  * `exists_le_card` — dually, in *any* unit-fraction representation of `1` the
    smallest denominator is at most the number of terms: some `n ∈ S` has
    `n ≤ |S|`.  (Otherwise every denominator would exceed `|S|`, forcing
    `|S| ≥ |S| + 1` by the previous bound.)

  Neither statement is a construction, so neither is equivalent-strength to the
  open target (an exact representation of `1` with arbitrarily large minimum
  denominator); they are necessary conditions constraining any such
  representation.  The deep monochromatic result (Croot 2003) stays unformalized.

  0 axioms, 0 sorries — `#print axioms` = propext / Classical.choice / Quot.sound.
-/

import Mathlib
import Proofs.Erdos46Problem

open Finset

/-- **Large minimum denominator forces many terms.**  If `S` is a unit-fraction
    representation of `1` and every denominator exceeds `N` (`∀ n ∈ S, N < n`),
    then `N + 1 ≤ |S|`.  Each term satisfies `1/n ≤ 1/(N+1)`, so the total
    `∑_{n∈S} 1/n = 1` is at most `|S| · 1/(N+1)`; hence `|S| ≥ N + 1`. -/
theorem card_ge_of_forall_gt {S : Finset ℕ} {N : ℕ}
    (hS : IsUnitFractionRepr S) (hN : ∀ n ∈ S, N < n) : N + 1 ≤ S.card := by
  obtain ⟨_, hsum⟩ := hS
  have hNpos : (0 : ℚ) < (N : ℚ) + 1 := by positivity
  -- every term is bounded by 1/(N+1)
  have hterm : ∀ n ∈ S, (1 : ℚ) / n ≤ 1 / ((N : ℚ) + 1) := by
    intro n hn
    have hle : (N : ℚ) + 1 ≤ (n : ℚ) := by exact_mod_cast hN n hn
    exact one_div_le_one_div_of_le hNpos hle
  -- sum ≤ card • (1/(N+1)); rewrite the sum as 1
  have hbound : S.sum (fun n => (1 : ℚ) / n) ≤ S.card • ((1 : ℚ) / ((N : ℚ) + 1)) :=
    Finset.sum_le_card_nsmul S _ _ hterm
  rw [hsum, nsmul_eq_mul] at hbound
  -- 1 ≤ card * (1/(N+1)); multiply through by (N+1) > 0 and cancel
  have hmul := mul_le_mul_of_nonneg_right hbound (le_of_lt hNpos)
  rw [one_mul, mul_assoc, one_div_mul_cancel (ne_of_gt hNpos), mul_one] at hmul
  -- hmul : (N : ℚ) + 1 ≤ (S.card : ℚ)
  exact_mod_cast hmul

/-- **The smallest denominator never exceeds the number of terms.**  In any
    unit-fraction representation `S` of `1`, some denominator is `≤ |S|`.  If not,
    every denominator would exceed `|S|`, and `card_ge_of_forall_gt` (with
    `N = |S|`) would give `|S| + 1 ≤ |S|` — impossible. -/
theorem exists_le_card {S : Finset ℕ} (hS : IsUnitFractionRepr S) :
    ∃ n ∈ S, n ≤ S.card := by
  by_contra h
  push_neg at h
  -- h : ∀ n ∈ S, S.card < n
  have := card_ge_of_forall_gt hS h
  omega
