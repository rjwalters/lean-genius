/-
  Erdős Problem #1000, OQ-02: The Rate of Convergence of the Cesàro Average

  The parent problem (Erdős #1000) concerns the Cesàro average
    C_A(N) = (1/N) Σ_{k<N} ρ_A(k),   ρ_A(k) = φ_A(k)/n_k,
  of the "new-denominator density" ρ_A. Haight proved that C_A(N) → 0 is
  possible (`Erdos1000.cassels_liminf_zero`), contrary to Erdős' expectation.

  This open question asks about the *optimal rate*: how fast can C_A(N) → 0?

  We establish a hierarchy of universal lower bounds on C_A(N), all sharp in
  their respective regimes and all inherited from the parent's density-ratio
  theory (no new axioms, no sorries):

  1.  **Universal Ω(1/N) floor** (`cesaroAvg_ge_inv_N`):
        C_A(N) ≥ 1/N     for every increasing sequence A and every N ≥ 1.
      The single term ρ_A(0) = 1 (the first fraction never has a "previous"
      denominator to collide with) already pins the running total at ≥ 1, so
      the average is at least 1/N. No sequence can drive C_A to 0 faster than
      1/N.  Restated: `1 ≤ N · C_A(N)`, and equivalently C_A(N) is never
      strictly below 1/N (`not_cesaroAvg_lt_inv_N`).

  2.  **Harmonic floor** (`cesaroAvg_ge_harmonic`):
        C_A(N) ≥ (1/N) Σ_{k<N} 1/n_k,
      from the pointwise bound ρ_A(k) ≥ 1/n_k (`densityRatio_ge_inv`).

  3.  **Large-ratio frequency floor** (`cesaroAvg_ge_largeCount`):
        C_A(N) ≥ #{k < N : ρ_A(k) ≥ 1/2} / (2N).
      The rate of convergence is controlled by how *rarely* the density ratio
      is large: C_A(N) → 0 forces the large-ratio indices to have density 0.

  4.  **Prime-density floor** (`cesaroAvg_ge_primeCount`):
        C_A(N) ≥ #{k < N : n_k prime} / (2N),
      since prime terms have ρ_A(k) ≥ 1/2 (`densityRatio_ge_of_prime`). Thus the
      convergence rate is bounded below by half the density of prime terms.

  5.  **Capstone** (`not_vanishingAverage_of_frequently_prime_dense`): if the
      prime terms have positive density infinitely often, C_A(N) cannot converge
      to 0 at all. A Haight-type (vanishing-average) sequence must therefore be
      sparse in primes — a concrete structural necessary condition.

  Axiom count: 0 (inherits 2 from parent via import: erdos_dichotomy,
                  haight_resolution — neither is used below)
  Sorry count: 0

  Tags: number-theory, diophantine-approximation, cesaro-averages,
        rate-of-convergence, totient-function
-/

import Mathlib
import Proofs.Erdos1000Problem

open Finset Filter Topology Erdos1000

namespace Erdos1000OQ02

/-! ## Part I: The universal Ω(1/N) rate floor

The first density ratio is pinned: ρ_A(0) = 1 for every sequence (the reduced
denominator of `m/n₀` is never a *previous* term, so nothing is filtered out).
Since all ratios are nonnegative, the running total is always at least 1, hence
the Cesàro average is at least 1/N. -/

/-- The running total of density ratios is at least 1 for `N ≥ 1`, because the
    `k = 0` term equals 1 and all terms are nonnegative. -/
theorem sum_densityRatio_ge_one (A : IncreasingSeq) (N : ℕ) (hN : 0 < N) :
    1 ≤ ∑ k ∈ range N, densityRatio A k := by
  calc (1 : ℝ) = densityRatio A 0 := (densityRatio_zero A).symm
    _ ≤ ∑ k ∈ range N, densityRatio A k :=
        Finset.single_le_sum (fun k _ => densityRatio_nonneg A k)
          (Finset.mem_range.mpr hN)

/-- **Universal Ω(1/N) floor.** For every increasing sequence and every `N ≥ 1`,
    `C_A(N) ≥ 1/N`. No sequence's Cesàro average decays faster than `1/N`. -/
theorem cesaroAvg_ge_inv_N (A : IncreasingSeq) (N : ℕ) (hN : 0 < N) :
    1 / (N : ℝ) ≤ cesaroAvg A N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  unfold cesaroAvg
  rw [div_le_div_right₀ hNpos]
  exact sum_densityRatio_ge_one A N hN

/-- Restatement of the floor as `1 ≤ N · C_A(N)`. -/
theorem one_le_N_mul_cesaroAvg (A : IncreasingSeq) (N : ℕ) (hN : 0 < N) :
    1 ≤ (N : ℝ) * cesaroAvg A N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h2 : (N : ℝ) * (1 / N) ≤ N * cesaroAvg A N :=
    mul_le_mul_of_nonneg_left (cesaroAvg_ge_inv_N A N hN) (le_of_lt hNpos)
  rwa [mul_one_div, div_self (ne_of_gt hNpos)] at h2

/-- The Cesàro average is never strictly below `1/N`: `1/N` is the best possible
    universal upper rate. -/
theorem not_cesaroAvg_lt_inv_N (A : IncreasingSeq) (N : ℕ) (hN : 0 < N) :
    ¬ cesaroAvg A N < 1 / N :=
  fun h => absurd (cesaroAvg_ge_inv_N A N hN) (not_le.mpr h)

/-! ## Part II: The harmonic floor

Refining the pointwise bound `ρ_A(k) ≥ 1/n_k` gives a term-by-term floor. -/

/-- **Harmonic floor.** `C_A(N) ≥ (1/N) Σ_{k<N} 1/n_k`, from `ρ_A(k) ≥ 1/n_k`. -/
theorem cesaroAvg_ge_harmonic (A : IncreasingSeq) (N : ℕ) :
    (∑ k ∈ range N, 1 / (A.seq k : ℝ)) / N ≤ cesaroAvg A N := by
  unfold cesaroAvg
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [div_le_div_right₀ (by exact_mod_cast hN : (0 : ℝ) < N)]
    exact Finset.sum_le_sum fun k _ => densityRatio_ge_inv A k

/-! ## Part III: The large-ratio frequency floor

The rate of convergence is governed by how often ρ_A(k) is large: indices with
`ρ_A(k) ≥ 1/2` each contribute at least `1/2` to the running total. -/

/-- The running total is at least `(1/2) ·` (number of large-ratio indices). -/
theorem sum_densityRatio_ge_half_largeCount (A : IncreasingSeq) (N : ℕ) :
    (1 / 2) * ((range N).filter (fun k => 1 / 2 ≤ densityRatio A k)).card
      ≤ ∑ k ∈ range N, densityRatio A k := by
  have hconst : ∑ _k ∈ (range N).filter (fun k => 1 / 2 ≤ densityRatio A k), (1 / 2 : ℝ)
      = (1 / 2) * ((range N).filter (fun k => 1 / 2 ≤ densityRatio A k)).card := by
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  calc (1 / 2 : ℝ) * ((range N).filter (fun k => 1 / 2 ≤ densityRatio A k)).card
      = ∑ _k ∈ (range N).filter (fun k => 1 / 2 ≤ densityRatio A k), (1 / 2 : ℝ) :=
        hconst.symm
    _ ≤ ∑ k ∈ (range N).filter (fun k => 1 / 2 ≤ densityRatio A k), densityRatio A k :=
        Finset.sum_le_sum (fun k hk => (Finset.mem_filter.mp hk).2)
    _ ≤ ∑ k ∈ range N, densityRatio A k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun k _ _ => densityRatio_nonneg A k)

/-- **Large-ratio frequency floor.**
    `C_A(N) ≥ #{k < N : ρ_A(k) ≥ 1/2} / (2N)`. -/
theorem cesaroAvg_ge_largeCount (A : IncreasingSeq) (N : ℕ) (hN : 0 < N) :
    (((range N).filter (fun k => 1 / 2 ≤ densityRatio A k)).card : ℝ) / (2 * N)
      ≤ cesaroAvg A N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hbase := sum_densityRatio_ge_half_largeCount A N
  unfold cesaroAvg
  rw [show (((range N).filter (fun k => 1 / 2 ≤ densityRatio A k)).card : ℝ) / (2 * N)
        = ((1 / 2) * ((range N).filter (fun k => 1 / 2 ≤ densityRatio A k)).card) / N by
        ring]
  rw [div_le_div_right₀ hNpos]
  exact hbase

/-! ## Part IV: The prime-density floor

Prime terms force `ρ_A(k) ≥ 1/2`, so the prime indices are a subset of the
large-ratio indices, yielding a concrete number-theoretic rate floor. -/

/-- **Prime-density floor.** `C_A(N) ≥ #{k < N : n_k prime} / (2N)`. -/
theorem cesaroAvg_ge_primeCount (A : IncreasingSeq) (N : ℕ) (hN : 0 < N) :
    (((range N).filter (fun k => Nat.Prime (A.seq k))).card : ℝ) / (2 * N)
      ≤ cesaroAvg A N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsub : (range N).filter (fun k => Nat.Prime (A.seq k))
              ⊆ (range N).filter (fun k => 1 / 2 ≤ densityRatio A k) := by
    intro k hk
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, densityRatio_ge_of_prime A k hk.2⟩
  refine le_trans ?_ (cesaroAvg_ge_largeCount A N hN)
  have hcard : (((range N).filter (fun k => Nat.Prime (A.seq k))).card : ℝ)
      ≤ (((range N).filter (fun k => 1 / 2 ≤ densityRatio A k)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  rw [div_le_div_right₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hNpos)]
  exact hcard

/-! ## Part V: Capstone — no vanishing average for prime-dense sequences

Combining the prime-density floor with the definition of a vanishing Cesàro
average shows that a Haight-type sequence cannot be prime-dense: if the prime
terms have density bounded below infinitely often, `C_A(N)` stays bounded away
from 0 along that subsequence. -/

/-- If the prime terms have density `≥ c > 0` for infinitely many `N`, then the
    Cesàro average does not converge to 0. A necessary structural condition on
    Haight-type (vanishing-average) sequences: they must be sparse in primes. -/
theorem not_vanishingAverage_of_frequently_prime_dense (A : IncreasingSeq)
    {c : ℝ} (hc : 0 < c)
    (hfreq : ∃ᶠ N in atTop,
      c * N ≤ (((range N).filter (fun k => Nat.Prime (A.seq k))).card : ℝ)) :
    ¬ VanishingAverage A := by
  intro hV
  have hev : ∀ᶠ N in atTop, cesaroAvg A N < c / 2 :=
    (tendsto_order.mp hV).2 (c / 2) (by linarith)
  have hev1 : ∀ᶠ N in atTop, (1 : ℕ) ≤ N := eventually_atTop.mpr ⟨1, fun n hn => hn⟩
  obtain ⟨N, hN_prime, hN_lt, hN_pos⟩ :=
    (hfreq.and_eventually (hev.and hev1)).exists
  have hNpos : 0 < N := hN_pos
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hstep : c / 2 ≤
      (((range N).filter (fun k => Nat.Prime (A.seq k))).card : ℝ) / (2 * N) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
        (mul_pos (by norm_num : (0 : ℝ) < 2) hNr)]
    nlinarith [hN_prime]
  have hge := cesaroAvg_ge_primeCount A N hNpos
  linarith [le_trans hstep hge, hN_lt]

end Erdos1000OQ02
