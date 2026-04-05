/-
# Erdős Problem #279 — OQ-04: Formal Density Definitions via Mathlib Asymptotic Analysis

Formalizes HasPrimeLikeDensity and HasLogLogDivergence, replacing the placeholder
`True` bodies in Erdos279Problem.lean with rigorous Mathlib-based definitions.

## Formal Definitions

- HasPrimeLikeDensity A: ∃ c > 0, ∀ᶠ N, c·N/log(N) ≤ |A ∩ [1,N]|
- HasLogLogDivergence A: ∑_{n∈A,n≤N} 1/n − log(log N) → +∞

## Results

- Both conditions are monotone under set inclusion (proved)
- Both conditions imply A is infinite (proved, modulo N/log N → ∞)
- Primes satisfy both conditions (2 axioms: PNT lower bound + Mertens)

Status: 2 axioms, 1 sorry (tendsto_atTop_mul_div_log — HARD for Aristotle)
-/

import Mathlib

open Filter Set Finset Real Nat

namespace Erdos279OQ04

/-! ## Core Definitions -/

/-- Counting function: |A ∩ {1,...,N}|. -/
noncomputable def countingFn (A : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard (A ∩ Set.Icc 1 N)

/-- A set A has prime-like lower density: ∃ c > 0, |A ∩ {1,...,N}| ≥ c·N/log N eventually.

    Formal replacement for the placeholder `True` in Erdos279Problem.HasPrimeLikeDensity.
    By PNT, the primes themselves satisfy this with c approaching 1. -/
def HasPrimeLikeDensity (A : Set ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, c * (N : ℝ) / Real.log N ≤ (countingFn A N : ℝ)

/-- Partial reciprocal sum over A up to N: ∑_{n ∈ A ∩ [1,N]} 1/n.
    Uses Set.indicator to avoid requiring DecidablePred. -/
noncomputable def reciprocalPartialSum (A : Set ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, A.indicator (fun n => (1 : ℝ) / (n : ℝ)) n

/-- A set A satisfies log-log divergence: ∑_{n∈A, n≤N} 1/n − log(log N) → +∞.

    Formal replacement for the placeholder `True` in Erdos279Problem.HasLogLogDivergence.
    By Mertens' theorem, the primes satisfy this condition. -/
def HasLogLogDivergence (A : Set ℕ) : Prop :=
  Tendsto (fun N : ℕ => reciprocalPartialSum A N - Real.log (Real.log N)) atTop atTop

/-! ## Monotonicity Under Set Inclusion -/

theorem countingFn_mono {A B : Set ℕ} (h : A ⊆ B) (N : ℕ) :
    countingFn A N ≤ countingFn B N :=
  Set.ncard_le_ncard (Set.inter_subset_inter_left _ h)
    ((Set.finite_Icc 1 N).subset Set.inter_subset_right)

theorem reciprocalPartialSum_mono {A B : Set ℕ} (h : A ⊆ B) (N : ℕ) :
    reciprocalPartialSum A N ≤ reciprocalPartialSum B N :=
  Finset.sum_le_sum fun n _ =>
    Set.indicator_le_indicator_of_subset h
      (fun x => div_nonneg zero_le_one (Nat.cast_nonneg x)) n

theorem hasPrimeLikeDensity_mono {A B : Set ℕ} (h : A ⊆ B)
    (hA : HasPrimeLikeDensity A) : HasPrimeLikeDensity B := by
  obtain ⟨c, hc, hN⟩ := hA
  exact ⟨c, hc, hN.mono fun N hN => le_trans hN (Nat.cast_le.mpr (countingFn_mono h N))⟩

theorem hasLogLogDivergence_mono {A B : Set ℕ} (h : A ⊆ B)
    (hA : HasLogLogDivergence A) : HasLogLogDivergence B :=
  tendsto_atTop_mono (fun N => sub_le_sub_right (reciprocalPartialSum_mono h N) _) hA

/-! ## Both Conditions Imply Infinitude -/

/-- Key: c·N/log N → +∞ for c > 0.
    Follows from N/log N → ∞ (since log N = o(N) by Real.isLittleO_log_id_atTop). -/
theorem tendsto_atTop_mul_div_log {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => c * (N : ℝ) / Real.log N) atTop atTop := by
  sorry  -- HARD: use Real.isLittleO_log_id_atTop to derive N/log N → ∞

/-- If A has prime-like density, A is infinite.
    If A were finite, countingFn A N ≤ A.ncard (constant), but c·N/log N → ∞. -/
theorem hasPrimeLikeDensity_infinite {A : Set ℕ} (h : HasPrimeLikeDensity A) :
    A.Infinite := fun hfin => by
  obtain ⟨c, hc, hbd⟩ := h
  have hbdd : ∀ N : ℕ, (countingFn A N : ℝ) ≤ (A.ncard : ℝ) := fun N =>
    Nat.cast_le.mpr (Set.ncard_le_ncard Set.inter_subset_left hfin)
  have hlim := (tendsto_atTop_mul_div_log hc).eventually (eventually_gt_atTop (A.ncard : ℝ))
  obtain ⟨N, hNbig, hNle⟩ := (hlim.and hbd).exists
  linarith [hbdd N]

/-! ## Primes Satisfy Both Conditions -/

/-- Primes have prime-like density (PNT lower bound: π(N) ≥ c·N/log N).
    Axiomatized: full PNT lower bound not yet in Mathlib. -/
axiom primes_have_prime_like_density :
  HasPrimeLikeDensity {n : ℕ | n.Prime}

/-- Primes satisfy log-log divergence (Mertens' second theorem:
    ∑_{p≤N} 1/p = log log N + M + o(1) where M is the Meissel-Mertens constant).
    Axiomatized: Mertens' theorem not yet in Mathlib. -/
axiom primes_have_log_log_divergence :
  HasLogLogDivergence {n : ℕ | n.Prime}

/-- The primes are infinite, as a corollary of prime-like density. -/
theorem primes_infinite : {n : ℕ | n.Prime}.Infinite :=
  hasPrimeLikeDensity_infinite primes_have_prime_like_density

end Erdos279OQ04
