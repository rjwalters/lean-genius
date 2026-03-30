/-
  Erdős Problem #1000, OQ-01: Explicit Haight-type Sequences

  The parent problem (Erdős #1000) asks whether there exists A = {n₁ < n₂ < ...}
  with (1/N)Σ φ_A(k)/n_k → 0. Haight showed YES (axiom haight_resolution).

  This open question investigates explicit constructions:
  - Which natural candidate sequences FAIL to be Haight-type?
  - What structural properties must a Haight sequence have?
  - Can we characterize the growth rate / divisibility pattern needed?

  Key results:
  1. Factorial sequence: ρ → 1 (NOT Haight-type). Growth too fast.
  2. haight_density_one_low: for vanishing average, ρ < ε on density-1 indices
  3. haight_polynomial_growth: at low-density indices, growth ≤ O(k)

  Axiom count: 0 (inherits 2 from parent via import)
  Sorry count: 2 (factorialSeq_usedSum_le, sum_factorials_lt)

  Tags: number-theory, diophantine-approximation, explicit-construction
-/

import Mathlib
import Proofs.Erdos1000Problem

open Finset Filter Topology Erdos1000

namespace Erdos1000OQ01

/-! ## Part I: The Factorial Sequence -/

/-- The factorial sequence: n_k = (k+1)!. -/
def factorialSeq : IncreasingSeq where
  seq := fun k => (k + 1).factorial
  strictMono := by
    intro a b hab
    exact Nat.factorial_lt_of_lt (by omega) (by omega)
  pos := fun k => Nat.factorial_pos _

/-- Every earlier factorial divides every later factorial. -/
theorem factorial_divides (j k : ℕ) (hjk : j ≤ k) :
    (j + 1).factorial ∣ (k + 1).factorial :=
  Nat.factorial_dvd_factorial (by omega)

/-- At step k, every previous term divides the current term. -/
theorem factorialSeq_prev_divides (j k : ℕ) (hjk : j < k) :
    factorialSeq.seq j ∣ factorialSeq.seq k :=
  factorial_divides j k (Nat.le_of_lt hjk)

/-- The usedSum for factorials is bounded by the sum of all previous factorials.
    Each used divisor e = (j+1)! contributes φ((j+1)!) ≤ (j+1)!.
    The injection j ↦ (j+1)! maps {0,...,k-1} onto the used divisors. -/
theorem factorialSeq_usedSum_le (k : ℕ) (hk : 0 < k) :
    usedSum factorialSeq k ≤ (range k).sum (fun j => (j + 1).factorial) := by
  -- usedSum = Σ_{e used} φ(e) ≤ Σ_{e used} e ≤ Σ_{j<k} (j+1)!
  -- The used divisor set is {1!, 2!, ..., k!}, and each maps to a unique j < k.
  -- Formalization: φ(e) ≤ e for all e, and the used divisors are a subset of
  -- the image of j ↦ (j+1)! over range k.
  sorry

/-- Σ_{j=0}^{k-1} (j+1)! < 2 · k! for k ≥ 2.
    The largest term k! dominates: all prior terms 1! + ... + (k-1)! < k!. -/
theorem sum_factorials_lt (k : ℕ) (hk : 2 ≤ k) :
    (range k).sum (fun j => (j + 1).factorial) < 2 * k.factorial := by
  -- Standard: Σ_{j=1}^{k} j! = k! + Σ_{j=1}^{k-1} j! < k! + k! = 2·k!
  -- since Σ_{j=1}^{k-1} j! < k! (each j! ≤ (k-1)!, and there are k-1 terms,
  -- but really the geometric-like sum gives the bound).
  sorry

/-- ρ(k) ≥ 1 - 2/(k+1) for the factorial sequence (k ≥ 2).
    From usedSum < 2·k! and n_k = (k+1)!, giving usedSum/n_k < 2/(k+1). -/
theorem factorialSeq_densityRatio_ge (k : ℕ) (hk : 2 ≤ k) :
    1 - 2 / ((k : ℝ) + 1) ≤ densityRatio factorialSeq k := by
  rw [densityRatio_complement]
  have hk_pos : (0 : ℕ) < k := by omega
  have h_usedSum := factorialSeq_usedSum_le k hk_pos
  have h_sum_lt := sum_factorials_lt k hk
  have hn_k : factorialSeq.seq k = (k + 1).factorial := rfl
  have hfact : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
  have hfact_pos : (0 : ℝ) < ((k + 1).factorial : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  apply sub_le_sub_left
  rw [hn_k]
  calc (usedSum factorialSeq k : ℝ) / ((k + 1).factorial : ℝ)
      ≤ ((range k).sum (fun j => (j + 1).factorial) : ℝ) / ((k + 1).factorial : ℝ) := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast h_usedSum
        · exact hfact_pos.le
    _ ≤ (2 * k.factorial : ℝ) / ((k + 1).factorial : ℝ) := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast Nat.le_of_lt h_sum_lt
        · exact hfact_pos.le
    _ = 2 / ((k : ℝ) + 1) := by
        rw [hfact, Nat.cast_mul]
        field_simp
        ring

/-- The factorial sequence is NOT Haight-type: ρ(k) ≥ 1/2 for k ≥ 3,
    so the density ratio cannot converge to 0. -/
theorem factorialSeq_not_vanishing :
    ¬ DensityToZero factorialSeq :=
  not_densityToZero_of_frequently_ge factorialSeq (by norm_num : (0 : ℝ) < 1/2)
    (eventually_atTop.mpr ⟨3, fun k hk => by
      have h := factorialSeq_densityRatio_ge k (by omega)
      have : 1 - 2 / (↑k + 1) ≥ 1/2 := by
        have : (2 : ℝ) / (↑k + 1) ≤ 1/2 := by
          rw [div_le_div_iff (by positivity : (0:ℝ) < ↑k + 1) (by norm_num : (0:ℝ) < 2)]
          push_cast; linarith
        linarith
      linarith⟩ |>.frequently)

/-! ## Part II: Necessary Conditions for Haight Sequences -/

/-- **Main structural theorem**: A Haight sequence must have ρ(k) < ε
    for all but o(N) indices. If VanishingAverage A, then for any ε > 0,
    the fraction of indices k < N with ρ(k) ≥ ε tends to 0.

    Proof: By contraposition on the average. If a constant fraction of
    indices had ρ ≥ ε, the Cesàro average would be ≥ ε · fraction,
    contradicting VanishingAverage.

    This characterizes Haight sequences: they must have "generically small"
    density ratios, meaning they grow slowly and have many used divisors
    at almost every step. -/
theorem haight_density_one_low (A : IncreasingSeq) (hV : VanishingAverage A)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => ((range N).filter (fun k => ε ≤ densityRatio A k)).card / (N : ℝ))
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- VanishingAverage gives eventually C_A(N) < δ * ε / 2
  have hVε : ∀ᶠ N in atTop, cesaroAvg A N < δ * ε / 2 :=
    hV (Iio_mem_nhds (by positivity))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hVε
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN_pos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN_pos
  have hC := hN₀ N (le_of_max_le_left hN)
  set S := (range N).filter (fun k => ε ≤ densityRatio A k)
  -- Sum ≥ |S| * ε (each high-ρ index contributes ≥ ε)
  have hsum_ge : (S.card : ℝ) * ε ≤ ∑ k ∈ range N, densityRatio A k := by
    calc (S.card : ℝ) * ε
        = ∑ _ ∈ S, ε := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ S, densityRatio A k :=
          sum_le_sum fun k hk => by simp only [mem_filter] at hk; exact hk.2
      _ ≤ ∑ k ∈ range N, densityRatio A k :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            fun k _ _ => densityRatio_nonneg A k
  -- Sum = N * C_A(N) < N * δε/2
  have hsum_lt : ∑ k ∈ range N, densityRatio A k < N * (δ * ε / 2) := by
    have := hC; unfold cesaroAvg at this
    rwa [div_lt_iff hNr] at this
  -- So |S| * ε < N * δε/2, hence |S|/N < δ/2 < δ
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hNr.le)]
  calc (S.card : ℝ) / N
      ≤ N * (δ * ε / 2) / (N * ε) := by
        rw [div_le_div_iff hNr (by positivity : (0:ℝ) < N * ε)]
        nlinarith
    _ = δ / 2 := by field_simp; ring
    _ < δ := by linarith

/-! ## Part III: Growth Rate Constraints -/

/-- At low-density indices in a Haight sequence, growth is polynomial.
    If ρ(k+1) < 1/2, then n_{k+1} < 2(k+1) · n_k.
    This means Haight sequences cannot grow super-polynomially at indices
    where the density ratio is small. -/
theorem haight_polynomial_growth (A : IncreasingSeq) (k : ℕ) (hk : 0 < k)
    (hρ : densityRatio A (k + 1) < 1 / 2) :
    (A.seq (k + 1) : ℝ) < 2 * (k + 1 : ℝ) * A.seq k := by
  have h := consecutive_low_density_ratio A k hk (1/2) (by norm_num) (by norm_num) hρ
  have hn_pos : (0 : ℝ) < A.seq k := Nat.cast_pos.mpr (A.pos k)
  rw [div_lt_div_iff hn_pos (by norm_num : (0:ℝ) < 1 - 1/2)] at h
  linarith

/-! ## Part IV: Divisibility Density -/

/-- The "divisibility density" at index k: what fraction of divisors of n_k
    are previous sequence terms. High divisibility density → high usedSum → low ρ. -/
noncomputable def divDensity (A : IncreasingSeq) (k : ℕ) : ℝ :=
  ((A.seq k).divisors.filter (fun e => ∃ j, j < k ∧ e = A.seq j)).card /
  (A.seq k).divisors.card

theorem divDensity_nonneg (A : IncreasingSeq) (k : ℕ) :
    0 ≤ divDensity A k :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem divDensity_le_one (A : IncreasingSeq) (k : ℕ) :
    divDensity A k ≤ 1 := by
  unfold divDensity
  rcases Nat.eq_zero_or_pos (A.seq k).divisors.card with h | h
  · simp [h]
  · rw [div_le_one (Nat.cast_pos.mpr h)]
    exact_mod_cast card_filter_le _ _

theorem divDensity_zero (A : IncreasingSeq) :
    divDensity A 0 = 0 := by
  unfold divDensity
  suffices h : ((A.seq 0).divisors.filter (fun e => ∃ j, j < 0 ∧ e = A.seq j)) = ∅ by
    rw [h, card_empty, Nat.cast_zero, zero_div]
  rw [eq_empty_iff_forall_not_mem]
  intro e; simp only [mem_filter, Nat.mem_divisors, not_and]
  intro _; rintro ⟨j, hj, _⟩; omega

/-- For the factorial sequence, divDensity ≤ k/d((k+1)!) where d(n) is
    the divisor count. Since d(k!) grows super-polynomially while k grows
    linearly, divDensity → 0: factorials have far too many divisors for
    any significant fraction to be "used." -/
theorem factorialSeq_divDensity_le (k : ℕ) :
    divDensity factorialSeq k ≤ k / (((k + 1).factorial).divisors.card : ℝ) := by
  unfold divDensity factorialSeq
  dsimp
  rcases Nat.eq_zero_or_pos ((k + 1).factorial).divisors.card with h | h
  · simp [h]
  · rw [div_le_div_right (Nat.cast_pos.mpr h)]
    exact_mod_cast usedDivisors_card_le factorialSeq k

end Erdos1000OQ01
