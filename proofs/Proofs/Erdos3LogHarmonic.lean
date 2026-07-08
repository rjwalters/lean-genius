/-
  Erdős #3 supporting lemma: divergence of the log-harmonic (Bertrand) series
  ∑ 1/(n · log n).

  This substantiates the counterexample profile documented in the
  `StrongRequiredBound` docstring of `Erdos3Problem.lean`: a set whose counting
  function sits at the `o(N / log N)` threshold (e.g. the primes, counting function
  ~ N / log N) can still have a *divergent* reciprocal sum, since by partial
  summation ∑_{a ≤ N} 1/a ~ ∑ 1/(n log n) → ∞. Hence `RequiredBound` (the
  `o(N/log N)` threshold) is genuinely insufficient to force the AP conclusion; the
  strictly stronger `StrongRequiredBound` `O(N/(log N)^{1+δ})` threshold is needed.

  Proof: Cauchy condensation (`summable_condensed_iff_of_nonneg`) reduces summability
  of `1/(n log n)` to summability of `∑ 2^k / (2^k · log 2^k) ≍ ∑ 1/(k log 2)`, a
  constant multiple of the harmonic series, which diverges
  (`not_summable_one_div_natCast`).

  STATUS: [UNVERIFIED] — the build host is currently unhealthy (memory-kills at 32GB
  and purges corrupted Mathlib `.ltar` cache even on known-good files; see the
  build-blocker note in research/problems/erdos-3-incomplete-01/state.md). The proof
  is self-contained and uses only standard Mathlib lemmas, but has NOT been
  machine-checked this session. It must be `docker-build`-verified before any
  "verified" claim or gallery promotion.
-/
import Mathlib

open Filter Real

namespace Erdos3Bertrand

/-- Shifted log-harmonic term `1/((n+2)·log(n+2))`; positive and antitone for all `n`. -/
private noncomputable def f₂ (n : ℕ) : ℝ :=
  1 / (((n : ℝ) + 2) * Real.log ((n : ℝ) + 2))

private lemma f₂_nonneg (n : ℕ) : 0 ≤ f₂ n := by
  unfold f₂
  apply div_nonneg (by norm_num)
  apply mul_nonneg (by positivity)
  have : (1 : ℝ) ≤ (n : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  exact Real.log_nonneg this

private lemma f₂_antitone : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → f₂ n ≤ f₂ m := by
  intro m n _ hmn
  unfold f₂
  have hcastm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm2 : (0 : ℝ) < ((m : ℝ) + 2) * Real.log ((m : ℝ) + 2) := by
    apply mul_pos (by linarith)
    exact Real.log_pos (by linarith)
  apply one_div_le_one_div_of_le hm2
  have hmn' : ((m : ℝ) + 2) ≤ ((n : ℝ) + 2) := by
    have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    linarith
  apply mul_le_mul hmn' (Real.log_le_log (by linarith) hmn')
    (Real.log_nonneg (by linarith)) (by linarith)

/-- The lower bound on the condensed term used to compare against the harmonic series. -/
private lemma cond_lower (j : ℕ) (hj : 1 ≤ j) :
    1 / (2 * ((j : ℝ) + 1) * Real.log 2)
      ≤ (2 : ℝ) ^ j / (((2 : ℝ) ^ j + 2) * Real.log ((2 : ℝ) ^ j + 2)) := by
  have hpos_pow : (0 : ℝ) < 2 ^ j := by positivity
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h2j : (2 : ℝ) ≤ 2 ^ j := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  have hb1 : (0 : ℝ) < (2 : ℝ) ^ j + 2 := by positivity
  have hlogb : (0 : ℝ) < Real.log ((2 : ℝ) ^ j + 2) := Real.log_pos (by linarith)
  -- `2^j + 2 ≤ 2^(j+1)`
  have hsum_le : (2 : ℝ) ^ j + 2 ≤ 2 ^ (j + 1) := by
    rw [pow_succ]; linarith [h2j]
  -- `log(2^j+2) ≤ (j+1)·log 2`
  have hlog_le : Real.log ((2 : ℝ) ^ j + 2) ≤ ((j : ℝ) + 1) * Real.log 2 := by
    have hstep : Real.log ((2 : ℝ) ^ j + 2) ≤ Real.log ((2 : ℝ) ^ (j + 1)) :=
      Real.log_le_log hb1 hsum_le
    rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at hstep
  -- denominator product bound
  have hD : (((2 : ℝ) ^ j + 2) * Real.log ((2 : ℝ) ^ j + 2))
      ≤ 2 ^ (j + 1) * (((j : ℝ) + 1) * Real.log 2) :=
    mul_le_mul hsum_le hlog_le (le_of_lt hlogb) (by positivity)
  -- rewrite RHS as `1 / (D / 2^j)` and compare denominators
  rw [show (2 : ℝ) ^ j / (((2 : ℝ) ^ j + 2) * Real.log ((2 : ℝ) ^ j + 2))
        = 1 / ((((2 : ℝ) ^ j + 2) * Real.log ((2 : ℝ) ^ j + 2)) / 2 ^ j) from
      (one_div_div _ _).symm]
  apply one_div_le_one_div_of_le (by positivity)
  rw [div_le_iff₀ hpos_pow]
  calc (((2 : ℝ) ^ j + 2) * Real.log ((2 : ℝ) ^ j + 2))
      ≤ 2 ^ (j + 1) * (((j : ℝ) + 1) * Real.log 2) := hD
    _ = 2 * ((j : ℝ) + 1) * Real.log 2 * 2 ^ j := by rw [pow_succ]; ring

private lemma not_summable_f₂ : ¬ Summable f₂ := by
  intro hsum
  -- Cauchy condensation: `f₂` summable ⟹ `∑ 2^k · f₂(2^k)` summable.
  have hcond : Summable (fun k : ℕ => (2 : ℝ) ^ k * f₂ (2 ^ k)) :=
    (summable_condensed_iff_of_nonneg f₂_nonneg f₂_antitone).mpr hsum
  -- drop the `k = 0` term so the lower bound (valid for `j ≥ 1`) applies termwise
  have hS1 : Summable (fun k : ℕ => (2 : ℝ) ^ (k + 1) * f₂ (2 ^ (k + 1))) :=
    (summable_nat_add_iff 1).mpr hcond
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- compare with `1/(2(k+2)log2)`, a constant multiple of the harmonic series
  have hcomp : Summable (fun k : ℕ => 1 / (2 * ((k : ℝ) + 2) * Real.log 2)) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hS1
    have key := cond_lower (k + 1) (Nat.le_add_left 1 k)
    have hlhs : (1 : ℝ) / (2 * ((k : ℝ) + 2) * Real.log 2)
        = 1 / (2 * (((k + 1 : ℕ) : ℝ) + 1) * Real.log 2) := by push_cast; ring
    have hrhs : (2 : ℝ) ^ (k + 1) * f₂ (2 ^ (k + 1))
        = (2 : ℝ) ^ (k + 1)
            / (((2 : ℝ) ^ (k + 1) + 2) * Real.log ((2 : ℝ) ^ (k + 1) + 2)) := by
      unfold f₂; push_cast; ring
    rw [hlhs, hrhs]; exact key
  -- derive the harmonic series and contradict its divergence
  have h2 : Summable (fun k : ℕ => 1 / ((k : ℝ) + 2)) := by
    have hm := hcomp.mul_left (2 * Real.log 2)
    refine hm.congr (fun k => ?_)
    have hk2 : ((k : ℝ) + 2) ≠ 0 := by positivity
    have hl2 : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
    field_simp
  have h2' : Summable (fun n : ℕ => 1 / (((n + 2 : ℕ)) : ℝ)) :=
    h2.congr (fun k => by push_cast; ring)
  exact not_summable_one_div_natCast ((summable_nat_add_iff 2).mp h2')

/-- **The log-harmonic (Bertrand) series `∑ 1/(n · log n)` diverges.** -/
theorem not_summable_one_div_nat_mul_log :
    ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) * Real.log n)) := by
  intro hsum
  -- shift by two (dropping the `n = 0, 1` terms, where the summand vanishes) lands on `f₂`
  have hshift : Summable f₂ :=
    ((summable_nat_add_iff 2).mpr hsum).congr (fun n => by unfold f₂; push_cast; ring)
  exact not_summable_f₂ hshift

end Erdos3Bertrand
