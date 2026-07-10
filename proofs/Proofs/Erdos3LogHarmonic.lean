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

  STATUS: [VERIFIED] — machine-checked with `docker-build.sh Proofs.Erdos3LogHarmonic`
  (7743 jobs, 0 sorries). `#print axioms not_summable_one_div_nat_mul_log` reports only
  the foundational trio `[propext, Classical.choice, Quot.sound]`; no `sorryAx`,
  `Lean.ofReduceBool`, or added axioms.
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

/-!
### Convergent companion: `∑ 1/(n · (log n)^{1+δ})` converges for `δ > 0`

The `p = 1+δ > 1` twin of `not_summable_one_div_nat_mul_log` (the `p = 1`
divergent case).  Together they pin the Bertrand-series convergence boundary
at the exponent `p = 1`: divergent at `p = 1`, convergent at every `p > 1`.

This is the analytic ingredient needed to sharpen the Erdős #3 conditional
reduction below the `(log N)^{1+δ}` threshold of
`Erdos3Problem.summable_of_strongBound`: a set whose counting function is
`O(N / (log N · (log log N)^{1+δ}))` has convergent reciprocal sum, because the
dyadic block masses are bounded by the general term of *this* convergent series.
No such lemma exists in Mathlib (only the `p`-series `Real.summable_one_div_nat_rpow`
and the divergent harmonic/log-harmonic cases), so it is proved here from scratch
by Cauchy condensation, mirroring the divergent proof above.
-/

section Convergent

variable (δ : ℝ)

/-- Shifted convergent-Bertrand term `1/((n+2)·(log(n+2))^{1+δ})`; positive and
    antitone (for `n ≥ 1`), the inputs Cauchy condensation demands. -/
private noncomputable def h₂ (n : ℕ) : ℝ :=
  1 / (((n : ℝ) + 2) * (Real.log ((n : ℝ) + 2)) ^ (1 + δ))

private lemma h₂_nonneg (n : ℕ) : 0 ≤ h₂ δ n := by
  unfold h₂
  have hlog : 0 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  positivity

private lemma h₂_antitone (hδ : 0 ≤ δ) :
    ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → h₂ δ n ≤ h₂ δ m := by
  intro m n _ hmn
  unfold h₂
  have hlogm_pos : 0 < Real.log ((m : ℝ) + 2) :=
    Real.log_pos (by have := Nat.cast_nonneg (α := ℝ) m; linarith)
  have hDm_pos : 0 < ((m : ℝ) + 2) * (Real.log ((m : ℝ) + 2)) ^ (1 + δ) := by
    apply mul_pos (by have := Nat.cast_nonneg (α := ℝ) m; linarith)
    exact Real.rpow_pos_of_pos hlogm_pos _
  apply one_div_le_one_div_of_le hDm_pos
  have hmn' : ((m : ℝ) + 2) ≤ ((n : ℝ) + 2) := by
    have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    linarith
  have hlog_le : Real.log ((m : ℝ) + 2) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by have := Nat.cast_nonneg (α := ℝ) m; linarith) hmn'
  exact mul_le_mul hmn'
    (Real.rpow_le_rpow hlogm_pos.le hlog_le (by linarith))
    (Real.rpow_nonneg hlogm_pos.le _) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)

/-- Upper bound on the Cauchy-condensed term `2^k · h₂(2^k)`, compared against the
    convergent `p`-series term `1/k^{1+δ}` (up to the constant `(log 2)^{-(1+δ)}`). -/
private lemma h₂_cond_upper (hδ : 0 ≤ δ) (k : ℕ) (hk : 1 ≤ k) :
    (2 : ℝ) ^ k * h₂ δ (2 ^ k)
      ≤ (1 / (Real.log 2) ^ (1 + δ)) * (1 / (k : ℝ) ^ (1 + δ)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hklog_pos : 0 < (k : ℝ) * Real.log 2 := by positivity
  have hlogb_ge : (k : ℝ) * Real.log 2 ≤ Real.log ((2 : ℝ) ^ k + 2) := by
    have hstep : Real.log ((2 : ℝ) ^ k) ≤ Real.log ((2 : ℝ) ^ k + 2) :=
      Real.log_le_log (by positivity) (by linarith [pow_pos (show (0:ℝ) < 2 by norm_num) k])
    rwa [Real.log_pow] at hstep
  have hlogb_pos : 0 < Real.log ((2 : ℝ) ^ k + 2) := lt_of_lt_of_le hklog_pos hlogb_ge
  have hden_ge : ((k : ℝ) * Real.log 2) ^ (1 + δ)
      ≤ (Real.log ((2 : ℝ) ^ k + 2)) ^ (1 + δ) :=
    Real.rpow_le_rpow hklog_pos.le hlogb_ge (by linarith)
  -- `2^k · h₂(2^k) ≤ 1/(log(2^k+2))^{1+δ}`, dropping the `2^k/(2^k+2) ≤ 1` factor.
  have step1 : (2 : ℝ) ^ k * h₂ δ (2 ^ k)
      ≤ 1 / (Real.log ((2 : ℝ) ^ k + 2)) ^ (1 + δ) := by
    unfold h₂
    push_cast
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (Real.rpow_pos_of_pos hlogb_pos _), one_mul]
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hlogb_pos.le _)
  -- Rewrite the target RHS as `1/((k·log2)^{1+δ})` via `mul_rpow`.
  have hRHS : (1 / (Real.log 2) ^ (1 + δ)) * (1 / (k : ℝ) ^ (1 + δ))
      = 1 / (((k : ℝ) * Real.log 2) ^ (1 + δ)) := by
    rw [Real.mul_rpow (by positivity) hlog2.le]; ring
  calc (2 : ℝ) ^ k * h₂ δ (2 ^ k)
      ≤ 1 / (Real.log ((2 : ℝ) ^ k + 2)) ^ (1 + δ) := step1
    _ ≤ 1 / (((k : ℝ) * Real.log 2) ^ (1 + δ)) :=
        one_div_le_one_div_of_le (Real.rpow_pos_of_pos hklog_pos _) hden_ge
    _ = (1 / (Real.log 2) ^ (1 + δ)) * (1 / (k : ℝ) ^ (1 + δ)) := hRHS.symm

private lemma summable_h₂ (hδ : 0 < δ) : Summable (h₂ δ) := by
  rw [← summable_condensed_iff_of_nonneg (h₂_nonneg δ) (h₂_antitone δ hδ.le)]
  -- reduce to the `k ≥ 1` tail (the bound needs `k ≥ 1` so `log 2^k = k·log2 > 0`)
  apply (summable_nat_add_iff 1).mp
  -- dominate `2^{n+1}·h₂(2^{n+1})` by a constant multiple of the p-series `1/(n+1)^{1+δ}`
  set D : ℕ → ℝ := fun n => (1 / (Real.log 2) ^ (1 + δ)) * (1 / ((n : ℝ) + 1) ^ (1 + δ))
    with hDdef
  have hDsum : Summable D := by
    have hp : (1 : ℝ) < 1 + δ := by linarith
    have h1 := Real.summable_one_div_nat_rpow.mpr hp
    have h2 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (1 + δ)) := by
      have h1' := (summable_nat_add_iff 1).mpr h1
      simpa using h1'
    exact h2.mul_left _
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hDsum
  · exact mul_nonneg (by positivity) (h₂_nonneg δ _)
  · have hb := h₂_cond_upper δ hδ.le (n + 1) (Nat.le_add_left 1 n)
    have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hDdef]
    calc (2 : ℝ) ^ (n + 1) * h₂ δ (2 ^ (n + 1))
        ≤ (1 / (Real.log 2) ^ (1 + δ)) * (1 / (((n + 1 : ℕ)) : ℝ) ^ (1 + δ)) := hb
      _ = (1 / (Real.log 2) ^ (1 + δ)) * (1 / ((n : ℝ) + 1) ^ (1 + δ)) := by rw [hcast]

/-- **The convergent Bertrand series `∑ 1/(n · (log n)^{1+δ})` converges for `δ > 0`.**
    The `p = 1+δ > 1` companion of `not_summable_one_div_nat_mul_log`; together they
    locate the Bertrand-series convergence threshold exactly at the exponent `p = 1`.
    Proof by Cauchy condensation: the condensed term `2^k · (2^k·(log 2^k)^{1+δ})⁻¹`
    is `≤ (log 2)^{-(1+δ)} · k^{-(1+δ)}`, a constant multiple of the convergent
    `p`-series `∑ 1/k^{1+δ}`. -/
theorem summable_one_div_nat_mul_log_rpow {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) * (Real.log n) ^ (1 + δ))) := by
  -- shift by two (the `n = 0, 1` terms vanish or are harmless) to land on `h₂`
  apply (summable_nat_add_iff 2).mp
  refine (summable_h₂ δ hδ).congr (fun n => ?_)
  unfold h₂
  push_cast
  ring

end Convergent

end Erdos3Bertrand
