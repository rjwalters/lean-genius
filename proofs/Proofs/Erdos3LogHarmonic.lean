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

/-!
### Convergent Bertrand series with a multiplicative constant inside the log

The dyadic-blocking step that sharpens the Erdős #3 conditional reduction produces
a series whose general term carries a *multiplicative constant* `c = log 2 < 1`
inside the logarithm:

    ∑_j  1 / ((j+1) · (log ((j+1) · log 2))^{1+δ}).

Because `log ((j+1)·c) = log (j+1) + log c` with `log c < 0` for `c < 1`, this is
not literally the constant-free `summable_one_div_nat_mul_log_rpow`.  The
following lemma removes exactly that gap: for any `c > 0`, `δ > 0` the series
`∑ 1/(n·(log (n·c))^{1+δ})` still converges.  The proof is a tail comparison —
once `n ≥ 1/c²` one has `log n ≤ 2·log(n·c)` (equivalently `n·c² ≥ 1`), so each
term is at most `2^{1+δ}` times the corresponding constant-free term, and
`summable_one_div_nat_mul_log_rpow` supplies the dominating series.
-/

/-- **Convergent Bertrand series with a multiplicative constant inside the log.**
    For every `c > 0` and `δ > 0`, `∑ 1/(n·(log (n·c))^{1+δ})` converges.  This is
    the constant-carrying generalisation of `summable_one_div_nat_mul_log_rpow`
    (`c = 1`), the exact form the Erdős #3 dyadic-blocking argument needs (`c = log 2`).
    Proof: on the tail `n ≥ 1/c²` (where `n·c² ≥ 1`, hence `log n ≤ 2·log(n·c)`) each
    term is `≤ 2^{1+δ}` times the constant-free term, which is summable. -/
theorem summable_one_div_nat_mul_log_mul_const {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) * (Real.log ((n : ℝ) * c)) ^ (1 + δ))) := by
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  -- threshold `N₀` above `2`, `2/c` and `1/c²` (so `m·c ≥ 2` and `m·c² ≥ 1` on the tail)
  set N₀ : ℕ := max 2 (⌈2 / c⌉₊ + ⌈1 / c ^ 2⌉₊) with hN₀def
  have hN₀2 : (2 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast le_max_left 2 (⌈2 / c⌉₊ + ⌈1 / c ^ 2⌉₊)
  have hN₀2c : 2 / c ≤ (N₀ : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (Nat.le_add_right _ _)
      (le_max_right 2 (⌈2 / c⌉₊ + ⌈1 / c ^ 2⌉₊)))
  have hN₀c2 : 1 / c ^ 2 ≤ (N₀ : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (Nat.le_add_left _ _)
      (le_max_right 2 (⌈2 / c⌉₊ + ⌈1 / c ^ 2⌉₊)))
  -- dominating series: the constant-free convergent series, shifted and scaled by `2^{1+δ}`
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) * (Real.log n) ^ (1 + δ))) :=
    summable_one_div_nat_mul_log_rpow hδ
  have hdom : Summable (fun n : ℕ => (2 : ℝ) ^ (1 + δ) *
      (1 / (((n + N₀ : ℕ) : ℝ) * (Real.log ((n + N₀ : ℕ) : ℝ)) ^ (1 + δ)))) :=
    ((summable_nat_add_iff N₀).mpr hbase).mul_left _
  apply (summable_nat_add_iff N₀).mp
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hdom
  · -- nonnegativity of the shifted target term
    set m : ℝ := ((n + N₀ : ℕ) : ℝ) with hm
    have hmN : (N₀ : ℝ) ≤ m := by rw [hm]; exact_mod_cast Nat.le_add_left N₀ n
    have hm2 : (2 : ℝ) ≤ m := le_trans hN₀2 hmN
    have hmc : (2 : ℝ) ≤ m * c := (div_le_iff₀ hc).mp (le_trans hN₀2c hmN)
    have hlogmc : 0 ≤ Real.log (m * c) := Real.log_nonneg (by linarith)
    positivity
  · -- termwise domination
    set m : ℝ := ((n + N₀ : ℕ) : ℝ) with hm
    have hmN : (N₀ : ℝ) ≤ m := by rw [hm]; exact_mod_cast Nat.le_add_left N₀ n
    have hm2 : (2 : ℝ) ≤ m := le_trans hN₀2 hmN
    have hm_pos : 0 < m := by linarith
    have hm1 : (1 : ℝ) ≤ m := by linarith
    have hmc : (2 : ℝ) ≤ m * c := (div_le_iff₀ hc).mp (le_trans hN₀2c hmN)
    have hmc2 : (1 : ℝ) ≤ m * c ^ 2 := (div_le_iff₀ hc2).mp (le_trans hN₀c2 hmN)
    have hlogmc_pos : 0 < Real.log (m * c) := Real.log_pos (by linarith)
    -- key comparison `log m ≤ 2·log(m·c)`, i.e. `0 ≤ log(m·c²)`
    have hmc_eq : Real.log (m * c) = Real.log m + Real.log c :=
      Real.log_mul (ne_of_gt hm_pos) (ne_of_gt hc)
    have hmc2_eq : Real.log (m * c ^ 2) = Real.log m + 2 * Real.log c := by
      rw [Real.log_mul (ne_of_gt hm_pos) (by positivity), Real.log_pow]; push_cast; ring
    have hmc2_nonneg : 0 ≤ Real.log m + 2 * Real.log c := hmc2_eq ▸ Real.log_nonneg hmc2
    have hcrux : Real.log m ≤ 2 * Real.log (m * c) := by rw [hmc_eq]; linarith
    -- lift through the `(·)^{1+δ}` power
    have hPQ : (Real.log m) ^ (1 + δ)
        ≤ (2 : ℝ) ^ (1 + δ) * (Real.log (m * c)) ^ (1 + δ) := by
      calc (Real.log m) ^ (1 + δ)
          ≤ (2 * Real.log (m * c)) ^ (1 + δ) :=
            Real.rpow_le_rpow (Real.log_nonneg hm1) hcrux (by linarith)
        _ = (2 : ℝ) ^ (1 + δ) * (Real.log (m * c)) ^ (1 + δ) :=
            Real.mul_rpow (by norm_num) hlogmc_pos.le
    have hP_pos : 0 < (Real.log m) ^ (1 + δ) :=
      Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _
    have hQ_pos : 0 < (Real.log (m * c)) ^ (1 + δ) := Real.rpow_pos_of_pos hlogmc_pos _
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    calc m * (Real.log m) ^ (1 + δ)
        ≤ m * ((2 : ℝ) ^ (1 + δ) * (Real.log (m * c)) ^ (1 + δ)) :=
          mul_le_mul_of_nonneg_left hPQ hm_pos.le
      _ = (2 : ℝ) ^ (1 + δ) * (m * (Real.log (m * c)) ^ (1 + δ)) := by ring

/-- **Divergent Bertrand series with a multiplicative constant inside the log.**
    For every `c > 0`, `∑ 1/(n·log (n·c))` diverges.  This is the exact `p = 1`
    divergence twin of the convergent `summable_one_div_nat_mul_log_mul_const`
    (`p = 1+δ`): together they pin the constant-in-log Bertrand boundary at the
    exponent `p = 1`, exactly as `not_summable_one_div_nat_mul_log` and
    `summable_one_div_nat_mul_log_rpow` do for the constant-free series (`c = 1`).
    The multiplicative constant inside the log does not move the threshold.
    Proof: a tail comparison the mirror of the convergent lemma's.  On the tail
    `n ≥ max (c) (2/c)` one has `c ≤ n` (so `log c ≤ log n`, giving `log (n·c) ≤ 2·log n`)
    and `n·c ≥ 2` (so `log (n·c) > 0`); hence each term dominates `½·1/(n·log n)`,
    and `∑ 1/(n·log n)` already diverges (`not_summable_one_div_nat_mul_log`). -/
theorem not_summable_one_div_nat_mul_log_mul_const {c : ℝ} (hc : 0 < c) :
    ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) * Real.log ((n : ℝ) * c))) := by
  intro hsum
  -- threshold `N₀ ≥ 2`, `≥ c`, `≥ 2/c` (so `m ≥ 2`, `c ≤ m`, `m·c ≥ 2` on the tail)
  set N₀ : ℕ := max 2 (⌈c⌉₊ + ⌈2 / c⌉₊) with hN₀def
  have hN₀2 : (2 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast le_max_left 2 (⌈c⌉₊ + ⌈2 / c⌉₊)
  have hN₀c : c ≤ (N₀ : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (Nat.le_add_right _ _)
      (le_max_right 2 (⌈c⌉₊ + ⌈2 / c⌉₊)))
  have hN₀2c : 2 / c ≤ (N₀ : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (Nat.le_add_left _ _)
      (le_max_right 2 (⌈c⌉₊ + ⌈2 / c⌉₊)))
  -- the given series, shifted past the threshold and scaled by `2`, dominates `1/(n·log n)`
  have hdom : Summable (fun n : ℕ => (2 : ℝ) *
      (1 / (((n + N₀ : ℕ) : ℝ) * Real.log (((n + N₀ : ℕ) : ℝ) * c)))) :=
    ((summable_nat_add_iff N₀).mpr hsum).mul_left _
  -- derive `Summable (1/(n·log n))`, contradicting its divergence
  apply not_summable_one_div_nat_mul_log
  apply (summable_nat_add_iff N₀).mp
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hdom
  · -- nonnegativity of the shifted `1/(m·log m)`
    set m : ℝ := ((n + N₀ : ℕ) : ℝ) with hm
    have hmN : (N₀ : ℝ) ≤ m := by rw [hm]; exact_mod_cast Nat.le_add_left N₀ n
    have hm2 : (2 : ℝ) ≤ m := le_trans hN₀2 hmN
    have hm_pos : 0 < m := by linarith
    have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
    positivity
  · -- termwise domination `1/(m·log m) ≤ 2·(1/(m·log (m·c)))`
    set m : ℝ := ((n + N₀ : ℕ) : ℝ) with hm
    have hmN : (N₀ : ℝ) ≤ m := by rw [hm]; exact_mod_cast Nat.le_add_left N₀ n
    have hm2 : (2 : ℝ) ≤ m := le_trans hN₀2 hmN
    have hm_pos : 0 < m := by linarith
    have hmc_ge : c ≤ m := le_trans hN₀c hmN
    have hmc2 : (2 : ℝ) ≤ m * c := (div_le_iff₀ hc).mp (le_trans hN₀2c hmN)
    have hlogm_pos : 0 < Real.log m := Real.log_pos (by linarith)
    have hlogmc_pos : 0 < Real.log (m * c) := Real.log_pos (by linarith)
    have hlogc_le : Real.log c ≤ Real.log m := Real.log_le_log hc hmc_ge
    have hmc_eq : Real.log (m * c) = Real.log m + Real.log c :=
      Real.log_mul (ne_of_gt hm_pos) (ne_of_gt hc)
    -- key comparison `log (m·c) ≤ 2·log m` (`log c ≤ log m` since `c ≤ m`)
    have hcrux : Real.log (m * c) ≤ 2 * Real.log m := by rw [hmc_eq]; linarith
    rw [mul_one_div, div_le_div_iff₀ (mul_pos hm_pos hlogm_pos) (mul_pos hm_pos hlogmc_pos),
      one_mul]
    calc m * Real.log (m * c)
        ≤ m * (2 * Real.log m) := mul_le_mul_of_nonneg_left hcrux hm_pos.le
      _ = 2 * (m * Real.log m) := by ring

/-!
### Second-tier (iterated-log) Bertrand divergence: `∑ 1/(n · log n · log log n)`

`not_summable_one_div_nat_mul_log` pins the *first* Bertrand boundary: `∑ 1/(n(log n)^p)`
diverges at `p = 1` and converges for `p > 1`.  The genuine divergence borderline that
makes Erdős #3 hard, however, sits one iterated logarithm deeper: the profile
`f(N) ≍ N/(log N · log log N)` is still `o(N/log N)` (so it satisfies the weak
`RequiredBound` threshold) yet has a *divergent* reciprocal sum, because by partial
summation `∑_{a≤N} 1/a ≍ ∑ 1/(n · log n · log log n) → ∞`.  This is exactly the profile
whose existence — as an AP-free set — is the open content of Erdős #3, and it is the
reason `RequiredBound` (`o(N/log N)`) cannot be strengthened to a *provable* sufficient
condition without pushing all the way down to a `(log log N)`-power correction.

The following theorem formalises that second-tier divergence.  It is the true divergence
companion to the convergent `summable_one_div_nat_mul_log_mul_const` above (which lives at
the `(log log N)^{1+δ}` correction): together they now bracket the Erdős #3 borderline on
*both* logarithmic axes.

**Proof.**  Cauchy condensation absorbs one logarithm: the condensed term
`2^k · (2^k · log(2^k) · log log(2^k))⁻¹ = (log(2^k) · log log(2^k))⁻¹ ≍ 1/(k · log k)`,
so the condensed series is (a tail of) a constant multiple of the *first-tier*
log-harmonic series `∑ 1/(n log n)`, whose divergence is `not_summable_f₂` above.  Hence
the condensed series — and therefore the original — is not summable.
-/

/-- Shifted iterated-log term `1/((n+3)·log(n+3)·log log(n+3))`; positive and antitone.
    The shift `+3 > e` guarantees `log(n+3) > 1`, so the inner `log log` is positive. -/
private noncomputable def g₃ (n : ℕ) : ℝ :=
  1 / (((n : ℝ) + 3) * Real.log ((n : ℝ) + 3) * Real.log (Real.log ((n : ℝ) + 3)))

private lemma g₃_nonneg (n : ℕ) : 0 ≤ g₃ n := by
  unfold g₃
  have hn3 : (3 : ℝ) ≤ (n : ℝ) + 3 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hlog : 1 < Real.log ((n : ℝ) + 3) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    calc Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      _ ≤ (n : ℝ) + 3 := by linarith
  have hll : 0 ≤ Real.log (Real.log ((n : ℝ) + 3)) := Real.log_nonneg hlog.le
  refine div_nonneg (by norm_num) ?_
  refine mul_nonneg (mul_nonneg (by linarith) ?_) hll
  exact le_of_lt (lt_trans one_pos hlog)

private lemma g₃_antitone : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → g₃ n ≤ g₃ m := by
  intro m n _ hmn
  unfold g₃
  have hmc : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hmn3 : ((m : ℝ) + 3) ≤ ((n : ℝ) + 3) := by linarith
  have hlogm : 1 < Real.log ((m : ℝ) + 3) := by
    rw [Real.lt_log_iff_exp_lt (by have := Nat.cast_nonneg (α := ℝ) m; linarith)]
    calc Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      _ ≤ (m : ℝ) + 3 := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hlogm0 : 0 < Real.log ((m : ℝ) + 3) := lt_trans one_pos hlogm
  have hllm0 : 0 < Real.log (Real.log ((m : ℝ) + 3)) := Real.log_pos hlogm
  have hDm : 0 < ((m : ℝ) + 3) * Real.log ((m : ℝ) + 3) * Real.log (Real.log ((m : ℝ) + 3)) :=
    mul_pos (mul_pos (by have := Nat.cast_nonneg (α := ℝ) m; linarith) hlogm0) hllm0
  apply one_div_le_one_div_of_le hDm
  have hlogmn : Real.log ((m : ℝ) + 3) ≤ Real.log ((n : ℝ) + 3) :=
    Real.log_le_log (by have := Nat.cast_nonneg (α := ℝ) m; linarith) hmn3
  have hllmn : Real.log (Real.log ((m : ℝ) + 3)) ≤ Real.log (Real.log ((n : ℝ) + 3)) :=
    Real.log_le_log hlogm0 hlogmn
  exact mul_le_mul
    (mul_le_mul hmn3 hlogmn hlogm0.le (by have := Nat.cast_nonneg (α := ℝ) n; linarith))
    hllmn hllm0.le
    (mul_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (le_trans hlogm0.le hlogmn))

/-- The condensed term `2^k · g₃(2^k)` dominates `(2 log 2)⁻¹ · f₂ k`, a constant multiple
    of the first-tier log-harmonic term.  Valid for `k ≥ 2` (so `2^k ≥ 4`, giving both
    `2^k + 3 ≤ 2^{k+1}` and `log(2^k+3) > 1`). -/
private lemma cond_lower₃ (k : ℕ) (hk : 2 ≤ k) :
    (1 / (2 * Real.log 2)) * f₂ k ≤ (2 : ℝ) ^ k * g₃ (2 ^ k) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le : Real.log 2 ≤ 1 := le_of_lt (lt_of_lt_of_le Real.log_two_lt_d9 (by norm_num))
  have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hpow : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hlogk2 : 0 < Real.log ((k : ℝ) + 2) := Real.log_pos (by linarith)
  set b : ℝ := (2 : ℝ) ^ k + 3 with hbdef
  have hb : (7 : ℝ) ≤ b := by rw [hbdef]; linarith
  have hb0 : 0 < b := by linarith
  set L : ℝ := Real.log b with hLdef
  have hL1 : 1 < L := by
    rw [hLdef, Real.lt_log_iff_exp_lt hb0]
    calc Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      _ ≤ b := by linarith
  have hL0 : 0 < L := lt_trans one_pos hL1
  set LL : ℝ := Real.log L with hLLdef
  have hLL0 : 0 < LL := by rw [hLLdef]; exact Real.log_pos hL1
  -- factor bounds
  have hb_le : b ≤ (2 : ℝ) ^ (k + 1) := by rw [hbdef, pow_succ]; nlinarith [h4]
  have hL_le : L ≤ ((k : ℝ) + 2) * Real.log 2 := by
    have hble2 : b ≤ (2 : ℝ) ^ (k + 2) := by rw [hbdef, pow_succ, pow_succ]; nlinarith [h4]
    calc L = Real.log b := hLdef
      _ ≤ Real.log ((2 : ℝ) ^ (k + 2)) := Real.log_le_log hb0 hble2
      _ = ((k : ℝ) + 2) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
  have hLL_le : LL ≤ Real.log ((k : ℝ) + 2) := by
    have h2 : ((k : ℝ) + 2) * Real.log 2 ≤ (k : ℝ) + 2 := by nlinarith [hlog2_le, hkR]
    calc LL = Real.log L := hLLdef
      _ ≤ Real.log (((k : ℝ) + 2) * Real.log 2) := Real.log_le_log hL0 hL_le
      _ ≤ Real.log ((k : ℝ) + 2) := Real.log_le_log (mul_pos (by linarith) hlog2) h2
  -- product bound: `b·L·LL ≤ 2^k · (2 log2 · (k+2) · log(k+2))`
  have hprod : b * L * LL
      ≤ (2 : ℝ) ^ k * (2 * Real.log 2 * (((k : ℝ) + 2) * Real.log ((k : ℝ) + 2))) := by
    have hstep : b * L * LL
        ≤ (2 : ℝ) ^ (k + 1) * (((k : ℝ) + 2) * Real.log 2) * Real.log ((k : ℝ) + 2) := by
      apply mul_le_mul _ hLL_le hLL0.le
        (mul_nonneg (by positivity) (mul_nonneg (by positivity) hlog2.le))
      · exact mul_le_mul hb_le hL_le hL0.le (by positivity)
    calc b * L * LL
        ≤ (2 : ℝ) ^ (k + 1) * (((k : ℝ) + 2) * Real.log 2) * Real.log ((k : ℝ) + 2) := hstep
      _ = (2 : ℝ) ^ k * (2 * Real.log 2 * (((k : ℝ) + 2) * Real.log ((k : ℝ) + 2))) := by
          rw [pow_succ]; ring
  -- assemble
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
  have hg : (2 : ℝ) ^ k * g₃ (2 ^ k) = (2 : ℝ) ^ k / (b * L * LL) := by
    rw [hLLdef, hLdef, hbdef]; unfold g₃; rw [hcast, mul_one_div]
  have hden1 : 0 < 2 * Real.log 2 * (((k : ℝ) + 2) * Real.log ((k : ℝ) + 2)) :=
    mul_pos (mul_pos (by norm_num) hlog2) (mul_pos (by linarith) hlogk2)
  have hden2 : 0 < b * L * LL := mul_pos (mul_pos hb0 hL0) hLL0
  have hf2 : f₂ k = 1 / (((k : ℝ) + 2) * Real.log ((k : ℝ) + 2)) := rfl
  rw [hg, hf2, one_div_mul_one_div, div_le_div_iff₀ hden1 hden2, one_mul]
  -- goal is now exactly `b·L·LL ≤ 2^k · (2 log2 · (k+2) · log(k+2))`
  exact hprod

private lemma not_summable_g₃ : ¬ Summable g₃ := by
  intro hsum
  -- Cauchy condensation
  have hcond : Summable (fun k : ℕ => (2 : ℝ) ^ k * g₃ (2 ^ k)) :=
    (summable_condensed_iff_of_nonneg g₃_nonneg g₃_antitone).mpr hsum
  -- restrict to the `k ≥ 2` tail where the comparison bound holds
  have hcond2 : Summable (fun k : ℕ => (2 : ℝ) ^ (k + 2) * g₃ (2 ^ (k + 2))) :=
    (summable_nat_add_iff 2).mpr hcond
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hconst_pos : 0 < 1 / (2 * Real.log 2) := div_pos one_pos (by positivity)
  -- dominate the (scaled, shifted) log-harmonic term by the condensed term
  have hcomp : Summable (fun k : ℕ => (1 / (2 * Real.log 2)) * f₂ (k + 2)) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hcond2
    · exact mul_nonneg hconst_pos.le (f₂_nonneg _)
    · exact cond_lower₃ (k + 2) (by omega)
  -- strip the constant and the shift to recover `Summable f₂`, contradicting its divergence
  have hf2shift : Summable (fun k : ℕ => f₂ (k + 2)) := by
    have hm := hcomp.mul_left (2 * Real.log 2)
    refine hm.congr (fun k => ?_)
    have h2l : (2 * Real.log 2) ≠ 0 := by positivity
    rw [← mul_assoc, mul_one_div, div_self h2l, one_mul]
  exact not_summable_f₂ ((summable_nat_add_iff 2).mp hf2shift)

/-- **The iterated-log (second-tier Bertrand) series `∑ 1/(n · log n · log log n)`
    diverges.**  This is the divergence borderline one logarithm deeper than
    `not_summable_one_div_nat_mul_log`, and it formalises the profile
    `f(N) ≍ N/(log N · log log N)` that is `o(N/log N)` yet has a divergent reciprocal
    sum — the exact obstruction to strengthening the weak `RequiredBound` threshold of
    Erdős #3 into a provable sufficient condition.  Together with the convergent
    `summable_one_div_nat_mul_log_mul_const`, it brackets the borderline on the second
    logarithmic axis.  Proof: Cauchy condensation absorbs one logarithm, reducing to the
    first-tier log-harmonic divergence `not_summable_one_div_nat_mul_log`. -/
theorem not_summable_one_div_nat_mul_log_mul_loglog :
    ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) * Real.log n * Real.log (Real.log n))) := by
  intro hsum
  -- shift by three (dropping `n = 0, 1, 2`, where the summand is junk `0`) lands on `g₃`
  have hshift : Summable g₃ := by
    refine ((summable_nat_add_iff 3).mpr hsum).congr (fun n => ?_)
    unfold g₃; push_cast; ring
  exact not_summable_g₃ hshift

end Erdos3Bertrand
