import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Proofs.AmgmInequalityOQ03
import Proofs.PowerMeanCrossZeroOQ

/-
# Full Power Mean Monotonicity: M_r ≤ M_s for All r ≤ s

## Open Question (cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02-oq-01)

Prove the complete power mean chain inequality: for weighted power means,
M_{r} ≤ M_{s} holds for all r ≤ s (r, s ≠ 0).

## What This Proves

**Main theorem**: `power_mean_monotone` — for any weighted power means with positive
weights summing to 1 and positive reals, weightedPowerMean(r) ≤ weightedPowerMean(s)
whenever r ≤ s (and r, s ≠ 0). 0 sorries, 0 axioms.

## Proof Strategy

Three partial results already exist in the gallery:
- `power_mean_monotone_pos` (AmgmInequalityOQ03): M_r ≤ M_s for 0 < r ≤ s
- `power_mean_monotone_neg` (AmgmInequalityOQ03): M_r ≤ M_s for r ≤ s < 0
- `power_mean_monotone_crossing_zero` (PowerMeanCrossZeroOQ): M_r ≤ M_s for r < 0 < s

**Unification by case analysis**: Given r ≤ s (both ≠ 0):
- Case r > 0: then s > 0 too → apply pos case
- Case r < 0 and s < 0: apply neg case (r ≤ s < 0)
- Case r < 0 and s > 0: apply crossing-zero case

These three cases are exhaustive (since r = 0 or s = 0 is excluded).

## Gallery Position

This completes the weighted power mean monotonicity story:
- AmgmInequalityOQ03.lean: proved the pos and neg cases
- PowerMeanCrossZeroOQ.lean: proved the crossing-zero case
- PowerMeanMonotoneOQ.lean (this file): unifies all three cases

Together: M_r is a monotone function of r for all r ≠ 0.

## Prerequisites

- AmgmInequalityOQ03.lean: power_mean_monotone_pos, power_mean_monotone_neg
- PowerMeanCrossZeroOQ.lean: power_mean_monotone_crossing_zero
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace PowerMeanMonotone

open Real Finset PowerMeanCrossZero

variable {ι : Type*} (s : Finset ι) (w z : ι → ℝ)

-- ============================================================
-- § 1: The Unified Monotonicity Theorem
-- ============================================================

/-- **Full Power Mean Monotonicity**: weightedPowerMean(r) ≤ weightedPowerMean(s) for r ≤ s.

    This unifies the three partial results in the gallery:
    - AmgmInequalityOQ03.power_mean_monotone_pos (0 < r ≤ s)
    - AmgmInequalityOQ03.power_mean_monotone_neg (r ≤ s < 0)
    - PowerMeanCrossZeroOQ.power_mean_monotone_crossing_zero (r < 0 < s)

    Proof: Case analysis on the signs of r and s.
    Since r ≠ 0, s ≠ 0, and r ≤ s, exactly one of the three partial cases applies. -/
theorem power_mean_monotone
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    {r t : ℝ} (hr : r ≠ 0) (ht : t ≠ 0) (hrt : r ≤ t) :
    weightedPowerMean s w z r hr ≤ weightedPowerMean s w z t ht := by
  rcases lt_trichotomy r 0 with hr_neg | hr_zero | hr_pos
  · -- Case: r < 0
    rcases lt_trichotomy t 0 with ht_neg | ht_zero | ht_pos
    · -- Subcase: t < 0 (both negative, r ≤ t < 0)
      exact power_mean_monotone_neg s w z hw hw' hz hrt ht_neg hr ht
    · -- Subcase: t = 0, impossible
      exact absurd ht_zero ht
    · -- Subcase: t > 0 (crossing zero)
      exact power_mean_monotone_crossing_zero s w z hw hw' hz hr_neg ht_pos hr ht
  · -- Case: r = 0, impossible
    exact absurd hr_zero hr
  · -- Case: r > 0 (then t > 0 too since r ≤ t)
    have ht_pos : 0 < t := lt_of_lt_of_le hr_pos hrt
    exact power_mean_monotone_pos s w z hw hw' hz hr_pos hrt hr ht

-- ============================================================
-- § 2: Corollaries
-- ============================================================

/-- **Reflexivity**: M_r ≤ M_r (trivial). -/
theorem power_mean_le_self
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    {r : ℝ} (hr : r ≠ 0) :
    weightedPowerMean s w z r hr ≤ weightedPowerMean s w z r hr :=
  le_refl _

/-- **HM ≤ AM**: The harmonic mean is at most the arithmetic mean.

    Special case: r = -1, t = 1. -/
theorem hm_le_am
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) :
    weightedPowerMean s w z (-1) (by norm_num) ≤
    weightedPowerMean s w z 1 (by norm_num) :=
  power_mean_monotone s w z hw hw' hz (by norm_num) (by norm_num) (by norm_num)

/-- **HM ≤ QM**: The harmonic mean is at most the quadratic mean.

    Special case: r = -1, t = 2. -/
theorem hm_le_qm
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) :
    weightedPowerMean s w z (-1) (by norm_num) ≤
    weightedPowerMean s w z 2 (by norm_num) :=
  power_mean_monotone s w z hw hw' hz (by norm_num) (by norm_num) (by norm_num)

/-- **AM ≤ QM**: The arithmetic mean is at most the quadratic mean.

    Special case: r = 1, t = 2. -/
theorem am_le_qm
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) :
    weightedPowerMean s w z 1 (by norm_num) ≤
    weightedPowerMean s w z 2 (by norm_num) :=
  power_mean_monotone s w z hw hw' hz (by norm_num) (by norm_num) (by norm_num)

/-- **M_{-2} ≤ M_{-1}**: Power means of order -2 and -1. -/
theorem power_mean_neg2_le_neg1
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) :
    weightedPowerMean s w z (-2) (by norm_num) ≤
    weightedPowerMean s w z (-1) (by norm_num) :=
  power_mean_monotone s w z hw hw' hz (by norm_num) (by norm_num) (by norm_num)

/-- **M_r ≤ M_{2r} for r > 0**: Power means grow with exponent. -/
theorem power_mean_le_double_exp
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    {r : ℝ} (hr : 0 < r) :
    weightedPowerMean s w z r (ne_of_gt hr) ≤
    weightedPowerMean s w z (2 * r) (by positivity) :=
  power_mean_monotone s w z hw hw' hz (ne_of_gt hr) (by positivity) (by linarith)

/-- **M_r ≤ M_s ≤ M_t (transitivity)**: Power mean chain inequality. -/
theorem power_mean_chain
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    {r u t : ℝ} (hr : r ≠ 0) (hu : u ≠ 0) (ht : t ≠ 0)
    (hru : r ≤ u) (hut : u ≤ t) :
    weightedPowerMean s w z r hr ≤ weightedPowerMean s w z t ht :=
  le_trans
    (power_mean_monotone s w z hw hw' hz hr hu hru)
    (power_mean_monotone s w z hw hw' hz hu ht hut)

-- ============================================================
-- § 3: Connection to the Full Power Mean Chain
-- ============================================================

/-- **HM ≤ GM ≤ AM ≤ QM**: The classical power mean chain via power mean monotonicity.

    This connects to PowerMeanCrossZeroOQ.hm_le_gm_le_am_via_power_means
    and adds the QM step. -/
theorem hm_le_gm_le_am_le_qm
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) :
    weightedPowerMean s w z (-1) (by norm_num) ≤
    weightedGeomMean s w z ∧
    weightedGeomMean s w z ≤ weightedPowerMean s w z 1 (by norm_num) ∧
    weightedPowerMean s w z 1 (by norm_num) ≤
    weightedPowerMean s w z 2 (by norm_num) := by
  refine ⟨?_, ?_, ?_⟩
  · exact power_mean_le_geom_mean_neg s w z hw hw' hz (by norm_num) (by norm_num)
  · exact geom_mean_le_power_mean_pos s w z hw hw' hz (by norm_num) (by norm_num)
  · exact power_mean_monotone s w z hw hw' hz (by norm_num) (by norm_num) (by norm_num)

end PowerMeanMonotone
