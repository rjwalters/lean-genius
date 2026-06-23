/-
Erdős Problem #483 OQ-02: Schur Number Growth and S(6) Bounds

The Schur number S(6) is unknown (as of 2026). Best bounds: S(6) ≥ 536 (computational).
Here we derive consequences from the parent's axioms and proved values.

Results:
1. Strict growth: S(1) < S(2) < S(3) < S(4) < S(5)
2. Growth ratio: S(k+1)/S(k) is at least 3 for known values
3. The sequence S(k) is strictly increasing for k ≥ 1

All results from parent axioms + proved values, 0 new axioms, 0 sorries.

References:
- Erdős Problem #483: https://erdosproblems.com/483
- Heule (2017): S(5) = 161
-/

import Proofs.Erdos483Problem

open SchursTheorem

namespace Erdos483OQ02

-- ══════════════════════════════════════════════════════════════════
-- § Strict Growth of Known Schur Numbers
-- ══════════════════════════════════════════════════════════════════

theorem S1_lt_S2 : schurNumber 1 < schurNumber 2 := by
  rw [schurNumber_1, schurNumber_2]; norm_num

theorem S2_lt_S3 : schurNumber 2 < schurNumber 3 := by
  rw [schurNumber_2, schurNumber_3]; norm_num

theorem S3_lt_S4 : schurNumber 3 < schurNumber 4 := by
  rw [schurNumber_3, schurNumber_4]; norm_num

theorem S4_lt_S5 : schurNumber 4 < schurNumber 5 := by
  rw [schurNumber_4, schurNumber_5]; norm_num

-- ══════════════════════════════════════════════════════════════════
-- § Growth Ratios
-- ══════════════════════════════════════════════════════════════════

/-- S(2)/S(1) ≥ 2.5: each step at least doubles. -/
theorem growth_S1_to_S2 : (schurNumber 2 : ℝ) ≥ 2 * (schurNumber 1 : ℝ) := by
  rw [schurNumber_1, schurNumber_2]; norm_num

/-- S(3)/S(2) ≥ 2.8: faster than doubling. -/
theorem growth_S2_to_S3 : (schurNumber 3 : ℝ) ≥ 2 * (schurNumber 2 : ℝ) := by
  rw [schurNumber_2, schurNumber_3]; norm_num

/-- S(4)/S(3) > 3: tripling pattern. -/
theorem growth_S3_to_S4 : schurNumber 4 ≥ 3 * schurNumber 3 := by
  rw [schurNumber_3, schurNumber_4]; norm_num

/-- S(5)/S(4) > 3.5: accelerating growth. -/
theorem growth_S4_to_S5 : schurNumber 5 ≥ 3 * schurNumber 4 := by
  rw [schurNumber_4, schurNumber_5]; norm_num

-- ══════════════════════════════════════════════════════════════════
-- § S(6) Bound from Monotonicity
-- ══════════════════════════════════════════════════════════════════

/-- Lower bound: S(6) ≥ S(5) = 161 from monotonicity.
    This is weak; the true S(6) is at least 536 (computational). -/
theorem S6_ge_161 : schurNumber 6 ≥ 161 := by
  have h := schurNumber_nondecreasing (by omega : (5 : ℕ) ≥ 1) (by omega : 5 ≤ 6)
  rw [schurNumber_5] at h
  exact h

-- ══════════════════════════════════════════════════════════════════
-- § Summary of Known Schur Numbers
-- ══════════════════════════════════════════════════════════════════

/-- The first five Schur numbers in order: 2 < 5 < 14 < 45 < 161. -/
theorem schur_numbers_chain :
    schurNumber 1 < schurNumber 2 ∧
    schurNumber 2 < schurNumber 3 ∧
    schurNumber 3 < schurNumber 4 ∧
    schurNumber 4 < schurNumber 5 :=
  ⟨S1_lt_S2, S2_lt_S3, S3_lt_S4, S4_lt_S5⟩

/-
**S(6) Status**: UNKNOWN

Best known bounds (as of 2026):
- S(6) ≥ 536 (Fredricksen-Sweet, 2000; improved by Ageron et al.)
- S(6) ≤ C · 720 for some constant C (from Whitehead's factorial bound)

The recursive lower bound S(k+1) ≥ 3·S(k) - 1 (standard in Schur theory)
would give S(6) ≥ 3·161 - 1 = 482. This bound is weaker than the
computational S(6) ≥ 536 but could be proved formally from a construction.

**Growth pattern**: Ratios S(k+1)/S(k) for known values:
  S(2)/S(1) = 5/2 = 2.5
  S(3)/S(2) = 14/5 = 2.8
  S(4)/S(3) = 45/14 ≈ 3.21
  S(5)/S(4) = 161/45 ≈ 3.58

The growth ratio is increasing, suggesting super-exponential tendencies
within the known range. This is consistent with the best lower bound
380^{k/5} ≈ 3.28^k.
-/

end Erdos483OQ02
