import Proofs.Erdos85RamseyPlateau

/-!
# Conditional finite-drop core for Erdős 85

This module contains the reusable order-theoretic implications. It is separate
from `Erdos85FiniteDropCapstone`, the eventual generated certificate endpoint.
-/

namespace Erdos85

theorem not_c4FreeMinDegreeWitness_iff_minDegreeForC4_le
    {n d : ℕ} (hn : 4 ≤ n) :
    ¬ C4FreeMinDegreeWitness n d ↔ minDegreeForC4 n ≤ d := by
  rw [c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hn]
  omega

theorem minDegreeForC4_drop_of_witness_of_no_succ_witness
    {n d : ℕ} (hn : 4 ≤ n)
    (hw : C4FreeMinDegreeWitness n d)
    (hnext : ¬ C4FreeMinDegreeWitness (n + 1) d) :
    minDegreeForC4 (n + 1) < minDegreeForC4 n := by
  have hold : d < minDegreeForC4 n :=
    (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hn).1 hw
  have hnew : minDegreeForC4 (n + 1) ≤ d :=
    (not_c4FreeMinDegreeWitness_iff_minDegreeForC4_le (by omega)).1 hnext
  omega

theorem minDegreeForC4_fortyNine_lt_fortyEight
    (hw48 : C4FreeMinDegreeWitness 48 7)
    (hno49 : ¬ C4FreeMinDegreeWitness 49 7) :
    minDegreeForC4 49 < minDegreeForC4 48 := by
  simpa using minDegreeForC4_drop_of_witness_of_no_succ_witness
    (n := 48) (d := 7) (by norm_num) hw48 hno49

theorem minDegreeForC4_fortyEight_eq_eight
    (hw48 : C4FreeMinDegreeWitness 48 7) :
    minDegreeForC4 48 = 8 := by
  have hlower : 7 < minDegreeForC4 48 :=
    (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 (by norm_num)).1 hw48
  have hupper : minDegreeForC4 48 ≤ 8 :=
    minDegreeForC4_le_of_le_mul_pred (by norm_num) (by norm_num)
  omega

theorem minDegreeForC4_fortyEight_fortyNine_exact
    (hw48 : C4FreeMinDegreeWitness 48 7)
    (hw49 : C4FreeMinDegreeWitness 49 6)
    (hno49 : ¬ C4FreeMinDegreeWitness 49 7) :
    minDegreeForC4 48 = 8 ∧ minDegreeForC4 49 = 7 := by
  refine ⟨minDegreeForC4_fortyEight_eq_eight hw48, ?_⟩
  have hlower : 6 < minDegreeForC4 49 :=
    (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 (by norm_num)).1 hw49
  have hupper : minDegreeForC4 49 ≤ 7 :=
    (not_c4FreeMinDegreeWitness_iff_minDegreeForC4_le (by norm_num)).1 hno49
  omega

theorem consecutiveC4StarPlateauAt_fortyEight
    (hw48 : C4FreeMinDegreeWitness 48 7)
    (hno49 : ¬ C4FreeMinDegreeWitness 49 7) :
    ConsecutiveC4StarPlateauAt 48 41 := by
  have hold : 7 < minDegreeForC4 48 :=
    (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 (by norm_num)).1 hw48
  have hnew : minDegreeForC4 49 ≤ 7 :=
    (not_c4FreeMinDegreeWitness_iff_minDegreeForC4_le (by norm_num)).1 hno49
  constructor
  · intro h
    have hle := (c4StarRamseyAt_iff_threshold (m := 48) (s := 41)
      (by norm_num) (by norm_num)).1 h
    omega
  constructor
  · intro h
    have hle := (c4StarRamseyAt_iff_threshold (m := 48) (s := 42)
      (by norm_num) (by norm_num)).1 h
    omega
  constructor
  · exact (c4StarRamseyAt_iff_threshold (m := 49) (s := 41)
      (by norm_num) (by norm_num)).2 (by omega)
  · exact (c4StarRamseyAt_iff_threshold (m := 49) (s := 42)
      (by norm_num) (by norm_num)).2 (by omega)

end Erdos85
