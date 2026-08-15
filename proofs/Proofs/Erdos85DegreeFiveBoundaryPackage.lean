import Proofs.Erdos85OddPlateauExcessAtLeastThree
import Proofs.Erdos85OrderTwentySevenDegreeFiveWitness
import Proofs.Erdos85DegreeFiveWitnessBand
import Proofs.Erdos85DegreeSixBoundaryPackage

/-!
# Degree-five plateau package

The odd-excess theory already makes the entire sub-square degree-five band
empty: positive excess would have to be at least three and at most one.
The checked order-27 graph begins the construction-facing exclusion above
the square order.
-/

namespace Erdos85

/-- No degree-five plateau core lies below the square order. -/
theorem not_C4PlateauCore_degreeFive_of_lt_twentyFive
    {m : ℕ} (hm : 4 ≤ m) (hsize : m < 25) :
    ¬ C4PlateauCore m 5 := by
  intro hcore
  obtain ⟨e, _heOdd, heLower, hdata⟩ :=
    hcore.exists_odd_positiveExcessData_three_le
      hm (by norm_num) (by norm_num) hsize
  have heUpper := hdata.2
  omega

/-- The checked order-27 witness rules out a degree-five core at order 26. -/
theorem not_C4PlateauCore_twentySix_five : ¬ C4PlateauCore 26 5 := by
  rintro ⟨_G, _hGdec, _hGmin, _hGfree, _hcover, hnext⟩
  rcases orderTwentySeven_degreeFive_witness with ⟨H, hdec, hmin, hfree⟩
  exact hfree (hnext H hdec hmin)

/-- Explicit degree-five witnesses fill every order from 26 through 34. -/
theorem degreeFive_witness_twentySix_add
    (j : ℕ) (hj : j ≤ 8) :
    C4FreeMinDegreeWitness (26 + j) 5 := by
  interval_cases j <;> norm_num
  · exact er5_delete5_degreeFive_witness
  · exact orderTwentySeven_degreeFive_witness
  · exact er5_delete3_degreeFive_witness
  · exact er7_deleteTo29_degreeFive_witness
  · exact er5_delete1_degreeFive_witness
  · exact er5_degreeFive_witness
  · exact er7_deleteTo32_degreeFive_witness
  · exact er7_deleteTo33_degreeFive_witness
  · exact er7_deleteTo34_degreeFive_witness

/-- Every order at least 26 carries a degree-five witness; from order 35 on,
this is inherited from the completed degree-six construction. -/
theorem degreeFive_witness_of_twentySix_le
    {n : ℕ} (hn : 26 ≤ n) :
    C4FreeMinDegreeWitness n 5 := by
  by_cases h35 : n < 35
  · let j := n - 26
    have hj : j ≤ 8 := by dsimp [j]; omega
    have hnj : 26 + j = n := by dsimp [j]; omega
    rw [← hnj]
    exact degreeFive_witness_twentySix_add j hj
  · exact (degreeSix_witness_of_thirtyFive_le (by omega)).mono_degree (by norm_num)

/-- **Complete degree-five plateau exclusion.** -/
theorem not_C4PlateauCore_degreeFive
    {m : ℕ} (hm : 4 ≤ m) :
    ¬ C4PlateauCore m 5 := by
  intro hcore
  by_cases h25 : m < 25
  · exact not_C4PlateauCore_degreeFive_of_lt_twentyFive hm h25 hcore
  · have hw := degreeFive_witness_of_twentySix_le (n := m + 1) (by omega)
    rcases hw with ⟨H, hdec, hmin, hfree⟩
    rcases hcore with ⟨_G, _hGdec, _hGmin, _hGfree, _hcover, hnext⟩
    exact hfree (hnext H hdec hmin)

end Erdos85
