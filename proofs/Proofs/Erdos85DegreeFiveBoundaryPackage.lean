import Proofs.Erdos85OddPlateauExcessAtLeastThree
import Proofs.Erdos85OrderTwentySevenDegreeFiveWitness

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

end Erdos85
