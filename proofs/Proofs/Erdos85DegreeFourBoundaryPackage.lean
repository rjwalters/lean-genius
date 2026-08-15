import Proofs.Erdos85DegreeFourWitnessBand

/-!
# Degree-four plateau package

The strict Moore bound localizes a degree-four plateau to order at least 15.
The already certified exact values `f(15)=...=f(21)=5` exclude orders 15--20,
and the cofinal degree-four witness theorem excludes every later order.
-/

namespace Erdos85

/-- **Complete degree-four plateau exclusion.** -/
theorem not_C4PlateauCore_degreeFour
    {m : ℕ} (hm : 4 ≤ m) :
    ¬ C4PlateauCore m 4 := by
  intro hcore
  have hlower : 15 ≤ m := by
    have := hcore.second_strict_moore_lower (by norm_num)
    norm_num at this
    exact this
  by_cases h21 : m < 21
  · have hbounds := hcore.threshold_bounds hm
    interval_cases m <;>
      norm_num [minDegreeForC4_fifteen, minDegreeForC4_sixteen,
        minDegreeForC4_seventeen, minDegreeForC4_eighteen,
        minDegreeForC4_nineteen, minDegreeForC4_twenty,
        minDegreeForC4_twentyone] at hbounds
  · have hw := degreeFour_witness_of_twentyOne_le (n := m + 1) (by omega)
    rcases hw with ⟨H, hdec, hmin, hfree⟩
    rcases hcore with ⟨_G, _hGdec, _hGmin, _hGfree, _hcover, hnext⟩
    exact hfree (hnext H hdec hmin)

end Erdos85
