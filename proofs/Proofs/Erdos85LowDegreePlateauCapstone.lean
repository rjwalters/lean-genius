import Proofs.Erdos85DegreeFourBoundaryPackage

/-!
# Low-degree plateau capstone

The exact table through order 21 and the cofinal degree-four construction
dispose of degrees two and three.  Together with the dedicated degree-four,
degree-five, and degree-six packages, every surviving plateau core has degree
at least seven.
-/

namespace Erdos85

private theorem no_smallTable_plateau_degree
    {m d : ℕ} (hm : 4 ≤ m) (h21 : m < 21)
    (hcore : C4PlateauCore m d) (hd : d = 2 ∨ d = 3) : False := by
  have hbounds := hcore.threshold_bounds hm
  rcases hd with rfl | rfl <;>
    interval_cases m <;>
    norm_num [minDegreeForC4_four, minDegreeForC4_five,
      minDegreeForC4_six, minDegreeForC4_seven, minDegreeForC4_eight,
      minDegreeForC4_nine, minDegreeForC4_ten, minDegreeForC4_eleven,
      minDegreeForC4_twelve, minDegreeForC4_thirteen,
      minDegreeForC4_fourteen, minDegreeForC4_fifteen,
      minDegreeForC4_sixteen, minDegreeForC4_seventeen,
      minDegreeForC4_eighteen, minDegreeForC4_nineteen,
      minDegreeForC4_twenty, minDegreeForC4_twentyone] at hbounds

theorem not_C4PlateauCore_degreeTwo
    {m : ℕ} (hm : 4 ≤ m) : ¬ C4PlateauCore m 2 := by
  intro hcore
  by_cases h21 : m < 21
  · exact no_smallTable_plateau_degree hm h21 hcore (Or.inl rfl)
  · have hw := (degreeFour_witness_of_twentyOne_le (n := m + 1) (by omega)).mono_degree
        (by norm_num : 2 ≤ 4)
    rcases hw with ⟨H, hdec, hmin, hfree⟩
    rcases hcore with ⟨_G, _hGdec, _hGmin, _hGfree, _hcover, hnext⟩
    exact hfree (hnext H hdec hmin)

theorem not_C4PlateauCore_degreeThree
    {m : ℕ} (hm : 4 ≤ m) : ¬ C4PlateauCore m 3 := by
  intro hcore
  by_cases h21 : m < 21
  · exact no_smallTable_plateau_degree hm h21 hcore (Or.inr rfl)
  · have hw := (degreeFour_witness_of_twentyOne_le (n := m + 1) (by omega)).mono_degree
        (by norm_num : 3 ≤ 4)
    rcases hw with ⟨H, hdec, hmin, hfree⟩
    rcases hcore with ⟨_G, _hGdec, _hGmin, _hGfree, _hcover, hnext⟩
    exact hfree (hnext H hdec hmin)

/-- Every plateau core at a nondegenerate order has degree at least seven. -/
theorem C4PlateauCore.seven_le_degree
    {m d : ℕ} (hm : 4 ≤ m) (hcore : C4PlateauCore m d) : 7 ≤ d := by
  have htwo := hcore.two_le_degree hm
  by_contra hseven
  have hd : d ≤ 6 := by omega
  interval_cases d
  · exact not_C4PlateauCore_degreeTwo hm hcore
  · exact not_C4PlateauCore_degreeThree hm hcore
  · exact not_C4PlateauCore_degreeFour hm hcore
  · exact not_C4PlateauCore_degreeFive hm hcore
  · exact not_C4PlateauCore_degreeSix hm hcore

end Erdos85
