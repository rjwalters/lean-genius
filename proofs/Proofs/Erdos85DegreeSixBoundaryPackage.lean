import Proofs.Erdos85DegreeSixColorSectorSplit
import Proofs.Erdos85PlateauExcessStructure
import Proofs.Erdos85PositiveExcessLocalParity
import Proofs.Erdos85CofinalLowerBound
import Proofs.Erdos85Boza35Witness
import Proofs.Erdos85Boza36Witness
import Proofs.Erdos85Boza37To39Witness
import Proofs.Erdos85Boza48DeletionBand
import Proofs.Erdos85OrderFortyNineDegreeSixWitness
import Proofs.Erdos85ER7DeletionBand

/-!
# Degree-six boundary package

This file exports the graph-facing degree-six exact-boundary contradiction in
the threshold and plateau-core forms used by the global Erdős--85 assembly.
-/

namespace Erdos85

open SimpleGraph

/-- The order-33 forcing threshold is at most six. -/
theorem minDegreeForC4_thirtyThree_le_six :
    minDegreeForC4 33 ≤ 6 := by
  by_contra hnot
  have hlt : 6 < minDegreeForC4 33 := by omega
  obtain ⟨G, hdec, hmin, hfree⟩ :=
    (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 (by norm_num)).2 hlt
  letI : DecidableRel G.Adj := hdec
  exact hfree (containsC4_of_degreeSix_exact_boundary G hmin (by simp))

/-- A degree-six plateau core cannot occur at its exact second-order
boundary order. -/
theorem not_C4PlateauCore_thirtyThree_six :
    ¬ C4PlateauCore 33 6 := by
  rintro ⟨G, hdec, hmin, hfree, _hcover, _hnext⟩
  letI : DecidableRel G.Adj := hdec
  exact hfree (containsC4_of_degreeSix_exact_boundary G hmin.ge (by simp))

/-- Complete assembly interface for the degree-six exact boundary. -/
theorem degreeSix_secondOrder_boundary_package :
    minDegreeForC4 33 ≤ 6 ∧ ¬ C4PlateauCore 33 6 :=
  ⟨minDegreeForC4_thirtyThree_le_six,
    not_C4PlateauCore_thirtyThree_six⟩

/-- Below the square order, the degree-six plateau band has only three
remaining orders.  The first-order alternative gives `32`; positive excess
has `e ≤ 2`, and the exact-boundary result removes `e = 0` (order `33`). -/
theorem C4PlateauCore.degreeSix_order_eq_thirtyTwo_or_thirtyFour_or_thirtyFive
    {m : ℕ} (hm : 4 ≤ m) (hcore : C4PlateauCore m 6)
    (hsize : m < 36) :
    m = 32 ∨ m = 34 ∨ m = 35 := by
  rcases hcore.firstOrder_or_positiveExcessData hm (by norm_num) hsize with
    hfirst | ⟨e, hdata⟩
  · left
    omega
  · have hme := hdata.1
    have he := hdata.2
    have hmne : m ≠ 33 := by
      intro hm33
      apply not_C4PlateauCore_thirtyThree_six
      simpa [hm33] using hcore
    omega

/-- A degree-six plateau core at order 34 supplies the exact excess-one
operator package, with no remaining cardinality ambiguity. -/
theorem C4PlateauCore.degreeSix_thirtyFour_positiveExcessOne
    (hcore : C4PlateauCore 34 6) :
    PositiveExcessPlateauData 34 6 1 := by
  rcases hcore.firstOrder_or_positiveExcessData
      (by norm_num) (by norm_num) (by norm_num) with
    hfirst | ⟨e, hdata⟩
  · norm_num at hfirst
  · have hme := hdata.1
    have he : e = 1 := by omega
    simpa [he] using hdata

/-- The order-34 degree-six plateau case is impossible because the checked
Boza/House-of-Graphs witness at order 35 contradicts one-step nonextension. -/
theorem not_C4PlateauCore_thirtyFour_six : ¬ C4PlateauCore 34 6 := by
  rintro ⟨_G, _hdec, _hmin, _hfree, _hcover, hnext⟩
  exact boza35Graph_not_containsC4
    (hnext boza35Graph inferInstance (by
      apply SimpleGraph.le_minDegree_of_forall_le_degree
      intro v
      rw [boza35Graph_degree v]))

/-- A degree-six plateau core at order 35 supplies the exact excess-two
operator package, with no remaining cardinality ambiguity. -/
theorem C4PlateauCore.degreeSix_thirtyFive_positiveExcessTwo
    (hcore : C4PlateauCore 35 6) :
    PositiveExcessPlateauData 35 6 2 := by
  rcases hcore.firstOrder_or_positiveExcessData
      (by norm_num) (by norm_num) (by norm_num) with
    hfirst | ⟨e, hdata⟩
  · norm_num at hfirst
  · have hme := hdata.1
    have he : e = 2 := by omega
    simpa [he] using hdata

/-- Concrete color-sector interface for a hypothetical order-35 degree-six
plateau core.  Its four-regular defect graph splits locally only as
`(T,C) = (0,4)`, `(2,2)`, or `(4,0)`, and the first mixed trace counts the
two nonzero triangle-free sectors with weights two and four. -/
theorem C4PlateauCore.degreeSix_thirtyFive_exists_excessTwo_colorData
    (hcore : C4PlateauCore 35 6) :
    ∃ (G : SimpleGraph (Fin 35)) (_ : DecidableRel G.Adj)
        (_ : DecidableRel (antipodalGraph G).Adj)
        (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
      ¬ containsC4 (Fin 35) G ∧
      (∀ x, G.degree x = 6) ∧
      (∀ x, (secondOrderDefectGraph G).degree x = 4) ∧
      (∀ x,
        ((triangleFreeEdgeGraph G).degree x = 0 ∧
            (antipodalGraph G).degree x = 4) ∨
          ((triangleFreeEdgeGraph G).degree x = 2 ∧
            (antipodalGraph G).degree x = 2) ∨
          ((triangleFreeEdgeGraph G).degree x = 4 ∧
            (antipodalGraph G).degree x = 0)) ∧
      Matrix.trace (G.adjMatrix ℤ *
          (secondOrderDefectGraph G).adjMatrix ℤ) =
        2 * ((Finset.univ.filter fun x : Fin 35 =>
          (triangleFreeEdgeGraph G).degree x = 2).card : ℤ) +
        4 * ((Finset.univ.filter fun x : Fin 35 =>
          (triangleFreeEdgeGraph G).degree x = 4).card : ℤ) ∧
      ∀ (H : SimpleGraph (Fin 36)) (_ : DecidableRel H.Adj),
        6 ≤ H.minDegree → containsC4 (Fin 36) H := by
  rcases hcore.degreeSix_thirtyFive_positiveExcessTwo with
    ⟨_hcard, _he, G, hdec, hfree, hreg, hDreg, _hsq, _hcomm, hnext⟩
  letI : DecidableRel G.Adj := hdec
  letI : DecidableRel (antipodalGraph G).Adj := Classical.decRel _
  letI : DecidableRel (triangleFreeEdgeGraph G).Adj := Classical.decRel _
  refine ⟨G, hdec, inferInstance, inferInstance,
    hfree, hreg, hDreg, ?_, ?_, hnext⟩
  · intro x
    exact excessTwo_even_color_degree_classification
      G hfree (by norm_num) hreg (by norm_num) x
  · exact trace_adjMatrix_mul_secondOrderDefect_even_excessTwo
      G hfree (by norm_num) hreg (by norm_num)

/-- The order-35 degree-six plateau case is impossible because the checked
Boza/House-of-Graphs witness already supplies a `C₄`-free minimum-degree-six
graph at order 36, contradicting one-step nonextension. -/
theorem not_C4PlateauCore_thirtyFive_six : ¬ C4PlateauCore 35 6 := by
  intro hcore
  rcases hcore.degreeSix_thirtyFive_exists_excessTwo_colorData with
    ⟨_G, _hdec, _hantiDec, _htriangleDec, _hfree, _hreg, _hDreg,
      _hcolors, _htrace, hnext⟩
  exact boza36Graph_not_containsC4
    (hnext boza36Graph inferInstance (by
      apply SimpleGraph.le_minDegree_of_forall_le_degree
      intro v
      rw [boza36Graph_degree v]))

/-- All positive-excess degree-six plateau cores below the square order are
impossible.  The only remaining degree-six case in this band is the
first-order value `m = 32`. -/
theorem C4PlateauCore.degreeSix_order_eq_thirtyTwo
    {m : ℕ} (hm : 4 ≤ m) (hcore : C4PlateauCore m 6)
    (hsize : m < 36) :
    m = 32 := by
  rcases hcore.degreeSix_order_eq_thirtyTwo_or_thirtyFour_or_thirtyFive
      hm hsize with h32 | h34 | h35
  · exact h32
  · subst m
    exact (not_C4PlateauCore_thirtyFour_six hcore).elim
  · subst m
    exact (not_C4PlateauCore_thirtyFive_six hcore).elim

/-- The remaining first-order degree-six case is excluded by the parity-free
second strict Moore bound. -/
theorem not_C4PlateauCore_thirtyTwo_six : ¬ C4PlateauCore 32 6 := by
  rintro ⟨G, hdec, hmin, hfree, _hcover, _hnext⟩
  letI : DecidableRel G.Adj := hdec
  exact hfree (containsC4_of_firstOrder G (by norm_num) hmin.ge (by norm_num))

/-- Complete degree-six plateau exclusion below the square order. -/
theorem not_C4PlateauCore_degreeSix_of_lt_thirtySix
    {m : ℕ} (hm : 4 ≤ m) (hsize : m < 36) :
    ¬ C4PlateauCore m 6 := by
  intro hcore
  have hm32 := hcore.degreeSix_order_eq_thirtyTwo hm hsize
  subst m
  exact not_C4PlateauCore_thirtyTwo_six hcore

/-- The five checked Boza graphs fill the complete degree-six witness interval
from order 35 through order 39. -/
theorem degreeSix_witness_thirtyFive_add
    (j : ℕ) (hj : j ≤ 4) :
    C4FreeMinDegreeWitness (35 + j) 6 := by
  interval_cases j <;> norm_num
  · exact boza35_degreeSix_witness
  · exact boza36_degreeSix_witness
  · exact boza37_degreeSix_witness
  · exact boza38_degreeSix_witness
  · exact boza39_degreeSix_witness

/-- Five consecutive witness orders reduce the degree-six conductor from the
generic quadratic bound `1296` to `315`. -/
theorem degreeSix_witness_of_threeHundredFifteen_le
    {n : ℕ} (hn : 315 ≤ n) :
    C4FreeMinDegreeWitness n 6 := by
  apply eventually_witness_of_interval
      (A := 35) (L := 4) (d := 6) (by norm_num) (by norm_num)
      degreeSix_witness_thirtyFive_add n
  norm_num at hn ⊢
  exact hn

/-- Every degree-six plateau core occurs before the improved order-315
conductor. -/
theorem C4PlateauCore.degreeSix_order_succ_lt_threeHundredFifteen
    {m : ℕ} (hcore : C4PlateauCore m 6) :
    m + 1 < 315 := by
  by_contra hnot
  have hw := degreeSix_witness_of_threeHundredFifteen_le (by omega : 315 ≤ m + 1)
  rcases hw with ⟨H, hdec, hmin, hfree⟩
  rcases hcore with ⟨_G, _hGdec, _hGmin, _hGfree, _hcover, hnext⟩
  exact hfree (hnext H hdec hmin)

/-- Combined localization for the still-unresolved degree-six regime. -/
theorem C4PlateauCore.degreeSix_remaining_order_window
    {m : ℕ} (hm : 4 ≤ m) (hcore : C4PlateauCore m 6) :
    36 ≤ m ∧ m < 314 := by
  constructor
  · by_contra hnot
    exact not_C4PlateauCore_degreeSix_of_lt_thirtySix hm (by omega) hcore
  · have hlt := hcore.degreeSix_order_succ_lt_threeHundredFifteen
    omega

/-- The Boza witnesses and safe deletions fill every degree-six witness order
from 35 through 48. -/
theorem degreeSix_witness_thirtyFive_add_of_le_thirteen
    (j : ℕ) (hj : j ≤ 13) :
    C4FreeMinDegreeWitness (35 + j) 6 := by
  interval_cases j <;> norm_num
  · exact boza35_degreeSix_witness
  · exact boza36_degreeSix_witness
  · exact boza37_degreeSix_witness
  · exact boza38_degreeSix_witness
  · exact boza39_degreeSix_witness
  · exact boza48_delete8_degreeSix_witness
  · exact boza48_delete7_degreeSix_witness
  · exact boza48_delete6_degreeSix_witness
  · exact boza48_delete5_degreeSix_witness
  · exact boza48_delete4_degreeSix_witness
  · exact boza48_delete3_degreeSix_witness
  · exact boza48_delete2_degreeSix_witness
  · exact boza48_delete1_degreeSix_witness
  · exact boza48_degreeSeven_witness.mono_degree (by norm_num)

/-- The fourteen-order witness interval gives the sharp conductor bound used
by the degree-six plateau localization: every order at least 105 works. -/
theorem degreeSix_witness_of_oneHundredFive_le
    {n : ℕ} (hn : 105 ≤ n) :
    C4FreeMinDegreeWitness n 6 := by
  apply eventually_witness_of_interval
      (A := 35) (L := 13) (d := 6) (by norm_num) (by norm_num)
      degreeSix_witness_thirtyFive_add_of_le_thirteen n
  norm_num at hn ⊢
  exact hn

/-- Improved complete localization of every degree-six plateau core. -/
theorem C4PlateauCore.degreeSix_order_succ_lt_oneHundredFive
    {m : ℕ} (hcore : C4PlateauCore m 6) :
    m + 1 < 105 := by
  by_contra hnot
  have hw := degreeSix_witness_of_oneHundredFive_le (by omega : 105 ≤ m + 1)
  rcases hw with ⟨H, hdec, hmin, hfree⟩
  rcases hcore with ⟨_G, _hGdec, _hGmin, _hGfree, _hcover, hnext⟩
  exact hfree (hnext H hdec hmin)

/-- After all checked constructions and the sub-square contradiction, only
the finite degree-six order window 36 through 103 can still contain a core. -/
theorem C4PlateauCore.degreeSix_sharp_remaining_order_window
    {m : ℕ} (hm : 4 ≤ m) (hcore : C4PlateauCore m 6) :
    36 ≤ m ∧ m < 104 := by
  constructor
  · by_contra hnot
    exact not_C4PlateauCore_degreeSix_of_lt_thirtySix hm (by omega) hcore
  · have hlt := hcore.degreeSix_order_succ_lt_oneHundredFive
    omega

/-- The order-49 polarity deletion and the `ER(7)` deletion family extend the
continuous degree-six witness interval through order 57. -/
theorem degreeSix_witness_thirtyFive_add_of_le_twentyTwo
    (j : ℕ) (hj : j ≤ 22) :
    C4FreeMinDegreeWitness (35 + j) 6 := by
  interval_cases j <;> norm_num
  · exact boza35_degreeSix_witness
  · exact boza36_degreeSix_witness
  · exact boza37_degreeSix_witness
  · exact boza38_degreeSix_witness
  · exact boza39_degreeSix_witness
  · exact boza48_delete8_degreeSix_witness
  · exact boza48_delete7_degreeSix_witness
  · exact boza48_delete6_degreeSix_witness
  · exact boza48_delete5_degreeSix_witness
  · exact boza48_delete4_degreeSix_witness
  · exact boza48_delete3_degreeSix_witness
  · exact boza48_delete2_degreeSix_witness
  · exact boza48_delete1_degreeSix_witness
  · exact boza48_degreeSeven_witness.mono_degree (by norm_num)
  · exact orderFortyNine_degreeSix_witness
  · exact er7_delete7_degreeSix_witness
  · exact er7_delete6_degreeSix_witness
  · exact er7_delete5_degreeSix_witness
  · exact er7_delete4_degreeSix_witness
  · exact er7_delete3_degreeSix_witness
  · exact er7_delete2_degreeSix_witness
  · exact er7_delete1_degreeSix_witness
  · exact er7_degreeSix_witness

/-- The 23-order witness interval proves existence at every order at least 70. -/
theorem degreeSix_witness_of_seventy_le
    {n : ℕ} (hn : 70 ≤ n) :
    C4FreeMinDegreeWitness n 6 := by
  apply eventually_witness_of_interval
      (A := 35) (L := 22) (d := 6) (by norm_num) (by norm_num)
      degreeSix_witness_thirtyFive_add_of_le_twentyTwo n
  norm_num at hn ⊢
  exact hn

/-- Final construction-driven localization currently available for degree
six: every plateau core precedes order 70. -/
theorem C4PlateauCore.degreeSix_order_succ_lt_seventy
    {m : ℕ} (hcore : C4PlateauCore m 6) :
    m + 1 < 70 := by
  by_contra hnot
  have hw := degreeSix_witness_of_seventy_le (by omega : 70 ≤ m + 1)
  rcases hw with ⟨H, hdec, hmin, hfree⟩
  rcases hcore with ⟨_G, _hGdec, _hGmin, _hGfree, _hcover, hnext⟩
  exact hfree (hnext H hdec hmin)

/-- Only the 33 degree-six orders from 36 through 68 remain after combining
the structural sub-square kill with the polarity witness interval. -/
theorem C4PlateauCore.degreeSix_final_remaining_order_window
    {m : ℕ} (hm : 4 ≤ m) (hcore : C4PlateauCore m 6) :
    36 ≤ m ∧ m < 69 := by
  constructor
  · by_contra hnot
    exact not_C4PlateauCore_degreeSix_of_lt_thirtySix hm (by omega) hcore
  · have hlt := hcore.degreeSix_order_succ_lt_seventy
    omega

end Erdos85
