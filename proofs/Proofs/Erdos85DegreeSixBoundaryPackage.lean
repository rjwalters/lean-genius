import Proofs.Erdos85DegreeSixColorSectorSplit
import Proofs.Erdos85PlateauExcessStructure
import Proofs.Erdos85PositiveExcessLocalParity
import Proofs.Erdos85CofinalLowerBound
import Proofs.Erdos85Boza35Witness
import Proofs.Erdos85Boza36Witness
import Proofs.Erdos85Boza37To39Witness

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

end Erdos85
