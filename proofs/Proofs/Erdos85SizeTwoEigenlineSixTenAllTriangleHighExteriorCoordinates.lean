import Proofs.Erdos85SizeTwoEigenlineSixTenAllTriangleHighReduction
import Proofs.Erdos85ExteriorPairGraphAdjacency
import Proofs.Erdos85SizeTwoEigenlineSixTenInternalCommonPairs

/-!
# Exterior-pair coordinates on the surviving all-triangle C10 shore

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- On the surviving high C10 shore, the graph-theoretic exterior-pair
relation has exactly offsets `{±1,5}`.  In particular, the ambient cycle
edges at offsets `±1` are retained: they are triangle edges and hence are
not second-order defect edges. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTriangle_high_exteriorPair_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      3 * s x)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (v : ZMod 10 → c.supp) (hvinj : Function.Injective v)
    (hvrange : Set.range v = b.supp)
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (hball : ∀ z : c.supp, z ∈ b.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 0) :
    ∀ i j, (exteriorPairGraph G c.supp).Adj (v i) (v j) ↔
      j - i = 1 ∨ j - i = 5 ∨ j - i = 9 := by
  have hanti :=
    binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTriangle_high_support
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
        v hvinj hvrange hv hball
  have hD : ∀ i j,
      ((secondOrderDefectGraph G).induce c.supp).Adj (v i) (v j) ↔
        j - i = 3 ∨ j - i = 4 ∨ j - i = 6 ∨ j - i = 7 := by
    intro i j
    rw [binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTriangle_defectAdj_iff_antipodal
      G c b hball (v i) (v j)]
    · exact hanti i j
    · rw [← hvrange]
      exact ⟨i, rfl⟩
  intro i j
  by_cases hij : i = j
  · subst j
    constructor
    · intro hadj
      exact ((exteriorPairGraph G c.supp).loopless.irrefl (v i) hadj).elim
    · intro h
      have hfalse : ¬ (i - i = 1 ∨ i - i = 5 ∨ i - i = 9) := by
        intro h'
        have hz : ¬ (((0 : ZMod 10) = (1 : ZMod 10)) ∨
            ((0 : ZMod 10) = (5 : ZMod 10)) ∨
            ((0 : ZMod 10) = (9 : ZMod 10))) := by decide
        exact hz (by simpa only [sub_self] using h')
      exact (hfalse h).elim
  have hvij : v i ≠ v j := fun h => hij (hvinj h)
  have hDij : (secondOrderDefectGraph G).Adj (v i).1 (v j).1 ↔
      j - i = 3 ∨ j - i = 4 ∨ j - i = 6 ∨ j - i = 7 := hD i j
  have hcommon : (∃ z : c.supp,
      G.Adj (v i).1 z.1 ∧ G.Adj (v j).1 z.1) ↔
      j - i = 2 ∨ j - i = 8 := by
    simpa using
      (zmodTen_cycle_internalCommon_iff_offset_two_eight
        (G.induce c.supp) v hvinj hv i j hij)
  rw [exteriorPairGraph_adj_iff_not_defect_and_no_internal_common
    G hfree c (v i) (v j), hDij, hcommon]
  rw [and_iff_right hvij]
  fin_cases i <;> fin_cases j
  all_goals first | contradiction | decide

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTriangle_high_exteriorPair_iff
