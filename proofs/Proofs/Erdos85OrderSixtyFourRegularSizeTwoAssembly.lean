import Proofs.Erdos85OrderSixtyFourRegularOutsideFeasibility
import Proofs.Erdos85OrderSixtyFourSizeTwoConcreteHighClosure

/-!
# Regular re-assembly of the size-two eigenline closure

Editor repair step (2) of squad msg 13926: the seven-component
assembly wrappers are vacuous under regularity because their component
count hypothesis contradicts `2·#components ≤ q`.  The theorems below
are their regular counterparts: the four outside feasibility facts come
from `orderSixtyFour_regular_sizeSixteen_outsidePair_feasibility`
(equitable law + C4, no component count), and every downstream terminal
call is unchanged.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The four outside feasibility facts under regularity alone. -/
theorem orderSixtyFour_regular_sizeSixteen_outsidePair_facts
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x : Fin 64, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16) :
    (∀ x : Fin 64,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2) ∧
    Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c) ∧
    Fintype.card {x : Fin 64 // x ∉ c.supp} = 48 ∧
    (exteriorPairGraph G c).edgeSet.ncard = 48 := by
  classical
  obtain ⟨_label, hqcard, hpaircard, hinj, _himage, _hRreg, hRedges,
      _hCreg, _hC4, _hcross⟩ :=
    orderSixtyFour_regular_sizeSixteen_outsidePair_feasibility
      G hfree hreg c hc
  refine ⟨hpaircard, hinj, hqcard, ?_⟩
  have hncard : (exteriorPairGraph G c.supp).edgeSet.ncard =
      (exteriorPairGraph G c.supp).edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  exact hncard.trans hRedges

/-- Regular counterpart of the coordinate `8+8` high-terminal wrapper. -/
theorem orderSixtyFour_regular_eightEight_false_of_high_terminal
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : Fin 64 → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      3 * s x)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 8) (hb : b.supp.ncard = 8) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (h6 : componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 1 →
      componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 6 →
      componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = 6 →
      componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 1 →
      EightEightShoreAllTriangle G c a →
      EightEightShoreAllTriangle G c b → False) :
    False := by
  obtain ⟨hpaircard, hpairinc, houtcard, hRedgesNcard⟩ :=
    orderSixtyFour_regular_sizeSixteen_outsidePair_facts
      G hfree hreg c (by simpa using hc)
  exact binarySquare_regular_sizeTwoPart_eight_eightEight_false_of_high_terminal
    G hfree hreg (by norm_num) c hc s hs_in hs_out hA_in hDs
      a b ha hb hab u v huinj hvinj hurange hvrange hu hv
      hpaircard hpairinc houtcard hRedgesNcard h6

/-- Regular counterpart of the abstract `8+8` high-terminal wrapper. -/
theorem orderSixtyFour_regular_eightEight_false_of_abstract_high_terminal
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : Fin 64 → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      3 * s x)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 8) (hb : b.supp.ncard = 8) (hab : a ≠ b)
    (h6 : componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 1 →
      componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 6 →
      componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = 6 →
      componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 1 →
      EightEightShoreAllTriangle G c a →
      EightEightShoreAllTriangle G c b → False) :
    False := by
  let H := G.induce c.supp
  have hdeg : ∀ x, H.degree x = 2 := by
    intro x
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg (by norm_num) c hc x
  obtain ⟨u, v, huinj, hvinj, hurange, hvrange, hu, hv⟩ :=
    exists_zmodEight_twoComponent_coordinates H hdeg a b ha hb
  exact orderSixtyFour_regular_eightEight_false_of_high_terminal
    G hfree hreg c hc s hs_in hs_out hA_in hDs a b ha hb hab
      u v huinj hvinj hurange hvrange hu hv h6

/-- Regular counterpart of the callback assembly wrapper. -/
theorem orderSixtyFour_regular_sizeTwoEigenline_false_of_terminals
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : Fin 64 → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hsum : ∑ x, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      3 * s x)
    (hHigh : ∀ (a b : (G.induce c.supp).ConnectedComponent), a ≠ b →
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 1 →
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 6 →
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = 6 →
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 1 →
      EightEightShoreAllTriangle G c a →
      EightEightShoreAllTriangle G c b → False) :
    False := by
  obtain ⟨hpaircard, hpairinc, houtcard, hRedgesNcard⟩ :=
    orderSixtyFour_regular_sizeSixteen_outsidePair_facts
      G hfree hreg c (by simpa using hc)
  apply false_of_sizeTwoEigenline_eight_of_stratum_terminals
    G hfree hreg (by norm_num) c hc s hs_in hs_out hsum hA_in
      (by simpa using hDs)
  · intro a b hab hshape
    obtain ⟨ha, hb, _haa, _habq, _hbaq, _hbb⟩ := hshape
    exact binarySquare_regular_sizeTwoPart_eight_sixTen_false
      G hfree hreg (by norm_num) c hc s hs_in hs_out hA_in hDs
        a b hab ha hb hpaircard hpairinc houtcard hRedgesNcard
  · intro a b hab hshape
    obtain ⟨ha, hb, _r, _hr2, _hr7, _haa, _habq, _hbaq, _hbb⟩ := hshape
    exact orderSixtyFour_regular_eightEight_false_of_abstract_high_terminal
      G hfree hreg c hc s hs_in hs_out hA_in hDs a b ha hb hab
        (hHigh a b hab)

/-- Regular counterpart of the no-callback closure. -/
theorem orderSixtyFour_regular_sizeTwoEigenline_false
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : Fin 64 → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hsum : ∑ x, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      3 * s x) : False := by
  obtain ⟨hpaircard, hpairinc, houtcard, hRedgesNcard⟩ :=
    orderSixtyFour_regular_sizeSixteen_outsidePair_facts
      G hfree hreg c (by simpa using hc)
  apply false_of_sizeTwoEigenline_eight_of_stratum_terminals
    G hfree hreg (by norm_num) c hc s hs_in hs_out hsum hA_in
      (by simpa using hDs)
  · intro a b hab hshape
    obtain ⟨ha, hb, _haa, _habq, _hbaq, _hbb⟩ := hshape
    exact binarySquare_regular_sizeTwoPart_eight_sixTen_false
      G hfree hreg (by norm_num) c hc s hs_in hs_out hA_in hDs
        a b hab ha hb hpaircard hpairinc houtcard hRedgesNcard
  · intro a b hab hshape
    obtain ⟨ha, hb, _r, _hr2, _hr7, _haa, _habq, _hbaq, _hbb⟩ := hshape
    apply orderSixtyFour_regular_eightEight_false_of_abstract_high_terminal
      G hfree hreg c hc s hs_in hs_out hA_in hDs a b ha hb hab
    intro _haa hab6 hba6 _hbb _allA _allB
    exact binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_high_false
      G hfree hreg (by norm_num) c hc s hs_in hs_out hA_in hDs
        a b ha hb hab hab6 hba6 hpaircard hpairinc houtcard hRedgesNcard

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_regular_sizeSixteen_outsidePair_facts
#print axioms Erdos85.orderSixtyFour_regular_sizeTwoEigenline_false_of_terminals
#print axioms Erdos85.orderSixtyFour_regular_sizeTwoEigenline_false
