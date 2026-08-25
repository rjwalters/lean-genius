import Proofs.Erdos85MuNegThreeZeroFiveCrossCountFields
import Proofs.Erdos85MuNegThreeExplicitParameters
import Proofs.Erdos85MuNegFiveCanonicalCrossProfiles

/-! # Cross-profile transport for the honest h305 terminal -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Convert the defect-matrix `(3,2)` cross profile to the exterior-pair
same/opposite split consumed by the corrected owner CNF. -/
theorem h305_crossExteriorSplit_of_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (su sv : ZMod 8 → ℤ)
    (hprofile : MuNegFiveCrossExteriorProfile
      (fun i j ↦ ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
        (u i) (v j)) su sv 3 2) :
    MuNegThreeZeroFiveCrossExteriorSplit
      (exteriorPairGraph G c.supp) u v su sv := by
  classical
  let K := (secondOrderDefectGraph G).induce c.supp
  have hcomp := sizeTwo_distinctCycle_cross_exteriorPair_iff_not_defect
    G hfree c a b hab u v hurange hvrange
  refine ⟨?_, ?_⟩
  · intro i
    let S := (Finset.univ : Finset (ZMod 8)).filter fun j ↦
      (exteriorPairGraph G c.supp).Adj (u i) (v j)
    have htotal : S.card = 3 := by
      simpa [S, K, SimpleGraph.adjMatrix_apply, hcomp i] using
        hprofile.row_total i
    have hsame : (S.filter fun j ↦ sv j = su i).card = 2 := by
      change (((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        (exteriorPairGraph G c.supp).Adj (u i) (v j)).filter
          fun j ↦ sv j = su i).card = 2
      rw [Finset.filter_filter]
      simpa [K, SimpleGraph.adjMatrix_apply, hcomp i, and_comm] using
        hprofile.row_same i
    have hsplit := S.card_filter_add_card_filter_not (fun j ↦ sv j = su i)
    constructor
    · simpa [S, Finset.filter_filter, and_comm] using hsame
    · have hsum : (S.filter fun j ↦ sv j = su i).card +
          (S.filter fun j ↦ sv j ≠ su i).card = S.card := by
        simpa using hsplit
      have : (S.filter fun j ↦ sv j ≠ su i).card = 1 := by omega
      simpa [S, Finset.filter_filter, and_comm] using this
  · intro j
    let S := (Finset.univ : Finset (ZMod 8)).filter fun i ↦
      (exteriorPairGraph G c.supp).Adj (u i) (v j)
    have htotal : S.card = 3 := by
      simpa [S, K, SimpleGraph.adjMatrix_apply, hcomp] using
        hprofile.col_total j
    have hsame : (S.filter fun i ↦ su i = sv j).card = 2 := by
      change (((Finset.univ : Finset (ZMod 8)).filter fun i ↦
        (exteriorPairGraph G c.supp).Adj (u i) (v j)).filter
          fun i ↦ su i = sv j).card = 2
      rw [Finset.filter_filter]
      simpa [K, SimpleGraph.adjMatrix_apply, hcomp, and_comm] using
        hprofile.col_same j
    have hsplit := S.card_filter_add_card_filter_not (fun i ↦ su i = sv j)
    constructor
    · simpa [S, Finset.filter_filter, and_comm] using hsame
    · have hsum : (S.filter fun i ↦ su i = sv j).card +
          (S.filter fun i ↦ su i ≠ sv j).card = S.card := by
        simpa using hsplit
      have : (S.filter fun i ↦ su i ≠ sv j).card = 1 := by omega
      simpa [S, Finset.filter_filter, and_comm] using this

end


end Erdos85

#print axioms Erdos85.h305_crossExteriorSplit_of_profile
