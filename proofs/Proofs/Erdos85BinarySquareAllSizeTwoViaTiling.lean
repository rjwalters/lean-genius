import Proofs.Erdos85BinarySquareSizeTwoRoutingRegularity
import Proofs.Erdos85BinarySquareCrossRoutingSymmetry

/-! # Uniform via-color tilings in the all-size-two stratum -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Ordered endpoint pairs whose unique common neighbor lies in component
`via`.  Sigma coordinates make the row-fiber census definitionally visible. -/
def crossRoutingViaFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {source target : (secondOrderDefectGraph G).ConnectedComponent}
    (hst : source ≠ target)
    (via : (secondOrderDefectGraph G).ConnectedComponent) :
    Finset (Σ _ : source.supp, target.supp) :=
  Finset.univ.sigma fun x => (Finset.univ : Finset target.supp).filter fun z =>
    via = crossIntermediateComponent G hfree hst x z

/-- Different via-colors occupy disjoint endpoint cells. -/
theorem crossRoutingViaFinset_disjoint_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {source target : (secondOrderDefectGraph G).ConnectedComponent}
    (hst : source ≠ target)
    {via via' : (secondOrderDefectGraph G).ConnectedComponent}
    (hne : via ≠ via') :
    Disjoint (crossRoutingViaFinset G hfree hst via)
      (crossRoutingViaFinset G hfree hst via') := by
  classical
  rw [Finset.disjoint_left]
  intro p hp hp'
  simp only [crossRoutingViaFinset, Finset.mem_sigma, Finset.mem_univ,
    Finset.mem_filter, true_and] at hp hp'
  exact hne (hp.trans hp'.symm)

/-- The via-color classes tile the complete ordered endpoint grid. -/
theorem biUnion_crossRoutingViaFinset_eq_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {source target : (secondOrderDefectGraph G).ConnectedComponent}
    (hst : source ≠ target) :
    (Finset.univ : Finset
      (secondOrderDefectGraph G).ConnectedComponent).biUnion
        (crossRoutingViaFinset G hfree hst) = Finset.univ := by
  classical
  ext p
  constructor
  · intro _
    exact Finset.mem_univ p
  · intro _
    apply Finset.mem_biUnion.mpr
    refine ⟨crossIntermediateComponent G hfree hst p.1 p.2,
      Finset.mem_univ _, ?_⟩
    simp [crossRoutingViaFinset]

/-- In the all-size-two regime, every via-color has exactly `8q` endpoint
cells between any two distinct components.  This is uniform in `q`. -/
theorem binarySquare_regular_allSizeTwo_crossRoutingViaFinset_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hall : ∀ d : (secondOrderDefectGraph G).ConnectedComponent,
      d.supp.ncard = q * 2)
    {source target : (secondOrderDefectGraph G).ConnectedComponent}
    (hst : source ≠ target)
    (via : (secondOrderDefectGraph G).ConnectedComponent) :
    (crossRoutingViaFinset G hfree hst via).card = 8 * q := by
  classical
  rw [crossRoutingViaFinset, Finset.card_sigma]
  have hrow : ∀ x : source.supp,
      ((Finset.univ : Finset target.supp).filter fun z =>
        via = crossIntermediateComponent G hfree hst x z).card = 4 := by
    intro x
    exact binarySquare_regular_threeSizeTwoParts_routing_row_card_eq_four
      G hfree hq hreg hcard source via target hst
        (hall source) (hall via) (hall target) x
  simp_rw [hrow]
  rw [Finset.sum_const, Finset.card_univ, Set.fintypeCard_eq_ncard,
    hall source]
  change (q * 2) * 4 = 8 * q
  omega

end

end Erdos85

#print axioms Erdos85.crossRoutingViaFinset_disjoint_of_ne
#print axioms Erdos85.biUnion_crossRoutingViaFinset_eq_univ
#print axioms Erdos85.binarySquare_regular_allSizeTwo_crossRoutingViaFinset_card
