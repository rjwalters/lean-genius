import Deficient1554
import DeficientMembership
import Proofs.Erdos85ThreeHighPilotDeficientU26R2Certificate

/-! Consume the verified U26/R2 pilot in the retained deficient census.
The remaining 1553 search rejections stay explicit hypotheses. This module
has not yet passed a cloud build; it does not establish deficient H3 exclusion. -/

namespace DeficientUStrongAfterPilot
open Erdos85 SimpleGraph
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] threeHighCrossDomain

def remainingPairs : Finset (Fin 370 × Fin 21) :=
  DeficientUOrbitPruning.remainingPairs.erase (26,2)

theorem pilot_mem : ((26 : Fin 370), (2 : Fin 21)) ∈
    DeficientUOrbitPruning.remainingPairs := by
  exact DeficientU26R2_mem

theorem remainingPairs_card : remainingPairs.card = 1553 := by
  rw [remainingPairs, Finset.card_erase_of_mem pilot_mem,
    DeficientUOrbitPruning.remainingPairs_card]

theorem pilot_input : DeficientUNormalizedAssembly.representative 26 =
    VariedPilot.DeficientU26R2.U := by
  exact DeficientU26R2_input

theorem pilot_rejected :
    threeHighNativePairSearch (DeficientUNormalizedAssembly.representative 26)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 2)) = false := by
  rw [pilot_input]
  exact VariedPilot.DeficientU26R2.rejected

theorem actual_distinct_witness
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (s t v : Fin 49) (hst : s ≠ t) (hsv : s ≠ v) (htv : t ≠ v)
    (hS : threeHighTripleSpecialSet G z = {s,t,v})
    (hr : (G.induce (↑(threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)) :
      Set (Fin 49))).edgeFinset.card = 3) :
    ∃ (r : Fin 370) (q : Fin 21) (cross : ThreeHighCross), (r,q) ∈ remainingPairs ∧
      cross ∈ threeHighCrossDomain (DeficientUNormalizedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) ∧
      encodedExternalBlockCap (threeHighEmptyAdj (DeficientUNormalizedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)
        threeHighCanonicalRow = true ∧
      ThreeHighDistinctJointWitness (threeHighEmptyAdj (DeficientUNormalizedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross) := by
  obtain ⟨r,q,cross,hp,hc,he,hj⟩ := DeficientUStrongCensus.actual_distinct_witness
    G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  have hne : (r,q) ≠ ((26 : Fin 370), (2 : Fin 21)) := by
    intro h
    rcases Prod.mk.inj h with ⟨hr,hq⟩
    subst r
    subst q
    exact threeHighNativePairSearch_no_joint _ _ pilot_rejected cross hc he hj
  exact ⟨r,q,cross,Finset.mem_erase.mpr ⟨hne,hp⟩,hc,he,hj⟩

theorem excluded_of_rejections
    (hreject : ∀ (r : Fin 370) (q : Fin 21), (r,q) ∈ remainingPairs →
      threeHighNativePairSearch (DeficientUNormalizedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) = false)
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (s t v : Fin 49) (hst : s ≠ t) (hsv : s ≠ v) (htv : t ≠ v)
    (hS : threeHighTripleSpecialSet G z = {s,t,v})
    (hr : (G.induce (↑(threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)) :
      Set (Fin 49))).edgeFinset.card = 3) : False := by
  obtain ⟨r,q,cross,hp,hc,he,hj⟩ := actual_distinct_witness
    G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  exact threeHighNativePairSearch_no_joint _ _ (hreject r q hp) cross hc he hj

end DeficientUStrongAfterPilot

#print axioms DeficientUStrongAfterPilot.pilot_mem
#print axioms DeficientUStrongAfterPilot.remainingPairs_card
#print axioms DeficientUStrongAfterPilot.pilot_input
#print axioms DeficientUStrongAfterPilot.pilot_rejected
#print axioms DeficientUStrongAfterPilot.actual_distinct_witness
#print axioms DeficientUStrongAfterPilot.excluded_of_rejections
