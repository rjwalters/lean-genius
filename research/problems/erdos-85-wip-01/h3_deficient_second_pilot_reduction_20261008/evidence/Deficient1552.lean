import Deficient1553
import DeficientMembership
import Proofs.Erdos85ThreeHighPilotDeficientU369R11Certificate

/-! Consume the verified U369/R11 pilot in the retained deficient census.
The remaining 1552 search rejections stay explicit hypotheses. This module
does not establish deficient H3 exclusion by itself. -/

namespace DeficientUStrongAfterTwoPilots
open Erdos85 SimpleGraph
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] threeHighCrossDomain

def remainingPairs : Finset (Fin 370 × Fin 21) :=
  DeficientUStrongAfterPilot.remainingPairs.erase (369,11)

theorem pilot_mem : ((369 : Fin 370), (11 : Fin 21)) ∈
    DeficientUStrongAfterPilot.remainingPairs := by
  apply Finset.mem_erase.mpr
  exact ⟨by decide, DeficientU369R11_mem⟩

theorem remainingPairs_card : remainingPairs.card = 1552 := by
  rw [remainingPairs, Finset.card_erase_of_mem pilot_mem,
    DeficientUStrongAfterPilot.remainingPairs_card]

theorem pilot_input : DeficientUNormalizedAssembly.representative 369 =
    VariedPilot.DeficientU369R11.U := by
  exact DeficientU369R11_input

theorem pilot_rejected :
    threeHighNativePairSearch (DeficientUNormalizedAssembly.representative 369)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 11)) = false := by
  rw [pilot_input]
  exact VariedPilot.DeficientU369R11.rejected

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
  obtain ⟨r,q,cross,hp,hc,he,hj⟩ := DeficientUStrongAfterPilot.actual_distinct_witness
    G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  have hne : (r,q) ≠ ((369 : Fin 370), (11 : Fin 21)) := by
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

end DeficientUStrongAfterTwoPilots

#print axioms DeficientUStrongAfterTwoPilots.pilot_mem
#print axioms DeficientUStrongAfterTwoPilots.remainingPairs_card
#print axioms DeficientUStrongAfterTwoPilots.pilot_input
#print axioms DeficientUStrongAfterTwoPilots.pilot_rejected
#print axioms DeficientUStrongAfterTwoPilots.actual_distinct_witness
#print axioms DeficientUStrongAfterTwoPilots.excluded_of_rejections
