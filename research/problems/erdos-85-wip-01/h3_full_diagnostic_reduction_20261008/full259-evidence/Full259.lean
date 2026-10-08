import Full260
import FullMembership
import Proofs.Erdos85ThreeHighPilotFullU3R3Certificate

/-! Consume the verified U3/R3 pilot in the retained full census.
The remaining 259 search rejections stay explicit hypotheses. This module
does not establish full H3 exclusion by itself. -/

namespace FullUStrongAfterTwoPilots
open Erdos85 SimpleGraph
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] threeHighCrossDomain

def remainingPairs : Finset (Fin 55 × Fin 21) :=
  FullUStrongAfterPilot.remainingPairs.erase (3,3)

theorem pilot_mem : ((3 : Fin 55), (3 : Fin 21)) ∈
    FullUStrongAfterPilot.remainingPairs := by
  exact Finset.mem_erase.mpr ⟨by decide, FullU3R3_mem⟩

theorem remainingPairs_card : remainingPairs.card = 259 := by
  rw [remainingPairs, Finset.card_erase_of_mem pilot_mem,
    FullUStrongAfterPilot.remainingPairs_card]

theorem pilot_input : FullURestrictedAssembly.representative 3 =
    VariedPilot.FullU3R3.U := by rfl

theorem pilot_rejected :
    threeHighNativePairSearch (FullURestrictedAssembly.representative 3)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 3)) = false := by
  rw [pilot_input]
  exact VariedPilot.FullU3R3.rejected

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
      Set (Fin 49))).edgeFinset.card = 4) :
    ∃ (r : Fin 55) (q : Fin 21) (cross : ThreeHighCross), (r,q) ∈ remainingPairs ∧
      cross ∈ threeHighCrossDomain (FullURestrictedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) ∧
      encodedExternalBlockCap (threeHighEmptyAdj (FullURestrictedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)
        threeHighCanonicalRow = true ∧
      ThreeHighDistinctJointWitness (threeHighEmptyAdj (FullURestrictedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross) := by
  obtain ⟨r,q,cross,hp,hc,he,hj⟩ := FullUStrongAfterPilot.actual_distinct_witness
    G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  have hne : (r,q) ≠ ((3 : Fin 55), (3 : Fin 21)) := by
    intro h
    rcases Prod.mk.inj h with ⟨hr,hq⟩
    subst r
    subst q
    exact threeHighNativePairSearch_no_joint _ _ pilot_rejected cross hc he hj
  exact ⟨r,q,cross,Finset.mem_erase.mpr ⟨hne,hp⟩,hc,he,hj⟩

theorem excluded_of_rejections
    (hreject : ∀ (r : Fin 55) (q : Fin 21), (r,q) ∈ remainingPairs →
      threeHighNativePairSearch (FullURestrictedAssembly.representative r)
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
      Set (Fin 49))).edgeFinset.card = 4) : False := by
  obtain ⟨r,q,cross,hp,hc,he,hj⟩ := actual_distinct_witness
    G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  exact threeHighNativePairSearch_no_joint _ _ (hreject r q hp) cross hc he hj

end FullUStrongAfterTwoPilots

#print axioms FullUStrongAfterTwoPilots.pilot_mem
#print axioms FullUStrongAfterTwoPilots.remainingPairs_card
#print axioms FullUStrongAfterTwoPilots.pilot_input
#print axioms FullUStrongAfterTwoPilots.pilot_rejected
#print axioms FullUStrongAfterTwoPilots.actual_distinct_witness
#print axioms FullUStrongAfterTwoPilots.excluded_of_rejections
