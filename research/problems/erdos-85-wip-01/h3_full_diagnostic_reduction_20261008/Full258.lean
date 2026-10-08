import Full259
import FullMembership
import Proofs.Erdos85ThreeHighPilotFullU54R20Certificate

/-! Consume the verified U54/R20 pilot in the retained full census.
The remaining 258 search rejections stay explicit hypotheses. This module
does not establish full H3 exclusion by itself. -/

namespace FullUStrongAfterThreePilots
open Erdos85 SimpleGraph
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] threeHighCrossDomain

def remainingPairs : Finset (Fin 55 × Fin 21) :=
  FullUStrongAfterTwoPilots.remainingPairs.erase (54,20)

theorem pilot_mem : ((54 : Fin 55), (20 : Fin 21)) ∈
    FullUStrongAfterTwoPilots.remainingPairs := by
  exact Finset.mem_erase.mpr ⟨by decide,
    Finset.mem_erase.mpr ⟨by decide, FullU54R20_mem⟩⟩

theorem remainingPairs_card : remainingPairs.card = 258 := by
  rw [remainingPairs, Finset.card_erase_of_mem pilot_mem,
    FullUStrongAfterTwoPilots.remainingPairs_card]

theorem pilot_input : FullURestrictedAssembly.representative 54 =
    VariedPilot.FullU54R20.U := by rfl

theorem pilot_rejected :
    threeHighNativePairSearch (FullURestrictedAssembly.representative 54)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 20)) = false := by
  rw [pilot_input]
  exact VariedPilot.FullU54R20.rejected

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
  obtain ⟨r,q,cross,hp,hc,he,hj⟩ := FullUStrongAfterTwoPilots.actual_distinct_witness
    G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  have hne : (r,q) ≠ ((54 : Fin 55), (20 : Fin 21)) := by
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

end FullUStrongAfterThreePilots

#print axioms FullUStrongAfterThreePilots.pilot_mem
#print axioms FullUStrongAfterThreePilots.remainingPairs_card
#print axioms FullUStrongAfterThreePilots.pilot_input
#print axioms FullUStrongAfterThreePilots.pilot_rejected
#print axioms FullUStrongAfterThreePilots.actual_distinct_witness
#print axioms FullUStrongAfterThreePilots.excluded_of_rejections
