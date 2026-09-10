import Transport
import Proofs.Erdos85ThreeHighLowDegreeTriangleGate
import Proofs.Erdos85ThreeHighFarColorCertificate

namespace FullUOrbitPruning
open Erdos85 SimpleGraph
set_option maxRecDepth 100000
attribute [local irreducible] threeHighCrossDomain

def triangleCodes : Finset (Fin 55) := {0,11,23,35}
def farColorCodes : Finset (Fin 55) := {1,2,4,6,8,9,12,13,14,16,18,21,22,34}
def farRCodes : Finset (Fin 21) := {3,6,8,10,12,13,20}
def lowVertices (r : Fin 55) : Fin 3 → Fin 15 :=
  ![![4,9,14],![4,9,14],![4,9,14],![4,9,13],![4,9,13],![4,9,13],![4,9,13],![4,9,13],![4,9,13],![4,9,13],![4,9,13],![4,9,14],![4,9,14],![4,9,12],![4,9,12],![4,9,12],![4,9,12],![4,9,12],![4,8,13],![4,8,13],![4,8,13],![4,8,13],![4,8,13],![4,8,13],![4,8,13],![4,8,13],![4,8,13],![4,8,13],![4,8,12],![4,8,12],![4,8,12],![4,8,12],![4,8,12],![4,8,12],![4,8,13],![4,8,13],![4,8,13],![4,8,12],![4,8,12],![4,8,12],![4,8,11],![4,8,11],![4,8,11],![4,8,11],![4,8,11],![4,8,10],![4,8,10],![4,8,10],![4,8,10],![4,8,10],![4,8,10],![4,8,10],![4,8,10],![4,8,10],![4,8,10]] r

set_option maxHeartbeats 4000000 in
theorem triangle_checked (r : Fin 55) (hr : r ∈ triangleCodes) :
    threeHighLowDegreeTriangleGate (FullURestrictedAssembly.representative r) = false := by
  decide +revert

set_option maxHeartbeats 4000000 in
theorem far_color_checked (r : Fin 55) (hr : r ∈ farColorCodes) :
    ThreeHighFarColorObstruction (FullURestrictedAssembly.representative r) (lowVertices r) := by
  decide +revert

theorem far_R_checked (q : Fin 21) (hq : q ∈ farRCodes) :
    threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q) 6 7 = true ∧
    threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q) 7 6 = true := by
  decide +revert

def remainingPairs : Finset (Fin 55 × Fin 21) :=
  ((Finset.univ \ triangleCodes).product (threeHighSecondaryDegreeCodes 8)) \
    (farColorCodes.product farRCodes)

theorem remainingPairs_card : remainingPairs.card = 565 := by
  rw [remainingPairs,threeHighSecondaryDegreeCodes_eight]
  decide

theorem actual_pair_mem (r : Fin 55) (q : Fin 21) (cross : ThreeHighCross)
    (hq : q ∈ threeHighSecondaryDegreeCodes 8)
    (hc : cross ∈ threeHighCrossDomain (FullURestrictedAssembly.representative r)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q))) :
    (r,q) ∈ remainingPairs := by
  have htri : r ∉ triangleCodes := by
    intro hr
    have h := threeHighLowDegreeTriangleGate_of_cross _ _ cross hc
    rw [triangle_checked r hr] at h
    cases h
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,htri⟩,hq⟩,?_⟩
  intro hbad
  obtain ⟨hr,hqfar⟩ := Finset.mem_product.mp hbad
  obtain ⟨h67,h76⟩ := far_R_checked q hqfar
  exact (far_color_checked r hr).no_cross _ _ _ h67 h76 cross hc

theorem actual_full_witness_pruned
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
      ThreeHighJointWitness (threeHighEmptyAdj (FullURestrictedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross) := by
  obtain ⟨r,q,cross,hq,hc,hExt,hJoint⟩ := FullUOrbitTransport.actual_full_witness
    G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  exact ⟨r,q,cross,actual_pair_mem r q cross hq hc,hc,hExt,hJoint⟩

/-- Only the565 remaining representative-pair searches are required to reject.
This false-search hypothesis is not established in this artifact. -/
theorem actual_full_excluded_pruned
    (search : ThreeHighExternalSearch) (hsearch : ThreeHighExternalSearchSound search)
    (accept : (Fin 24 → Fin 24 → Bool) → Bool) (hsound : ThreeHighTerminalSound accept)
    (hreject : ∀ (r : Fin 55) (q : Fin 21), (r,q) ∈ remainingPairs →
      search (FullURestrictedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q))
        (fun cross => accept (threeHighEmptyAdj (FullURestrictedAssembly.representative r)
          (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)) = false)
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
  obtain ⟨r,q,cross,hq,hc,hExt,hJoint⟩ := actual_full_witness_pruned
    G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  have h := hsearch _ _ (fun c => accept (threeHighEmptyAdj
    (FullURestrictedAssembly.representative r)
    (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) c)) cross hc hExt (hsound _ hJoint)
  rw [hreject r q hq] at h
  cases h

end FullUOrbitPruning
#print axioms FullUOrbitPruning.triangle_checked
#print axioms FullUOrbitPruning.far_color_checked
#print axioms FullUOrbitPruning.far_R_checked
#print axioms FullUOrbitPruning.remainingPairs_card
#print axioms FullUOrbitPruning.actual_pair_mem
#print axioms FullUOrbitPruning.actual_full_witness_pruned
#print axioms FullUOrbitPruning.actual_full_excluded_pruned
