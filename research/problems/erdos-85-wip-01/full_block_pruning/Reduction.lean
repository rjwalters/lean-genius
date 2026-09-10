import Pruning
import Certificate

namespace FullUBlockPruning
open Erdos85 SimpleGraph
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] threeHighCrossDomain

def remainingPairs : Finset (Fin 55 × Fin 21) :=
  FullUOrbitPruning.remainingPairs.filter (fun rq => rq.1 ∈ FullUBlockOrbits.targets)

theorem remainingPairs_card : remainingPairs.card = 276 := by
  simp only [remainingPairs, FullUOrbitPruning.remainingPairs,
    threeHighSecondaryDegreeCodes_eight]
  decide

theorem remainingPairs_subset : remainingPairs ⊆ FullUOrbitPruning.remainingPairs :=
  Finset.filter_subset _ _

theorem joint_witness_reduced (r : Fin 55) (q : Fin 21) (cross : ThreeHighCross)
    (hq : q ∈ threeHighSecondaryDegreeCodes 8)
    (hc : cross ∈ threeHighCrossDomain (FullURestrictedAssembly.representative r)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)))
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj (FullURestrictedAssembly.representative r)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)
      threeHighCanonicalRow = true)
    (hJoint : ThreeHighJointWitness (threeHighEmptyAdj (FullURestrictedAssembly.representative r)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)) :
    ∃ (r' : Fin 55) (cross' : ThreeHighCross), (r',q) ∈ remainingPairs ∧
      cross' ∈ threeHighCrossDomain (FullURestrictedAssembly.representative r')
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) ∧
      encodedExternalBlockCap (threeHighEmptyAdj (FullURestrictedAssembly.representative r')
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross')
        threeHighCanonicalRow = true ∧
      ThreeHighJointWitness (threeHighEmptyAdj (FullURestrictedAssembly.representative r')
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross') := by
  obtain ⟨c,hc',he',hj'⟩ := FullUBlockOrbits.joint_transport r _ cross hc hExt hJoint
  refine ⟨FullUBlockOrbits.target r,c,?_,hc',he',hj'⟩
  exact Finset.mem_filter.mpr ⟨FullUOrbitPruning.actual_pair_mem _ q c hq hc',
    FullUBlockOrbits.target_mem r⟩

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
  obtain ⟨r',c,hp,hc',he',hj'⟩ := joint_witness_reduced r q cross hq hc hExt hJoint
  exact ⟨r',q,c,hp,hc',he',hj'⟩

/-- Only the276 remaining representative-pair searches are required to reject.
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

end FullUBlockPruning
#print axioms FullUBlockPruning.remainingPairs_card
#print axioms FullUBlockPruning.remainingPairs_subset
#print axioms FullUBlockPruning.joint_witness_reduced
#print axioms FullUBlockPruning.actual_full_witness_pruned
#print axioms FullUBlockPruning.actual_full_excluded_pruned
