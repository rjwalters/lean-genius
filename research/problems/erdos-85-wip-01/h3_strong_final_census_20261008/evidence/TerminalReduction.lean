import FullBlockReduction
import FixedPairExclusion
namespace FullTerminalPruning
open Erdos85
set_option maxRecDepth 100000
attribute [local irreducible] threeHighCrossDomain

def remainingPairs := FullUBlockPruning.remainingPairs.erase (1,14)

theorem first_pair_mem : (1,14) ∈ FullUBlockPruning.remainingPairs := by
  simp only [FullUBlockPruning.remainingPairs, FullUOrbitPruning.remainingPairs,
    threeHighSecondaryDegreeCodes_eight]
  decide

theorem remainingPairs_card : remainingPairs.card = 275 := by
  rw [remainingPairs, Finset.card_erase_of_mem first_pair_mem, FullUBlockPruning.remainingPairs_card]

theorem representative_one : FullURestrictedAssembly.representative 1 =
    threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)) := by
  rfl

/-- The checked fixed-pair exclusion removes (1,14) while retaining the same witness. -/
theorem actual_pair_mem
    (r : Fin 55) (q : Fin 21) (cross : ThreeHighCross)
    (hp : (r,q) ∈ FullUBlockPruning.remainingPairs)
    (hc : cross ∈ threeHighCrossDomain (FullURestrictedAssembly.representative r)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)))
    (he : encodedExternalBlockCap (threeHighEmptyAdj (FullURestrictedAssembly.representative r)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)
      threeHighCanonicalRow = true)
    (hj : ThreeHighJointWitness (threeHighEmptyAdj (FullURestrictedAssembly.representative r)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)) :
    (r,q) ∈ remainingPairs := by
  apply Finset.mem_erase.mpr
  refine ⟨?_,hp⟩
  intro h
  have hr : r=1 := congrArg Prod.fst h
  have hq : q=14 := congrArg Prod.snd h
  subst r
  subst q
  rw [representative_one] at hc he hj
  exact ColumnCoverageFixedPair.no_joint cross hc he hj

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
  obtain ⟨r,q,cross,hp,hc,he,hj⟩ := FullUBlockPruning.actual_full_witness_pruned
    G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  exact ⟨r,q,cross,actual_pair_mem r q cross hp hc he hj,hc,he,hj⟩

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


end FullTerminalPruning
#print axioms FullTerminalPruning.first_pair_mem
#print axioms FullTerminalPruning.remainingPairs_card
#print axioms FullTerminalPruning.representative_one
#print axioms FullTerminalPruning.actual_pair_mem

#print axioms FullTerminalPruning.actual_full_witness_pruned

#print axioms FullTerminalPruning.actual_full_excluded_pruned
