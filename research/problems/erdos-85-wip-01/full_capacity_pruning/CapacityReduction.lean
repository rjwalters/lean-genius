import TerminalReduction
import SubsetCapacityBatch
import Zero32Exclusion
namespace FullCapacityPruning
open Erdos85
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
attribute [local irreducible] threeHighCrossDomain

def remainingPairs := (FullTerminalPruning.remainingPairs \ SubsetCapacityBatch.pairs).erase (32,14)

theorem remainingPairs_card : remainingPairs.card = 261 := by decide

theorem subset_representative (i : Fin 13) :
    FullURestrictedAssembly.representative (SubsetCapacityBatch.pair i).1 =
      SubsetCapacityBatch.U i := by
  fin_cases i <;> rfl

theorem subset_secondary (i : Fin 13) :
    threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative (SubsetCapacityBatch.pair i).2) =
      SubsetCapacityBatch.R i := by
  fin_cases i <;> rfl

theorem representative_32 : FullURestrictedAssembly.representative 32 =
    threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 10 58)) := by rfl

theorem actual_pair_mem
    (r : Fin 55) (q : Fin 21) (cross : ThreeHighCross)
    (hp : (r,q) ∈ FullTerminalPruning.remainingPairs)
    (hc : cross ∈ threeHighCrossDomain (FullURestrictedAssembly.representative r)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)))
    (he : encodedExternalBlockCap (threeHighEmptyAdj (FullURestrictedAssembly.representative r)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)
      threeHighCanonicalRow = true)
    (hj : ThreeHighJointWitness (threeHighEmptyAdj (FullURestrictedAssembly.representative r)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)) :
    (r,q) ∈ remainingPairs := by
  apply Finset.mem_erase.mpr
  constructor
  · intro h
    have hr : r=32 := congrArg Prod.fst h
    have hq : q=14 := congrArg Prod.snd h
    subst r
    subst q
    rw [representative_32] at hc he hj
    exact Zero32.no_joint cross hc he hj
  · apply Finset.mem_sdiff.mpr
    refine ⟨hp, ?_⟩
    intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    have hr := congrArg Prod.fst hi
    have hq := congrArg Prod.snd hi
    change (SubsetCapacityBatch.pair i).1 = r at hr
    change (SubsetCapacityBatch.pair i).2 = q at hq
    rw [← hr, ← hq, subset_representative, subset_secondary] at hc he
    exact SubsetCapacityBatch.impossible i cross hc he

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
  obtain ⟨r,q,cross,hp,hc,he,hj⟩ := FullTerminalPruning.actual_full_witness_pruned
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


end FullCapacityPruning
#print axioms FullCapacityPruning.remainingPairs_card
#print axioms FullCapacityPruning.subset_representative
#print axioms FullCapacityPruning.subset_secondary
#print axioms FullCapacityPruning.representative_32
#print axioms FullCapacityPruning.actual_pair_mem
#print axioms FullCapacityPruning.actual_full_witness_pruned
#print axioms FullCapacityPruning.actual_full_excluded_pruned
