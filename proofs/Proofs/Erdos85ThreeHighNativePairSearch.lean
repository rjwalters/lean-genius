import Proofs.Erdos85ThreeHighStaticCapacityColumnDFS
import Proofs.Erdos85ThreeHighDistinctJointSearch

/-! Cached executable H3 pair search with the distinct-neighbor terminal.
The external traversal equals the existing sound static-capacity search.
A rejection excludes only the supplied U/R pair, under the cross-domain and
external-cap hypotheses. No universal rejection or H3 exclusion is asserted. -/

namespace Erdos85

/-- Cache the fixed block-cap check once per U/R pair. -/
def threeHighFactoredCapacityColumnDFS : ThreeHighExternalSearch := fun U R accept =>
  let domains := Array.ofFn (threeHighStaticPrunedColumnList U R)
  let degrees := Array.ofFn (fun i : Fin 15 => encodedRowDegree (U i))
  let fixedCap := threeHighUnionBlockCap U
  finiteRowDFS (fun j => domains[j.val]!)
    (fun k columns =>
      let cross := threeHighCrossOfColumns columns
      threeHighColumnRowCapacityFor (fun i => degrees[i.val]!) cross k &&
        (fixedCap && threeHighCrossBlockCap cross) &&
        encodedC4FreeCachedRows (threeHighEmptyAdj U R cross))
    (fun columns =>
      let cross := threeHighCrossOfColumns columns
      encodedDegreeProfile (threeHighEmptyAdj U R cross) (fun i => if i = 23 then 6 else 4) &&
        accept cross)
    8 0 (fun _ => ∅)

theorem threeHighFactoredCapacityColumnDFS_eq
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (accept : ThreeHighCross → Bool) :
    threeHighFactoredCapacityColumnDFS U R accept =
      threeHighStaticCapacityColumnDFS U R accept := by
  simp only [threeHighFactoredCapacityColumnDFS, threeHighStaticCapacityColumnDFS,
    threeHighCapacityColumnDFSWith, threeHighExternalBlockCap_factor]

/-- Cache U/R adjacency before running the sound column and family searches. -/
def threeHighNativePairSearch (U : Fin 15 → Fin 15 → Bool)
    (R : Fin 8 → Fin 8 → Bool) : Bool :=
  let uRows := Vector.ofFn (fun i => Vector.ofFn (U i))
  let rRows := Vector.ofFn (fun i => Vector.ofFn (R i))
  let cachedU := fun i j => (uRows.get i).get j
  let cachedR := fun i j => (rRows.get i).get j
  threeHighFactoredCapacityColumnDFS cachedU cachedR
    (fun cross => threeHighCachedDistinctJointSearch
      (threeHighEmptyAdj cachedU cachedR cross))

theorem threeHighNativePairSearch_eq
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool) :
    threeHighNativePairSearch U R = threeHighStaticCapacityColumnDFS U R
      (fun cross => threeHighCachedDistinctJointSearch (threeHighEmptyAdj U R cross)) := by
  have hu : (fun i j => ((Vector.ofFn (fun i => Vector.ofFn (U i))).get i).get j) = U := by
    funext i j
    simp
  have hr : (fun i j => ((Vector.ofFn (fun i => Vector.ofFn (R i))).get i).get j) = R := by
    funext i j
    simp
  simp only [threeHighNativePairSearch, hu, hr, threeHighFactoredCapacityColumnDFS_eq]

attribute [local irreducible] threeHighCrossDomain

set_option maxRecDepth 10000 in
theorem threeHighNativePairSearch_no_joint
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (hreject : threeHighNativePairSearch U R = false)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross)
      threeHighCanonicalRow = true) :
    ¬ ThreeHighDistinctJointWitness (threeHighEmptyAdj U R cross) := by
  intro hj
  have ha := threeHighCachedDistinctJointSearch_sound _ hj
  have hs := threeHighStaticCapacityColumnDFS_sound U R
    (fun c => threeHighCachedDistinctJointSearch (threeHighEmptyAdj U R c)) cross hc he ha
  rw [← threeHighNativePairSearch_eq] at hs
  rw [hreject] at hs
  cases hs

end Erdos85

#print axioms Erdos85.threeHighFactoredCapacityColumnDFS_eq
#print axioms Erdos85.threeHighNativePairSearch_eq
#print axioms Erdos85.threeHighNativePairSearch_no_joint
