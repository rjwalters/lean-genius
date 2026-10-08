import Proofs.Erdos85ThreeHighNativePairSearch

/-! Split the existing H3 search after its first column. All branches must be
rejected before this module yields a pair exclusion; no concrete rejection is
supplied here. Each executable branch keeps the existing prefix gate and seven
remaining DFS levels, including the unchanged terminal search. -/

namespace Erdos85

private theorem finiteRowDFS_eight_first {α : Type}
    (domain : Fin 8 → List α)
    (keep : Nat → (Fin 8 → α) → Bool) (accept : (Fin 8 → α) → Bool)
    (rows : Fin 8 → α) :
    finiteRowDFS domain keep accept 8 0 rows =
      (domain 0).any (fun row =>
        let next := Function.update rows 0 row
        keep 1 next && finiteRowDFS domain keep accept 7 1 next) := by
  rfl

def threeHighFactoredColumnGate
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool) :
    Nat → (Fin 8 → Finset (Fin 15)) → Bool :=
  let degrees := Array.ofFn (fun i : Fin 15 => encodedRowDegree (U i))
  let fixedCap := threeHighUnionBlockCap U
  fun k columns =>
    let cross := threeHighCrossOfColumns columns
    threeHighColumnRowCapacityFor (fun i => degrees[i.val]!) cross k &&
      (fixedCap && threeHighCrossBlockCap cross) &&
      encodedC4FreeCachedRows (threeHighEmptyAdj U R cross)

def threeHighFactoredColumnAccept
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (accept : ThreeHighCross → Bool) (columns : Fin 8 → Finset (Fin 15)) : Bool :=
  let cross := threeHighCrossOfColumns columns
  encodedDegreeProfile (threeHighEmptyAdj U R cross) (fun i => if i = 23 then 6 else 4) &&
    accept cross

/-- One first-column branch, including its first prefix check. -/
def threeHighFirstColumnBranch
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (accept : ThreeHighCross → Bool) (S : Finset (Fin 15)) : Bool :=
  let domains := Array.ofFn (threeHighStaticPrunedColumnList U R)
  let keep := threeHighFactoredColumnGate U R
  let finish := threeHighFactoredColumnAccept U R accept
  let first := Function.update (fun _ : Fin 8 => (∅ : Finset (Fin 15))) 0 S
  keep 1 first && finiteRowDFS (fun j => domains[j.val]!) keep finish 7 1 first

theorem threeHighFactoredCapacityColumnDFS_eq_firstColumns
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (accept : ThreeHighCross → Bool) :
    threeHighFactoredCapacityColumnDFS U R accept =
      (threeHighStaticPrunedColumnList U R 0).any
        (threeHighFirstColumnBranch U R accept) := by
  unfold threeHighFactoredCapacityColumnDFS threeHighFirstColumnBranch
    threeHighFactoredColumnGate threeHighFactoredColumnAccept
  rw [finiteRowDFS_eight_first]
  simp

/-- Cache U/R once for a separately executable native first-column branch. -/
def threeHighNativeFirstColumnSearch
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (S : Finset (Fin 15)) : Bool :=
  let uRows := Vector.ofFn (fun i => Vector.ofFn (U i))
  let rRows := Vector.ofFn (fun i => Vector.ofFn (R i))
  let cachedU := fun i j => (uRows.get i).get j
  let cachedR := fun i j => (rRows.get i).get j
  threeHighFirstColumnBranch cachedU cachedR
    (fun cross => threeHighCachedDistinctJointSearch
      (threeHighEmptyAdj cachedU cachedR cross)) S

theorem threeHighNativeFirstColumnSearch_eq
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (S : Finset (Fin 15)) :
    threeHighNativeFirstColumnSearch U R S =
      threeHighFirstColumnBranch U R
        (fun cross => threeHighCachedDistinctJointSearch (threeHighEmptyAdj U R cross)) S := by
  have hu : (fun i j => ((Vector.ofFn (fun i => Vector.ofFn (U i))).get i).get j) = U := by
    funext i j
    simp
  have hr : (fun i j => ((Vector.ofFn (fun i => Vector.ofFn (R i))).get i).get j) = R := by
    funext i j
    simp
  simp only [threeHighNativeFirstColumnSearch, hu, hr]

theorem threeHighNativePairSearch_eq_firstColumns
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool) :
    threeHighNativePairSearch U R =
      (threeHighStaticPrunedColumnList U R 0).any (threeHighNativeFirstColumnSearch U R) := by
  rw [threeHighNativePairSearch_eq, ← threeHighFactoredCapacityColumnDFS_eq,
    threeHighFactoredCapacityColumnDFS_eq_firstColumns]
  exact congrArg (fun f => (threeHighStaticPrunedColumnList U R 0).any f)
    (funext (fun S => (threeHighNativeFirstColumnSearch_eq U R S).symm))

theorem threeHighNativePairSearch_false_of_firstColumns
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (hreject : ∀ S ∈ threeHighStaticPrunedColumnList U R 0,
      threeHighNativeFirstColumnSearch U R S = false) :
    threeHighNativePairSearch U R = false := by
  rw [threeHighNativePairSearch_eq_firstColumns]
  apply List.any_eq_false.mpr
  intro S hS
  simp [hreject S hS]

attribute [local irreducible] threeHighCrossDomain

theorem threeHighNativeFirstColumns_no_joint
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (hreject : ∀ S ∈ threeHighStaticPrunedColumnList U R 0,
      threeHighNativeFirstColumnSearch U R S = false)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross)
      threeHighCanonicalRow = true) :
    ¬ ThreeHighDistinctJointWitness (threeHighEmptyAdj U R cross) :=
  threeHighNativePairSearch_no_joint U R
    (threeHighNativePairSearch_false_of_firstColumns U R hreject) cross hc he

end Erdos85

#print axioms Erdos85.threeHighFactoredCapacityColumnDFS_eq_firstColumns
#print axioms Erdos85.threeHighNativeFirstColumnSearch_eq
#print axioms Erdos85.threeHighNativePairSearch_eq_firstColumns
#print axioms Erdos85.threeHighNativePairSearch_false_of_firstColumns
#print axioms Erdos85.threeHighNativeFirstColumns_no_joint
