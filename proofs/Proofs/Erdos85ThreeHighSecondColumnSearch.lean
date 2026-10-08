import Proofs.Erdos85ThreeHighFirstColumnSearch

/-! Exact second-column split for H3 pairs whose first column may be forced.
Every listed first/second-column combination must be rejected; no concrete
rejection is supplied. Both prefix gates and the remaining six levels stay. -/

namespace Erdos85

private theorem finiteRowDFS_seven_second {α : Type}
    (domain : Fin 8 → List α)
    (keep : Nat → (Fin 8 → α) → Bool) (accept : (Fin 8 → α) → Bool)
    (rows : Fin 8 → α) :
    finiteRowDFS domain keep accept 7 1 rows =
      (domain 1).any (fun row =>
        let next := Function.update rows 1 row
        keep 2 next && finiteRowDFS domain keep accept 6 2 next) := by
  rfl

private theorem and_list_any {α : Type} (b : Bool) (xs : List α) (f : α → Bool) :
    b && xs.any f = xs.any (fun x => b && f x) := by
  cases b <;> simp

/-- One first/second-column branch with both prefix checks. -/
def threeHighFirstTwoColumnsBranch
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (accept : ThreeHighCross → Bool) (S T : Finset (Fin 15)) : Bool :=
  let domains := Array.ofFn (threeHighStaticPrunedColumnList U R)
  let keep := threeHighFactoredColumnGate U R
  let finish := threeHighFactoredColumnAccept U R accept
  let first := Function.update (fun _ : Fin 8 => (∅ : Finset (Fin 15))) 0 S
  let second := Function.update first 1 T
  keep 1 first && (keep 2 second &&
    finiteRowDFS (fun j => domains[j.val]!) keep finish 6 2 second)

theorem threeHighFirstColumnBranch_eq_secondColumns
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (accept : ThreeHighCross → Bool) (S : Finset (Fin 15)) :
    threeHighFirstColumnBranch U R accept S =
      (threeHighStaticPrunedColumnList U R 1).any
        (threeHighFirstTwoColumnsBranch U R accept S) := by
  unfold threeHighFirstColumnBranch threeHighFirstTwoColumnsBranch
  rw [finiteRowDFS_seven_second]
  simp [and_list_any]

/-- Cache the fixed adjacency matrices for a separately executable two-column branch. -/
def threeHighNativeTwoColumnSearch
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (S T : Finset (Fin 15)) : Bool :=
  let uRows := Vector.ofFn (fun i => Vector.ofFn (U i))
  let rRows := Vector.ofFn (fun i => Vector.ofFn (R i))
  let cachedU := fun i j => (uRows.get i).get j
  let cachedR := fun i j => (rRows.get i).get j
  threeHighFirstTwoColumnsBranch cachedU cachedR
    (fun cross => threeHighCachedDistinctJointSearch
      (threeHighEmptyAdj cachedU cachedR cross)) S T

private theorem native_two_eq
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (S T : Finset (Fin 15)) :
    threeHighNativeTwoColumnSearch U R S T =
      threeHighFirstTwoColumnsBranch U R
        (fun cross => threeHighCachedDistinctJointSearch (threeHighEmptyAdj U R cross)) S T := by
  have hu : (fun i j => ((Vector.ofFn (fun i => Vector.ofFn (U i))).get i).get j) = U := by
    funext i j
    simp
  have hr : (fun i j => ((Vector.ofFn (fun i => Vector.ofFn (R i))).get i).get j) = R := by
    funext i j
    simp
  simp only [threeHighNativeTwoColumnSearch, hu, hr]

theorem threeHighNativeFirstColumnSearch_eq_secondColumns
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (S : Finset (Fin 15)) :
    threeHighNativeFirstColumnSearch U R S =
      (threeHighStaticPrunedColumnList U R 1).any (threeHighNativeTwoColumnSearch U R S) := by
  rw [threeHighNativeFirstColumnSearch_eq,
    threeHighFirstColumnBranch_eq_secondColumns]
  exact congrArg (fun f => (threeHighStaticPrunedColumnList U R 1).any f)
    (funext (fun T => (native_two_eq U R S T).symm))

theorem threeHighNativePairSearch_false_of_twoColumns
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (hreject : ∀ S ∈ threeHighStaticPrunedColumnList U R 0,
      ∀ T ∈ threeHighStaticPrunedColumnList U R 1,
        threeHighNativeTwoColumnSearch U R S T = false) :
    threeHighNativePairSearch U R = false := by
  apply threeHighNativePairSearch_false_of_firstColumns
  intro S hS
  rw [threeHighNativeFirstColumnSearch_eq_secondColumns]
  apply List.any_eq_false.mpr
  intro T hT
  simp [hreject S hS T hT]

attribute [local irreducible] threeHighCrossDomain

theorem threeHighNativeTwoColumns_no_joint
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (hreject : ∀ S ∈ threeHighStaticPrunedColumnList U R 0,
      ∀ T ∈ threeHighStaticPrunedColumnList U R 1,
        threeHighNativeTwoColumnSearch U R S T = false)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross)
      threeHighCanonicalRow = true) :
    ¬ ThreeHighDistinctJointWitness (threeHighEmptyAdj U R cross) :=
  threeHighNativePairSearch_no_joint U R
    (threeHighNativePairSearch_false_of_twoColumns U R hreject) cross hc he

end Erdos85

#print axioms Erdos85.threeHighFirstColumnBranch_eq_secondColumns
#print axioms Erdos85.threeHighNativeFirstColumnSearch_eq_secondColumns
#print axioms Erdos85.threeHighNativePairSearch_false_of_twoColumns
#print axioms Erdos85.threeHighNativeTwoColumns_no_joint
