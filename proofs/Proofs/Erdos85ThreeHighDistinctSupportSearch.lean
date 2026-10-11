import Proofs.Erdos85ThreeHighNativePairSearch

/-! Prune triples without a distinct compatible neighbor in every color before
enumerating resolution families. Every pass preserves the strong graph witness.
This module supplies search soundness, not a concrete pair rejection. -/

namespace Erdos85

def threeHighDistinctSupportPass (B : Fin 24 → Fin 24 → Bool)
    (D : Fin 3 → List (Finset (Fin 24))) (i : Fin 3) : List (Finset (Fin 24)) :=
  (D i).filter fun S => (List.finRange 3).all fun j =>
    (D j).any (fun T => decide (T ≠ S) && encodedCrossIndependent B S T)

theorem threeHighDistinctSupportPass_preserves
    (B : Fin 24 → Fin 24 → Bool) (D : Fin 3 → List (Finset (Fin 24)))
    (F : Fin 3 → Finset (Finset (Fin 24)))
    (hmem : ∀ i S, S ∈ F i → S ∈ D i)
    (hcompat : ∀ i j, encodedDistinctFamilyCompatibility B (F i) (F j) = true) :
    ∀ i S, S ∈ F i → S ∈ threeHighDistinctSupportPass B D i := by
  intro i S hS
  apply List.mem_filter.mpr
  refine ⟨hmem i S hS, List.all_eq_true.mpr ?_⟩
  intro j _
  have h := of_decide_eq_true (hcompat i j)
  obtain ⟨T,hT,hne,hST⟩ := h S hS
  apply List.any_eq_true.mpr
  exact ⟨T,hmem j T hT,by simp [hne,hST]⟩

/-- Cache each simultaneous pass and stop on equality or when fuel runs out. -/
def threeHighDistinctSupportUntilStable (B : Fin 24 → Fin 24 → Bool) :
    Nat → ThreeHighTripleTable → ThreeHighTripleTable
  | 0, D => D
  | n+1, D =>
    let E := Vector.ofFn (threeHighDistinctSupportPass B D.get)
    if E.get = D.get then D else threeHighDistinctSupportUntilStable B n E

theorem threeHighDistinctSupportUntilStable_preserves
    (B : Fin 24 → Fin 24 → Bool) (n : Nat) (D : ThreeHighTripleTable)
    (F : Fin 3 → Finset (Finset (Fin 24)))
    (hmem : ∀ i S, S ∈ F i → S ∈ D.get i)
    (hcompat : ∀ i j, encodedDistinctFamilyCompatibility B (F i) (F j) = true) :
    ∀ i S, S ∈ F i → S ∈ (threeHighDistinctSupportUntilStable B n D).get i := by
  induction n generalizing D with
  | zero => exact hmem
  | succ n ih =>
    dsimp only [threeHighDistinctSupportUntilStable]
    split
    · exact hmem
    · apply ih
      simpa using threeHighDistinctSupportPass_preserves B D.get F hmem hcompat

def threeHighDistinctSupportSearch (B : Fin 24 → Fin 24 → Bool) : Bool :=
  let adjacency := Vector.ofFn (fun i => Vector.ofFn (B i))
  let cachedB := fun i j => (adjacency.get i).get j
  let initial := Vector.ofFn (fun k => (threeHighCanonicalTripleShapes k).filter
    (threeHighTripleNoCommonNeighbor cachedB))
  let table := threeHighDistinctSupportUntilStable cachedB
    (threeHighTripleSupportSize initial.get) initial
  threeHighListedDistinctJointSearch cachedB table.get threeHighCanonicalResidual

theorem threeHighDistinctSupportSearch_sound
    (B : Fin 24 → Fin 24 → Bool) (hB : ThreeHighDistinctJointWitness B) :
    threeHighDistinctSupportSearch B = true := by
  have hb : (fun i j => ((Vector.ofFn (fun i => Vector.ofFn (B i))).get i).get j) = B := by
    funext i j
    simp
  simp only [threeHighDistinctSupportSearch, hb]
  obtain ⟨F,hF,hblocks,hcompat,hcap⟩ := hB
  apply threeHighListedDistinctJointSearch_of_families B _ _ F hF _ hcompat hcap
  apply threeHighDistinctSupportUntilStable_preserves B _ _ F _ hcompat
  intro k S hS
  simp only [Vector.get_ofFn]
  rw [threeHighCanonicalTripleShapes_filter]
  apply List.mem_filter.mpr
  refine ⟨?_,hblocks k S hS⟩
  rw [threeHighDirectTripleList_eq]
  exact (mem_threeHighEligibleTripleList B _ S).mpr
    (((mem_threeHighResolutionDomain B _ (F k)).mp (hF k)).1 hS)

def threeHighDistinctSupportPairSearch (U : Fin 15 → Fin 15 → Bool)
    (R : Fin 8 → Fin 8 → Bool) : Bool :=
  let uRows := Vector.ofFn (fun i => Vector.ofFn (U i))
  let rRows := Vector.ofFn (fun i => Vector.ofFn (R i))
  let cachedU := fun i j => (uRows.get i).get j
  let cachedR := fun i j => (rRows.get i).get j
  threeHighFactoredCapacityColumnDFS cachedU cachedR
    (fun cross => threeHighDistinctSupportSearch (threeHighEmptyAdj cachedU cachedR cross))

attribute [local irreducible] threeHighCrossDomain

theorem threeHighDistinctSupportPairSearch_no_joint
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (hreject : threeHighDistinctSupportPairSearch U R = false)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross)
      threeHighCanonicalRow = true) :
    ¬ ThreeHighDistinctJointWitness (threeHighEmptyAdj U R cross) := by
  intro hj
  have hu : (fun i j => ((Vector.ofFn (fun i => Vector.ofFn (U i))).get i).get j) = U := by
    funext i j
    simp
  have hr : (fun i j => ((Vector.ofFn (fun i => Vector.ofFn (R i))).get i).get j) = R := by
    funext i j
    simp
  simp only [threeHighDistinctSupportPairSearch,hu,hr,threeHighFactoredCapacityColumnDFS_eq]
    at hreject
  have ha := threeHighDistinctSupportSearch_sound _ hj
  have hs := threeHighStaticCapacityColumnDFS_sound U R
    (fun c => threeHighDistinctSupportSearch (threeHighEmptyAdj U R c)) cross hc he ha
  rw [hreject] at hs
  cases hs

end Erdos85

#print axioms Erdos85.threeHighDistinctSupportPass_preserves
#print axioms Erdos85.threeHighDistinctSupportUntilStable_preserves
#print axioms Erdos85.threeHighDistinctSupportSearch_sound
#print axioms Erdos85.threeHighDistinctSupportPairSearch_no_joint
