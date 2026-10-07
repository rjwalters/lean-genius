import Proofs.Erdos85ThreeHighDistinctJointWitness
import Proofs.Erdos85ThreeHighCachedSupportClosure

/-! The terminal checks a distinct neighbor within each selected color family,
as well as the existing between-color compatibility and intersection tests. -/

namespace Erdos85

def threeHighListedDistinctJointSearch (B : Fin 24 → Fin 24 → Bool)
    (D : Fin 3 → List (Finset (Fin 24))) (R : Fin 3 → Finset (Fin 24)) : Bool :=
  threeHighJointFamilySearch B fun k accept =>
    finitePivotFamilySearch (D k)
      (fun F => encodedDistinctFamilyCompatibility B F F && accept F) 6 (R k) ∅

theorem threeHighListedDistinctJointSearch_of_families
    (B : Fin 24 → Fin 24 → Bool)
    (D : Fin 3 → List (Finset (Fin 24))) (R : Fin 3 → Finset (Fin 24))
    (F : Fin 3 → ThreeHighResolutionFamily)
    (hF : ∀ k, F k ∈ threeHighResolutionDomain B (R k))
    (hD : ∀ k S, S ∈ F k → S ∈ D k)
    (hcompat : ∀ i j, encodedDistinctFamilyCompatibility B (F i) (F j) = true)
    (hcap : ∀ i j, i ≠ j → encodedFamilyIntersectionCap (F i) (F j) = true) :
    threeHighListedDistinctJointSearch B D R = true := by
  unfold threeHighListedDistinctJointSearch
  apply threeHighJointFamilySearch_witness B _ F
  · intro k accept ha
    obtain ⟨hsub, hcard, hdis, hcover⟩ :=
      (mem_threeHighResolutionDomain B _ (F k)).mp (hF k)
    have hne : ∀ S ∈ F k, S.Nonempty := by
      intro S hS
      apply Finset.card_pos.mp
      have hc := ((mem_threeHighEligibleTriples B _ S).mp (hsub hS)).2.1
      omega
    apply finitePivotFamilySearch_of_family (D k) _ 6 (R k) (F k) ∅
      (hD k) hcard hne hdis hcover
    simpa only [Finset.union_empty, Bool.and_eq_true] using And.intro (hcompat k k) ha
  · intro i j _
    exact encodedDistinctFamilyCompatibility_forget B (F i) (F j) (hcompat i j)
  · exact hcap

def threeHighDistinctJointSearch (B : Fin 24 → Fin 24 → Bool) : Bool :=
  let D := threeHighTripleSupportClosure B
    (fun k => (threeHighCanonicalTripleShapes k).filter (threeHighTripleNoCommonNeighbor B))
  threeHighListedDistinctJointSearch B D threeHighCanonicalResidual

theorem threeHighDistinctJointSearch_sound
    (B : Fin 24 → Fin 24 → Bool) (hB : ThreeHighDistinctJointWitness B) :
    threeHighDistinctJointSearch B = true := by
  obtain ⟨F, hF, hblocks, hcompat, hcap⟩ := hB
  have hD : ∀ k S, S ∈ F k → S ∈ threeHighTripleSupportClosure B
      (fun k => (threeHighCanonicalTripleShapes k).filter (threeHighTripleNoCommonNeighbor B)) k := by
    apply threeHighTripleSupportClosure_preserves B _ F _
      (fun i j _ => encodedDistinctFamilyCompatibility_forget B (F i) (F j) (hcompat i j))
    intro k S hS
    rw [threeHighCanonicalTripleShapes_filter]
    apply List.mem_filter.mpr
    refine ⟨?_, hblocks k S hS⟩
    rw [threeHighDirectTripleList_eq]
    exact (mem_threeHighEligibleTripleList B _ S).mpr
      (((mem_threeHighResolutionDomain B _ (F k)).mp (hF k)).1 hS)
  exact threeHighListedDistinctJointSearch_of_families B _ _ F hF hD hcompat hcap

def threeHighCachedDistinctJointSearch (B : Fin 24 → Fin 24 → Bool) : Bool :=
  let adjacency := Vector.ofFn (fun i => Vector.ofFn (B i))
  let cachedB := fun i j => (adjacency.get i).get j
  let table := threeHighSupportTableClosure cachedB
    (fun k => (threeHighCanonicalTripleShapes k).filter (threeHighTripleNoCommonNeighbor cachedB))
  threeHighListedDistinctJointSearch cachedB table.get threeHighCanonicalResidual

theorem threeHighCachedDistinctJointSearch_eq (B : Fin 24 → Fin 24 → Bool) :
    threeHighCachedDistinctJointSearch B = threeHighDistinctJointSearch B := by
  have hb : (fun i j => ((Vector.ofFn (fun i => Vector.ofFn (B i))).get i).get j) = B := by
    funext i j
    simp
  simp only [threeHighCachedDistinctJointSearch, hb,
    threeHighSupportTableClosure_eq, threeHighDistinctJointSearch]

theorem threeHighCachedDistinctJointSearch_sound
    (B : Fin 24 → Fin 24 → Bool) (hB : ThreeHighDistinctJointWitness B) :
    threeHighCachedDistinctJointSearch B = true := by
  rw [threeHighCachedDistinctJointSearch_eq]
  exact threeHighDistinctJointSearch_sound B hB

end Erdos85

#print axioms Erdos85.threeHighListedDistinctJointSearch_of_families
#print axioms Erdos85.threeHighDistinctJointSearch_sound
#print axioms Erdos85.threeHighCachedDistinctJointSearch_eq
#print axioms Erdos85.threeHighCachedDistinctJointSearch_sound
