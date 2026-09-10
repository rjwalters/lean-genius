import Proofs.Erdos85ThreeHighJointResolutionSearch
import Proofs.Erdos85ThreeHighPrunedBlockFamilySearch

namespace Erdos85

/-- Later colors reject reused pairs as soon as a partial family creates them. -/
def threeHighPrunedJointResolutionSearch (B : Fin 24 → Fin 24 → Bool)
    (residuals blocks : Fin 3 → Finset (Fin 24)) : Bool :=
  threeHighBlockFamilySearch B (residuals 0) blocks fun F =>
    threeHighPrunedBlockFamilySearch B (residuals 1) blocks F fun K =>
      threeHighFamilyPairCompatible B F K &&
        threeHighPrunedBlockFamilySearch B (residuals 2) blocks (F ∪ K) fun L =>
          threeHighFamilyPairCompatible B F L && threeHighFamilyPairCompatible B K L

theorem threeHighPrunedJointResolutionSearch_of_families
    (B : Fin 24 → Fin 24 → Bool) (residuals blocks : Fin 3 → Finset (Fin 24))
    (F : Fin 3 → ThreeHighResolutionFamily)
    (hF : ∀ k, F k ∈ threeHighResolutionDomain B (residuals k))
    (hblocks : ∀ k S, S ∈ F k → encodedTripleBlockCap blocks S = true)
    (hcompat : ∀ i j, i ≠ j → encodedFamilyCompatibility B (F i) (F j) = true)
    (hcap : ∀ i j, i ≠ j → encodedFamilyIntersectionCap (F i) (F j) = true) :
    threeHighPrunedJointResolutionSearch B residuals blocks = true := by
  have hp (i j : Fin 3) (hij : i ≠ j) : threeHighFamilyPairCompatible B (F i) (F j) = true := by
    simp only [threeHighFamilyPairCompatible, Bool.and_eq_true]
    exact ⟨⟨hcompat i j hij, hcompat j i hij.symm⟩, hcap i j hij⟩
  unfold threeHighPrunedJointResolutionSearch
  apply threeHighBlockFamilySearch_of_mem B _ blocks _ (F 0) (hF 0) (hblocks 0)
  apply threeHighPrunedBlockFamilySearch_of_mem B _ blocks (F 0) _ (F 1)
    (hF 1) (hblocks 1) (hcap 1 0 (by decide))
  simp only [Bool.and_eq_true]
  refine ⟨hp 0 1 (by decide), ?_⟩
  apply threeHighPrunedBlockFamilySearch_of_mem B _ blocks (F 0 ∪ F 1) _ (F 2)
    (hF 2) (hblocks 2)
    (encodedFamilyIntersectionCap_union_right _ _ _ (hcap 2 0 (by decide)) (hcap 2 1 (by decide)))
  simp only [Bool.and_eq_true]
  exact ⟨hp 0 2 (by decide), hp 1 2 (by decide)⟩

end Erdos85
#print axioms Erdos85.threeHighPrunedJointResolutionSearch_of_families
