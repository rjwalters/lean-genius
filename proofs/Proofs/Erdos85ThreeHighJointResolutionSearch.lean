import Proofs.Erdos85OrderFortyNineThreeHighTripleColorFamilyIntersection
import Proofs.Erdos85ThreeHighBlockFamilySearch

namespace Erdos85

abbrev ThreeHighResolutionFamily := Finset (Finset (Fin 24))

def threeHighFamilyPairCompatible (B : Fin 24 → Fin 24 → Bool)
    (F K : ThreeHighResolutionFamily) : Bool :=
  encodedFamilyCompatibility B F K && encodedFamilyCompatibility B K F &&
    encodedFamilyIntersectionCap F K

/-- Nested continuation searches retain all three chosen families. -/
def threeHighJointFamilySearch (B : Fin 24 → Fin 24 → Bool)
    (search : Fin 3 → (ThreeHighResolutionFamily → Bool) → Bool) : Bool :=
  search 0 fun F =>
    search 1 fun K =>
      threeHighFamilyPairCompatible B F K &&
        search 2 fun L =>
          threeHighFamilyPairCompatible B F L && threeHighFamilyPairCompatible B K L

/-- The same three actual families survive every pairwise compatibility gate. -/
theorem threeHighJointFamilySearch_witness
    (B : Fin 24 → Fin 24 → Bool)
    (search : Fin 3 → (ThreeHighResolutionFamily → Bool) → Bool)
    (F : Fin 3 → ThreeHighResolutionFamily)
    (hsearch : ∀ k accept, accept (F k) = true → search k accept = true)
    (hcompat : ∀ i j, i ≠ j → encodedFamilyCompatibility B (F i) (F j) = true)
    (hcap : ∀ i j, i ≠ j → encodedFamilyIntersectionCap (F i) (F j) = true) :
    threeHighJointFamilySearch B search = true := by
  have hp (i j : Fin 3) (hij : i ≠ j) : threeHighFamilyPairCompatible B (F i) (F j) = true := by
    simp only [threeHighFamilyPairCompatible, Bool.and_eq_true]
    exact ⟨⟨hcompat i j hij, hcompat j i hij.symm⟩, hcap i j hij⟩
  unfold threeHighJointFamilySearch
  apply hsearch 0
  apply hsearch 1
  simp only [Bool.and_eq_true]
  refine ⟨hp 0 1 (by decide), ?_⟩
  apply hsearch 2
  simp only [Bool.and_eq_true]
  exact ⟨hp 0 2 (by decide), hp 1 2 (by decide)⟩

def threeHighJointResolutionSearch (B : Fin 24 → Fin 24 → Bool)
    (residuals blocks : Fin 3 → Finset (Fin 24)) : Bool :=
  threeHighJointFamilySearch B (fun k => threeHighBlockFamilySearch B (residuals k) blocks)

theorem threeHighJointResolutionSearch_of_families
    (B : Fin 24 → Fin 24 → Bool) (residuals blocks : Fin 3 → Finset (Fin 24))
    (F : Fin 3 → ThreeHighResolutionFamily)
    (hF : ∀ k, F k ∈ threeHighResolutionDomain B (residuals k))
    (hblocks : ∀ k S, S ∈ F k → encodedTripleBlockCap blocks S = true)
    (hcompat : ∀ i j, i ≠ j → encodedFamilyCompatibility B (F i) (F j) = true)
    (hcap : ∀ i j, i ≠ j → encodedFamilyIntersectionCap (F i) (F j) = true) :
    threeHighJointResolutionSearch B residuals blocks = true := by
  apply threeHighJointFamilySearch_witness B _ F _ hcompat hcap
  intro k accept ha
  exact threeHighBlockFamilySearch_of_mem B (residuals k) blocks accept (F k)
    (hF k) (hblocks k) ha

end Erdos85
#print axioms Erdos85.threeHighJointFamilySearch_witness
#print axioms Erdos85.threeHighJointResolutionSearch_of_families
