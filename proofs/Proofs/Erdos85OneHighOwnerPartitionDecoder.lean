import Proofs.Erdos85OneHighOddProfileSeparatedRepeat
import Proofs.Erdos85FourPairPartitionGeometry

/-!
# Decode odd-profile owner partition codes

The finite odd-profile classifier records each transversal by a `Fin 3`
partition code.  These lemmas expose the corresponding edge of the three
perfect matchings of the four canonical root pairs, in exactly the form used
by the star-or-triangle coherence theorem.
-/

namespace Erdos85

theorem oneHighOwnerPartitionCode_zero_edge
    (i j : Fin 8) (hij : i ≠ j)
    (hjm : j ≠ oneHighStandardMate i)
    (hcode : (oneHighOwnerPartitionCode i j == 0) = true) :
    finFourEdge (oneHighRootPair i) (oneHighRootPair j) = finFourEdge 0 1 ∨
      finFourEdge (oneHighRootPair i) (oneHighRootPair j) =
        finFourEdge 2 3 := by
  decide +revert

theorem oneHighOwnerPartitionCode_one_edge
    (i j : Fin 8) (hij : i ≠ j)
    (hjm : j ≠ oneHighStandardMate i)
    (hcode : (oneHighOwnerPartitionCode i j == 1) = true) :
    finFourEdge (oneHighRootPair i) (oneHighRootPair j) = finFourEdge 0 2 ∨
      finFourEdge (oneHighRootPair i) (oneHighRootPair j) =
        finFourEdge 1 3 := by
  decide +revert

theorem oneHighOwnerPartitionCode_two_edge
    (i j : Fin 8) (hij : i ≠ j)
    (hjm : j ≠ oneHighStandardMate i)
    (hcode : (oneHighOwnerPartitionCode i j == 2) = true) :
    finFourEdge (oneHighRootPair i) (oneHighRootPair j) = finFourEdge 0 3 ∨
      finFourEdge (oneHighRootPair i) (oneHighRootPair j) =
        finFourEdge 1 2 := by
  decide +revert

/-- Three separated owner witnesses, one for each partition code, have star
or triangle geometry after quotienting the eight labels by standard mates. -/
theorem oneHigh_threeOwnerPartitions_star_or_triangle
    (i₀ j₀ i₁ j₁ i₂ j₂ : Fin 8)
    (hne₀ : i₀ ≠ j₀) (hmate₀ : j₀ ≠ oneHighStandardMate i₀)
    (hcode₀ : (oneHighOwnerPartitionCode i₀ j₀ == 0) = true)
    (hne₁ : i₁ ≠ j₁) (hmate₁ : j₁ ≠ oneHighStandardMate i₁)
    (hcode₁ : (oneHighOwnerPartitionCode i₁ j₁ == 1) = true)
    (hne₂ : i₂ ≠ j₂) (hmate₂ : j₂ ≠ oneHighStandardMate i₂)
    (hcode₂ : (oneHighOwnerPartitionCode i₂ j₂ == 2) = true) :
    (∃ z : Fin 4,
      z ∈ finFourEdge (oneHighRootPair i₀) (oneHighRootPair j₀) ∧
      z ∈ finFourEdge (oneHighRootPair i₁) (oneHighRootPair j₁) ∧
      z ∈ finFourEdge (oneHighRootPair i₂) (oneHighRootPair j₂)) ∨
    ((finFourEdge (oneHighRootPair i₀) (oneHighRootPair j₀) ∪
        finFourEdge (oneHighRootPair i₁) (oneHighRootPair j₁)) ∪
      finFourEdge (oneHighRootPair i₂) (oneHighRootPair j₂)).card = 3 := by
  apply finFour_complementaryChoices_star_or_triangle
  · exact oneHighOwnerPartitionCode_zero_edge i₀ j₀ hne₀ hmate₀ hcode₀
  · exact oneHighOwnerPartitionCode_one_edge i₁ j₁ hne₁ hmate₁ hcode₁
  · exact oneHighOwnerPartitionCode_two_edge i₂ j₂ hne₂ hmate₂ hcode₂

end Erdos85

#print axioms Erdos85.oneHighOwnerPartitionCode_zero_edge
#print axioms Erdos85.oneHighOwnerPartitionCode_one_edge
#print axioms Erdos85.oneHighOwnerPartitionCode_two_edge
#print axioms Erdos85.oneHigh_threeOwnerPartitions_star_or_triangle
