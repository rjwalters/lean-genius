import Proofs.Erdos85OneHighFourPairTransversal

/-!
# Geometry of the three complementary four-pair partitions

Choosing one edge from each perfect matching of `K₄` produces either the
three edges of a star or the three edges of a triangle.  This is the finite
coherence split needed when the odd one-high classification supplies a
transversal for every complementary partition.
-/

namespace Erdos85

def finFourEdge (a b : Fin 4) : Finset (Fin 4) := {a, b}

/-- One chosen edge from each of the three perfect matchings of `K₄` either
has a common endpoint (a star) or its endpoint union has cardinality three
(a triangle). -/
theorem finFour_complementaryChoices_star_or_triangle
    (a₀ b₀ a₁ b₁ a₂ b₂ : Fin 4)
    (h₀ : finFourEdge a₀ b₀ = finFourEdge 0 1 ∨
      finFourEdge a₀ b₀ = finFourEdge 2 3)
    (h₁ : finFourEdge a₁ b₁ = finFourEdge 0 2 ∨
      finFourEdge a₁ b₁ = finFourEdge 1 3)
    (h₂ : finFourEdge a₂ b₂ = finFourEdge 0 3 ∨
      finFourEdge a₂ b₂ = finFourEdge 1 2) :
    (∃ z : Fin 4,
      z ∈ finFourEdge a₀ b₀ ∧
      z ∈ finFourEdge a₁ b₁ ∧
      z ∈ finFourEdge a₂ b₂) ∨
    ((finFourEdge a₀ b₀ ∪ finFourEdge a₁ b₁) ∪
      finFourEdge a₂ b₂).card = 3 := by
  decide +revert

end Erdos85

#print axioms Erdos85.finFour_complementaryChoices_star_or_triangle
