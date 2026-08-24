import Proofs.Erdos85ExceptionalCoreCliqueSaturation
import Proofs.Erdos85BinarySquareRegularParity

/-!
# Binary-square exceptional-core fixed vector

In a `q`-regular `C₄`-free graph on `q²` vertices, the second-order defect
graph is `(q-1)`-regular.  Consequently a `q`-point exceptional defect
clique is automatically saturated.  Two vertices in its empty part then
give a binary fixed vector of the defect adjacency matrix.
-/

open SimpleGraph

namespace Erdos85

/-- The binary-square hypotheses supply the defect-degree inputs needed by
exceptional-core clique saturation.  Thus the structural full/empty clique
alone forces the two-pole indicator to be fixed by the defect matrix. -/
theorem binarySquare_adjMatrix_mulVec_twoCoordinate_eq_self_of_exceptionalCore
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcardV : Fintype.card V = q * q)
    (full empty : Finset V) (hdisj : Disjoint full empty)
    (hcardCore : (full ∪ empty).card = q)
    (hclique : ∀ ⦃u v⦄, u ∈ full ∪ empty → v ∈ full ∪ empty →
      u ≠ v → (secondOrderDefectGraph G).Adj u v)
    (pole₁ pole₂ : V) (hpole₁ : pole₁ ∈ empty) (hpole₂ : pole₂ ∈ empty)
    (hpoles : pole₁ ≠ pole₂) :
    ((secondOrderDefectGraph G).adjMatrix (ZMod 2)).mulVec
        (Pi.single pole₁ 1 + Pi.single pole₂ 1) =
      Pi.single pole₁ 1 + Pi.single pole₂ 1 := by
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcardV]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDdegree : ∀ z : V, (secondOrderDefectGraph G).degree z = q - 1 := by
    intro z
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus z
    change (secondOrderDefectGraph G).degree z = (q - 3) + 2 at h
    omega
  exact adjMatrix_mulVec_twoCoordinate_eq_self_of_exceptionalCore_clique
    (secondOrderDefectGraph G) full empty hdisj hcardCore hclique
    pole₁ pole₂ hpole₁ hpole₂ hpoles (hDdegree pole₁) (hDdegree pole₂)

end Erdos85

#print axioms Erdos85.binarySquare_adjMatrix_mulVec_twoCoordinate_eq_self_of_exceptionalCore
