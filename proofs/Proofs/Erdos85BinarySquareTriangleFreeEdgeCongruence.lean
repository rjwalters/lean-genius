import Proofs.Erdos85FifthMomentBridge
import Proofs.Erdos85OrderSixtyFourAllTwoTriangleLedger

/-!
# A binary square-order congruence for triangle-free edges

At order `q²` with regular degree `q = 2^k`, the cubic color partition and
handshaking give the exact formula

`#E(triangleFreeEdgeGraph G) = 2^(3k-1) - 3 * #triangles(G)`.

Thus the mod-three constraint found at order 64 is uniform in the binary
square-order parameter.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Exact binary square-order triangle-free edge ledger. -/
theorem binarySquare_regular_triangleFreeEdge_card_eq_pow_sub_three_mul_triangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {k : ℕ} (hk : 1 ≤ k)
    (hreg : ∀ x, G.degree x = 2 ^ k)
    (hcard : Fintype.card V = (2 ^ k) * (2 ^ k)) :
    ((triangleFreeEdgeGraph G).edgeFinset.card : ℤ) =
      (2 : ℤ) ^ (3 * k - 1) -
        3 * (adjacencyTriangleMinorFinset G).card := by
  have hcolor :=
    trace_adjMatrix_cube_add_colorTrace_eq_card_mul_degree_of_regular
      G hfree hreg
  rw [trace_adjMatrix_mul_secondOrderDefect_eq_sum_triangleFreeDegrees]
    at hcolor
  have htri := trace_adjMatrix_cube_eq_six_mul_triangleMinorCount
    G (by
      rw [hcard]
      have htwo : 2 ≤ 2 ^ k := by
        calc
          2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      nlinarith)
  rw [htri] at hcolor
  have hhand := (triangleFreeEdgeGraph G).sum_degrees_eq_twice_card_edges
  have hhandZ :
      (∑ x : V, ((triangleFreeEdgeGraph G).degree x : ℤ)) =
        2 * ((triangleFreeEdgeGraph G).edgeFinset.card : ℤ) := by
    exact_mod_cast hhand
  have hpow :
      (2 : ℤ) ^ k * (2 : ℤ) ^ k * (2 : ℤ) ^ k =
        2 * (2 : ℤ) ^ (3 * k - 1) := by
    rw [← pow_add, ← pow_add,
      show k + k + k = (3 * k - 1) + 1 by omega, pow_succ]
    ring
  rw [hcard] at hcolor
  norm_num at hcolor
  rw [hpow] at hcolor
  omega

/-- Congruence form: the triangle-free edge count differs from
`2^(3k-1)` by a multiple of three. -/
theorem binarySquare_regular_triangleFreeEdge_card_eq_three_mul_add_pow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {k : ℕ} (hk : 1 ≤ k)
    (hreg : ∀ x, G.degree x = 2 ^ k)
    (hcard : Fintype.card V = (2 ^ k) * (2 ^ k)) :
    ∃ z : ℤ,
      ((triangleFreeEdgeGraph G).edgeFinset.card : ℤ) =
        3 * z + (2 : ℤ) ^ (3 * k - 1) := by
  refine ⟨-((adjacencyTriangleMinorFinset G).card : ℤ), ?_⟩
  rw [binarySquare_regular_triangleFreeEdge_card_eq_pow_sub_three_mul_triangles
    G hfree hk hreg hcard]
  ring

end


end Erdos85

#print axioms
  Erdos85.binarySquare_regular_triangleFreeEdge_card_eq_pow_sub_three_mul_triangles
#print axioms
  Erdos85.binarySquare_regular_triangleFreeEdge_card_eq_three_mul_add_pow
