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

/-- At every binary square order, the triangle-free edge graph is nonempty.
This is the uniform version of the order-64 necessity theorem. -/
theorem binarySquare_regular_triangleFreeEdge_edgeFinset_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {k : ℕ} (hk : 1 ≤ k)
    (hreg : ∀ x, G.degree x = 2 ^ k)
    (hcard : Fintype.card V = (2 ^ k) * (2 ^ k)) :
    (triangleFreeEdgeGraph G).edgeFinset.Nonempty := by
  obtain ⟨z, hz⟩ :=
    binarySquare_regular_triangleFreeEdge_card_eq_three_mul_add_pow
      G hfree hk hreg hcard
  by_contra hempty
  have hcardZero : (triangleFreeEdgeGraph G).edgeFinset.card = 0 := by
    rw [Finset.card_eq_zero]
    exact Finset.not_nonempty_iff_eq_empty.mp hempty
  have hzmod := congrArg (fun a : ℤ => (a : ZMod 3)) hz
  rw [hcardZero] at hzmod
  push_cast at hzmod
  have hthree : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
  rw [hthree, zero_mul, zero_add] at hzmod
  exact (pow_ne_zero (3 * k - 1) (by decide : (2 : ZMod 3) ≠ 0)) hzmod.symm

end


end Erdos85

#print axioms
  Erdos85.binarySquare_regular_triangleFreeEdge_card_eq_pow_sub_three_mul_triangles
#print axioms
  Erdos85.binarySquare_regular_triangleFreeEdge_card_eq_three_mul_add_pow
#print axioms
  Erdos85.binarySquare_regular_triangleFreeEdge_edgeFinset_nonempty
