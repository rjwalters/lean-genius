import Proofs.Erdos85NonregularDefectOperator
import Proofs.Erdos85OrderFortyNineIncidence
import Proofs.Erdos85OrderFortyNineStratification

/-!
# The order-49 adjacency matrix as an integral square root

At order 49 and minimum degree seven, every degree is seven or eight.  Thus
the nonregular diagonal in the universal defect identity is `6I + E_H`,
where `E_H` is the diagonal indicator of the degree-eight sector.  This is
the matrix interface for exact spectral certificates in the order-49 lab.
-/

open SimpleGraph

namespace Erdos85

/-- The diagonal indicator matrix of the degree-eight vertices. -/
def orderFortyNineHighDiagonal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℤ :=
  Matrix.diagonal fun x ↦ if x ∈ orderFortyNineHighVertices G then 1 else 0

@[simp] theorem orderFortyNineHighDiagonal_apply_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    orderFortyNineHighDiagonal G x x =
      if x ∈ orderFortyNineHighVertices G then 1 else 0 := by
  simp [orderFortyNineHighDiagonal]

theorem orderFortyNineHighDiagonal_apply_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V} (hxy : x ≠ y) :
    orderFortyNineHighDiagonal G x y = 0 := by
  simp [orderFortyNineHighDiagonal, hxy]

/-- In the order-49 degree band, the degree-minus-one diagonal is exactly
`6I` plus the indicator of the high sector. -/
theorem orderFortyNine_degreePredDiagonal_eq_six_add_highDiagonal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) :
    degreePredDiagonal G =
      (6 : ℤ) • (1 : Matrix V V ℤ) + orderFortyNineHighDiagonal G := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [degreePredDiagonal_apply_self, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply,
      orderFortyNineHighDiagonal_apply_self, smul_eq_mul]
    rcases orderFortyNine_degree_eq_seven_or_eight
        G hfree hmin hcard x with hx7 | hx8
    · have hxnot : x ∉ orderFortyNineHighVertices G := by
        simp [orderFortyNineHighVertices, hx7]
      simp [hx7, hxnot]
    · have hxmem : x ∈ orderFortyNineHighVertices G := by
        simp [orderFortyNineHighVertices, hx8]
      simp [hx8, hxmem]
  · rw [degreePredDiagonal_apply_of_ne G hxy, Matrix.add_apply,
      orderFortyNineHighDiagonal_apply_of_ne G hxy]
    simp [Matrix.smul_apply, hxy]

/-- **Order-49 square-root identity.**  The integral adjacency matrix is a
symmetric square root of `6I + E_H + J - M`, with `M` the second-order defect
adjacency matrix. -/
theorem orderFortyNine_adjMatrix_sq_eq_six_add_high_add_ones_sub_defect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) :
    G.adjMatrix ℤ * G.adjMatrix ℤ =
      (6 : ℤ) • (1 : Matrix V V ℤ) + orderFortyNineHighDiagonal G +
        FriendshipTheoremOQ01.onesMatrix V -
          (secondOrderDefectGraph G).adjMatrix ℤ := by
  rw [adjMatrix_sq_eq_degreePredDiagonal_add_ones_sub_secondOrderDefect
    G hfree,
    orderFortyNine_degreePredDiagonal_eq_six_add_highDiagonal
      G hfree hmin hcard]

end Erdos85
