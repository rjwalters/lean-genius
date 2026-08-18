import Proofs.Erdos85EvenExcessOnePathSector
import Proofs.Erdos85DefectSecondMixedMoment

/-!
# Third moment and defect-triangle colors at even-degree excess one

Two pieces of the even-degree excess-one moment system.

First, the pure third moment: multiplying `A² = (d-1)I + J - D` by `A`
and taking traces gives `tr A³ = nd - tr(AD)`, and at even degree with
excess one the landed identity `tr(AD) = 2|S|` (with `S` the degree-two
triangle-free sector) turns this into `tr A³ = nd - 2|S|`.  Since
`tr A³` counts closed triangles, the path sector controls the total
triangle count of the graph.

Second, the color census of defect triangles: a triangle of the combined
defect graph `D = C ⊔ T` can contain at most one triangle-free edge.
Two adjacent `T`-edges closed by a `T`-edge would form a triangle of
triangle-free edges, and closed by a `C`-edge would put a common
neighbor on an antipodal pair.  So `D`-triangles are of type `CCC` or
`TCC` only, which pins `tr D³` to the antipodal geometry.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The trace of `A·J` for a `d`-regular graph is `n·d`. -/
theorem trace_adjMatrix_mul_onesMatrix_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hreg : ∀ x, G.degree x = d) :
    Matrix.trace (G.adjMatrix ℤ * FriendshipTheoremOQ01.onesMatrix V) =
      (Fintype.card V : ℤ) * d := by
  have hrow : ∀ x : V,
      (G.adjMatrix ℤ * FriendshipTheoremOQ01.onesMatrix V) x x = (d : ℤ) := by
    intro x
    rw [Matrix.mul_apply]
    simp only [FriendshipTheoremOQ01.onesMatrix, Matrix.of_apply, mul_one,
      SimpleGraph.adjMatrix_apply]
    rw [Finset.sum_boole]
    have hfilt : Finset.univ.filter (fun y => G.Adj x y) =
        G.neighborFinset x := by
      ext y
      simp [SimpleGraph.mem_neighborFinset]
    rw [hfilt, G.card_neighborFinset_eq_degree, hreg x]
  rw [Matrix.trace]
  calc
    ∑ x, Matrix.diag
        (G.adjMatrix ℤ * FriendshipTheoremOQ01.onesMatrix V) x
        = ∑ _x : V, (d : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      exact hrow x
    _ = (Fintype.card V : ℤ) * d := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Third moment.**  At even degree and excess one,
`tr A³ = nd - 2|S|` with `S` the degree-two triangle-free sector. -/
theorem trace_adjMatrix_cube_even_excessOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    Matrix.trace (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) =
      (Fintype.card V : ℤ) * d -
        2 * ((Finset.univ.filter fun x : V =>
          (triangleFreeEdgeGraph G).degree x = 2).card : ℤ) := by
  have hsq := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
  have hexp : G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ =
      (↑d - 1 : ℤ) • G.adjMatrix ℤ +
        G.adjMatrix ℤ * FriendshipTheoremOQ01.onesMatrix V -
          G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ := by
    calc
      G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
          = G.adjMatrix ℤ * (G.adjMatrix ℤ * G.adjMatrix ℤ) := by
        rw [Matrix.mul_assoc]
      _ = G.adjMatrix ℤ *
          ((↑d - 1 : ℤ) • (1 : Matrix V V ℤ) +
            FriendshipTheoremOQ01.onesMatrix V -
              (secondOrderDefectGraph G).adjMatrix ℤ) := by
        rw [hsq]
      _ = _ := by
        rw [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
  rw [hexp, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul,
    SimpleGraph.trace_adjMatrix,
    trace_adjMatrix_mul_onesMatrix_of_regular G hreg,
    trace_adjMatrix_mul_secondOrderDefect_even_excessOne
      G hfree heven hreg hcard,
    smul_zero, zero_add]

/-- Two triangle-free edges and an antipodal edge cannot close into a
triangle: the shared endpoint of the triangle-free edges is a common
neighbor of the antipodal pair. -/
theorem false_of_triangleFree_triangleFree_antipodal_triangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y z : V} (hxy : (triangleFreeEdgeGraph G).Adj x y)
    (hyz : (triangleFreeEdgeGraph G).Adj y z)
    (hzx : (antipodalGraph G).Adj z x) : False :=
  false_of_adj_antipodal_triangleFree_triangle G
    ((mem_triangleFreeNeighbors G y z).mp hyz).1 hzx hxy

/-- **Defect-triangle color census.**  In a triangle of the combined
defect graph, no two adjacent edges are both triangle-free: every
`D`-triangle is of color type `CCC` or `TCC`. -/
theorem not_two_adjacent_triangleFree_in_defect_triangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y z : V} (hxy : (triangleFreeEdgeGraph G).Adj x y)
    (hyz : (triangleFreeEdgeGraph G).Adj y z)
    (hzx : (secondOrderDefectGraph G).Adj z x) : False := by
  simp only [secondOrderDefectGraph, SimpleGraph.sup_adj] at hzx
  rcases hzx with hC | hT
  · exact false_of_triangleFree_triangleFree_antipodal_triangle
      G hxy hyz hC
  · exact triangleFreeEdgeGraph_not_triangle G hxy hyz hT

end

end Erdos85
