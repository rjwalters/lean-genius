import Proofs.Erdos85SquareOrderHighDifferenceQuadratic

/-!
# The doubled high-difference quadratic sector

Coordinate differences of high vertices are supported on the high sector,
whereas adjacency-row differences of high vertices vanish there.  The two
independent families therefore combine into one independent family of size
`2(|H|-1)`.  Adjacency exchanges the two halves, with product `d`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

def squareOrderHighQuadraticSectorFamily
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (a : V) :
    Sum {x // x ∈ H.erase a} {x // x ∈ H.erase a} → (V → ℚ)
  | Sum.inl b => coordinateDifferenceRat b.1 a
  | Sum.inr b => squareOrderHighRowDifferenceRat G b.1 a

theorem squareOrder_adjMatrixRat_mulVec_highQuadraticSectorFamily_inl
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (a : V) (b : {x // x ∈ H.erase a}) :
    (G.adjMatrix ℚ).mulVec
        (squareOrderHighQuadraticSectorFamily G H a (Sum.inl b)) =
      squareOrderHighQuadraticSectorFamily G H a (Sum.inr b) := by
  funext x
  simp only [squareOrderHighQuadraticSectorFamily, Matrix.mulVec, dotProduct,
    coordinateDifferenceRat, squareOrderHighRowDifferenceRat]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp [G.adj_comm]

theorem squareOrder_adjMatrixRat_mulVec_highQuadraticSectorFamily_inr
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcard : Fintype.card V = d * d)
    (H : Finset V) (a : V) (b : {x // x ∈ H.erase a})
    (hb : G.degree b.1 = d + 1) (ha : G.degree a = d + 1) :
    (G.adjMatrix ℚ).mulVec
        (squareOrderHighQuadraticSectorFamily G H a (Sum.inr b)) =
      (d : ℚ) • squareOrderHighQuadraticSectorFamily G H a (Sum.inl b) := by
  funext x
  have hx := congrFun
    (squareOrder_adjMatrixRat_mulVec_highRowDifferenceRat
      G hfree hd hmin hcard hb ha) x
  simpa [squareOrderHighQuadraticSectorFamily, Pi.smul_apply] using hx

theorem squareOrder_highQuadraticSectorFamily_linearIndependent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a : V} (ha : a ∈ squareOrderHighVertices G d) :
    LinearIndependent ℚ
      (squareOrderHighQuadraticSectorFamily
        G (squareOrderHighVertices G d) a) := by
  classical
  let H := squareOrderHighVertices G d
  let E := {x // x ∈ H.erase a}
  let coords : E → (V → ℚ) := fun b => coordinateDifferenceRat b.1 a
  let rows : E → (V → ℚ) := fun b => squareOrderHighRowDifferenceRat G b.1 a
  have hcoord : LinearIndependent ℚ coords := by
    simpa [H, E, coords] using coordinateDifferencesRat_linearIndependent H a
  have hrows : LinearIndependent ℚ rows := by
    simpa [H, E, rows] using
      squareOrder_highRowDifferencesRat_linearIndependent
        G hfree hd hmin hcard ha
  have hnotAdj : ∀ {x y : V}, x ∈ H → y ∈ H → ¬ G.Adj x y := by
    intro x y hx hy hxy
    exact squareOrder_not_adj_degree_succ_of_tightEdgeCover G hcover
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 hxy
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hleft : (∑ b : E, g (Sum.inl b) • coords b) = 0 := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hx : x ∈ H
    · have hxg := congrFun hg x
      rw [Fintype.sum_sum_type] at hxg
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, squareOrderHighQuadraticSectorFamily] at hxg
      change (∑ b : E, g (Sum.inl b) * coords b x) +
          (∑ b : E, g (Sum.inr b) * rows b x) = 0 at hxg
      have hrowzero :
          (∑ b : E, g (Sum.inr b) * rows b x) = 0 := by
        apply Finset.sum_eq_zero
        intro b _hb
        have hbH : b.1 ∈ H := Finset.mem_of_mem_erase b.2
        have hba : ¬ G.Adj b.1 x := hnotAdj hbH hx
        have hax : ¬ G.Adj a x := hnotAdj ha hx
        simp [rows, squareOrderHighRowDifferenceRat,
          SimpleGraph.adjMatrix_apply, hba, hax]
      rw [hrowzero, add_zero] at hxg
      exact hxg
    ·
      apply Finset.sum_eq_zero
      intro b _hb
      have hbH : b.1 ∈ H := Finset.mem_of_mem_erase b.2
      have hxb : x ≠ b.1 := fun h => hx (h ▸ hbH)
      have hxa : x ≠ a := fun h => hx (h ▸ ha)
      simp [coords, coordinateDifferenceRat, hxb, hxa]
  have hgleft : ∀ b : E, g (Sum.inl b) = 0 :=
    Fintype.linearIndependent_iff.mp hcoord (fun b => g (Sum.inl b)) hleft
  have hright : (∑ b : E, g (Sum.inr b) • rows b) = 0 := by
    have hsplit := hg
    rw [Fintype.sum_sum_type] at hsplit
    have hleftzero : (∑ b : E, g (Sum.inl b) •
        squareOrderHighQuadraticSectorFamily G H a (Sum.inl b)) = 0 := by
      apply Finset.sum_eq_zero
      intro b _hb
      rw [hgleft b]
      simp
    rw [hleftzero, zero_add] at hsplit
    simpa [H, E, rows, squareOrderHighQuadraticSectorFamily] using hsplit
  have hgright : ∀ b : E, g (Sum.inr b) = 0 :=
    Fintype.linearIndependent_iff.mp hrows (fun b => g (Sum.inr b)) hright
  cases i with
  | inl b => exact hgleft b
  | inr b => exact hgright b

end

end Erdos85
