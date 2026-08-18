import Proofs.Erdos85OrderSixtyFourOutsideBlockOperator

/-! # The outside return operator vanishes on internal edges -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- An internal edge cannot support a three-step return walk through two
outside vertices: together they would form a four-cycle. -/
theorem outsideReturn_apply_eq_zero_of_induce_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (s : Set V) [DecidablePred (· ∈ s)]
    (u v : s) (huv : (G.induce s).Adj u v) :
    let p : V → Prop := fun x ↦ x ∈ s
    let q : Set V := {x | ¬p x}
    let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
    let C := (G.induce q).adjMatrix ℂ
    ((B * C) * Matrix.conjTranspose B) u v = 0 := by
  classical
  let p : V → Prop := fun x ↦ x ∈ s
  let q : Set V := {x | ¬p x}
  let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
  let C := (G.induce q).adjMatrix ℂ
  change ((B * C) * Matrix.conjTranspose B) u v = 0
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro y _
  by_cases hyv : G.Adj y.1 v.1
  · rw [Matrix.mul_apply]
    apply mul_eq_zero_of_left
    apply Finset.sum_eq_zero
    intro x _
    by_cases hux : G.Adj u.1 x.1
    · by_cases hxy : G.Adj x.1 y.1
      · exfalso
        have h_u_y : u.1 ≠ y.1 := fun h ↦ y.2 (h ▸ u.2)
        have h_x_v : x.1 ≠ v.1 := fun h ↦ x.2 (h ▸ v.2)
        have h_u_x : u.1 ≠ x.1 := fun h ↦ x.2 (h ▸ u.2)
        have h_v_y : v.1 ≠ y.1 := fun h ↦ y.2 (h ▸ v.2)
        have h_v_u : v.1 ≠ u.1 := fun h ↦
          (G.induce s).ne_of_adj huv (Subtype.ext h.symm)
        exact hfree (containsC4_of_rim hux hxy hyv huv.symm
          h_u_y h_x_v h_u_x.symm (G.ne_of_adj hxy)
          h_v_u h_v_y)
      · simp [B, C, Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply,
          hux, hxy]
    · simp [B, C, Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply, hux]
  · have hvy : ¬ G.Adj v.1 y.1 := fun h ↦ hyv h.symm
    simp [B, C, Matrix.toBlock_apply, Matrix.conjTranspose_apply,
      SimpleGraph.adjMatrix_apply, hvy]

/-- Any matrix vanishing on the edges of a graph has zero mixed trace with
its adjacency matrix. -/
theorem trace_adj_mul_eq_zero_of_apply_zero_on_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (M : Matrix V V ℂ)
    (hzero : ∀ {u v}, H.Adj u v → M u v = 0) :
    Matrix.trace (H.adjMatrix ℂ * M) = 0 := by
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  intro u _
  rw [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro v _
  by_cases huv : H.Adj u v
  · rw [hzero huv.symm]
    simp
  · simp [SimpleGraph.adjMatrix_apply, huv]

/-- Hence the internal adjacency and the outside return operator have zero
mixed trace. -/
theorem trace_induceAdj_mul_outsideReturn_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (s : Set V) [DecidablePred (· ∈ s)] :
    let p : V → Prop := fun x ↦ x ∈ s
    let q : Set V := {x | ¬p x}
    let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
    let C := (G.induce q).adjMatrix ℂ
    Matrix.trace ((G.induce s).adjMatrix ℂ *
      ((B * C) * Matrix.conjTranspose B)) = 0 := by
  classical
  let p : V → Prop := fun x ↦ x ∈ s
  let q : Set V := {x | ¬p x}
  let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
  let C := (G.induce q).adjMatrix ℂ
  apply trace_adj_mul_eq_zero_of_apply_zero_on_adj
  intro u v huv
  exact outsideReturn_apply_eq_zero_of_induce_adj G hfree s u v huv

end

end Erdos85
