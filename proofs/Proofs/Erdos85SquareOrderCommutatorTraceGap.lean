import Proofs.Erdos85SquareOrderCommutatorFrobenius

/-!
# The square-order mixed fourth-moment gap

The exact Frobenius mass of the adjacency/defect commutator is equivalently
an exact gap between the two cyclic fourth words `A²D²` and `ADAD`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem neg_trace_commutator_sq_eq_sum_entry_sq_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A D : Matrix ι ι ℤ)
    (hA : ∀ x y, A x y = A y x)
    (hD : ∀ x y, D x y = D y x) :
    -Matrix.trace ((A * D - D * A) * (A * D - D * A)) =
      ∑ x, ∑ y, ((A * D - D * A) x y) ^ 2 := by
  let C := A * D - D * A
  have hskew : ∀ x y, C y x = -C x y := by
    intro x y
    dsimp [C]
    simp only [Matrix.mul_apply]
    have hAD : ∑ z, A y z * D z x = ∑ z, D x z * A z y := by
      apply Finset.sum_congr rfl
      intro z _
      rw [hA y z, hD z x, mul_comm]
    have hDA : ∑ z, D y z * A z x = ∑ z, A x z * D z y := by
      apply Finset.sum_congr rfl
      intro z _
      rw [hD y z, hA z x, mul_comm]
    rw [hAD, hDA]
    ring
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro y _
  have hs := hskew x y
  change (A * D - D * A) y x = -(A * D - D * A) x y at hs
  rw [hs]
  ring

private theorem trace_commutator_sq_expansion_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A D : Matrix ι ι ℤ) :
    Matrix.trace ((A * D - D * A) * (A * D - D * A)) =
      2 * (Matrix.trace ((A * D) * (A * D)) -
        Matrix.trace ((A * A) * (D * D))) := by
  have hcross : Matrix.trace ((A * D) * (D * A)) =
      Matrix.trace ((A * A) * (D * D)) := by
    calc
      Matrix.trace ((A * D) * (D * A)) =
          Matrix.trace (((A * D) * D) * A) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace (A * ((A * D) * D)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((A * A) * (D * D)) := by
        congr 1
        noncomm_ring
  have hcross' : Matrix.trace ((D * A) * (A * D)) =
      Matrix.trace ((A * A) * (D * D)) := by
    rw [Matrix.trace_mul_comm]
    exact hcross
  have halt : Matrix.trace ((D * A) * (D * A)) =
      Matrix.trace ((A * D) * (A * D)) := by
    calc
      Matrix.trace ((D * A) * (D * A)) =
          Matrix.trace (((D * A) * D) * A) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace (A * ((D * A) * D)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((A * D) * (A * D)) := by
        congr 1
        noncomm_ring
  rw [sub_mul, mul_sub, mul_sub, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_sub, hcross, hcross', halt]
  ring

/-- The positive-high commutator support is exactly the failure of the two
mixed fourth moments to agree.  This is the trace form suited to spectral
inequalities. -/
theorem squareOrder_trace_adj_sq_defect_sq_sub_alternating
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    let H := squareOrderHighVertices G d
    let A := G.adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    Matrix.trace ((A * A) * (D * D)) -
        Matrix.trace ((A * D) * (A * D)) =
      (H.card : ℤ) * ((d * d - H.card - (d + 1) : Nat) : ℤ) := by
  classical
  let H := squareOrderHighVertices G d
  let A := G.adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  let C := A * D - D * A
  dsimp only
  have hAsym : ∀ x y, A x y = A y x := by
    intro x y
    have ht : (G.adjMatrix ℤ).transpose = G.adjMatrix ℤ :=
      SimpleGraph.transpose_adjMatrix G
    have he := congrFun (congrFun ht y) x
    simpa [A] using he
  have hDsym : ∀ x y, D x y = D y x := by
    intro x y
    have ht : ((secondOrderDefectGraph G).adjMatrix ℤ).transpose =
        (secondOrderDefectGraph G).adjMatrix ℤ :=
      SimpleGraph.transpose_adjMatrix (secondOrderDefectGraph G)
    have he := congrFun (congrFun ht y) x
    simpa [D] using he
  have hmass := squareOrder_sum_commutator_entry_sq
    G hfree hd hmin hcover hcard
  change (∑ x : V, ∑ y : V, C x y * C x y) =
    2 * (H.card : ℤ) *
      ((d * d - H.card - (d + 1) : Nat) : ℤ) at hmass
  have htraceMass : (∑ x : V, ∑ y : V, C x y * C x y) =
      2 * (Matrix.trace ((A * A) * (D * D)) -
        Matrix.trace ((A * D) * (A * D))) := by
    calc
      (∑ x : V, ∑ y : V, C x y * C x y) =
          -Matrix.trace (C * C) := by
        have h := (neg_trace_commutator_sq_eq_sum_entry_sq_local
          A D hAsym hDsym).symm
        simpa [C, pow_two] using h
      _ = 2 * (Matrix.trace ((A * A) * (D * D)) -
          Matrix.trace ((A * D) * (A * D))) := by
        rw [trace_commutator_sq_expansion_local]
        ring
  rw [hmass] at htraceMass
  nlinarith

end

end Erdos85
