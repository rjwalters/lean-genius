import Proofs.Erdos85ExteriorGramSecondMoment
import Proofs.Erdos85OrderSixtyFourSixteenBlockGramTrace

/-! # The exterior Gram pair graph on H16 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Two vertices of a defect component are paired when they share an ambient
neighbor outside that component. -/
def exteriorPairGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    SimpleGraph c.supp where
  Adj x y := x ≠ y ∧
    ∃ z : {z : V // z ∉ c.supp}, G.Adj x.1 z.1 ∧ G.Adj y.1 z.1
  symm := ⟨by
    intro x y
    rintro ⟨hxy, z, hx, hy⟩
    exact ⟨Ne.symm hxy, z, hy, hx⟩⟩
  loopless := ⟨by
    intro x
    exact fun h ↦ h.1 rfl⟩

instance exteriorPairGraph_adj_decidable
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    DecidableRel (exteriorPairGraph G c).Adj := by
  classical
  unfold exteriorPairGraph
  infer_instance

/-- In a C4-free graph, two distinct rows of an adjacency incidence matrix
have at most one common `1`. -/
private theorem exterior_commonNeighbor_subsingleton
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    {x y : c.supp} (hxy : x ≠ y) :
    Subsingleton
      {z : {z : V // z ∉ c.supp} // G.Adj x.1 z.1 ∧ G.Adj y.1 z.1} := ⟨by
  intro z w
  apply Subtype.ext
  apply Subtype.ext
  exact Finset.card_le_one.mp
    (common_le_one_of_not_containsC4 hfree x.1 y.1
      (fun h => hxy (Subtype.ext h))) z.1
      (by simp [z.2.1, z.2.2]) w.1 (by simp [w.2.1, w.2.2])⟩

/-- A symmetric complex matrix with diagonal `6`, Boolean off-diagonal
entries, and row sum `12` is exactly `6I` plus the adjacency matrix of a
six-regular simple graph.  Its first two moments are therefore fixed. -/
theorem exists_sixRegularGraph_of_six_diagonal_boolean_offDiagonal
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Matrix V V ℂ) (hcard : Fintype.card V = 16)
    (hsym : ∀ i j, Q i j = Q j i)
    (hdiag : ∀ i, Q i i = 6)
    (hoff : ∀ i j, i ≠ j → Q i j = 0 ∨ Q i j = 1)
    (hone : Q.mulVec (fun _ ↦ 1) = (12 : ℂ) • (fun _ ↦ 1)) :
    ∃ R : SimpleGraph V, ∃ _ : DecidableRel R.Adj, (∀ i, R.degree i = 6) ∧
      Q = (6 : ℂ) • (1 : Matrix V V ℂ) + R.adjMatrix ℂ ∧
      Matrix.trace Q = 96 ∧ Matrix.trace (Q * Q) = 672 := by
  classical
  let R : SimpleGraph V :=
    { Adj := fun i j ↦ i ≠ j ∧ Q i j = 1
      symm := ⟨by
        intro i j
        rintro ⟨hij, hq⟩
        exact ⟨Ne.symm hij, by rw [← hsym i j, hq]⟩⟩
      loopless := ⟨fun i h ↦ h.1 rfl⟩ }
  letI : DecidableRel R.Adj := Classical.decRel _
  have hQ : Q = (6 : ℂ) • (1 : Matrix V V ℂ) + R.adjMatrix ℂ := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [hdiag, R, SimpleGraph.adjMatrix_apply]
    · rcases hoff i j hij with hzero | hone'
      · simp [hij, hzero, R, SimpleGraph.adjMatrix_apply]
      · simp [hij, hone', R, SimpleGraph.adjMatrix_apply]
  have hreg : ∀ i, R.degree i = 6 := by
    intro i
    have hi := congrFun hone i
    rw [hQ] at hi
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.smul_apply, smul_eq_mul, mul_one] at hi
    have hadj := SimpleGraph.adjMatrix_mulVec_const_apply
      (G := R) (α := ℂ) (a := 1) (v := i)
    simp only [mul_one] at hadj
    have hi' : 6 + (R.adjMatrix ℂ).mulVec (fun _ ↦ 1) i = 12 := by
      simpa using hi
    have hu : (fun _ : V ↦ (1 : ℂ)) = Function.const V 1 := by
      funext x
      rfl
    rw [hu, hadj] at hi'
    have hiNat : 6 + R.degree i = 12 := by exact_mod_cast hi'
    omega
  have hmom := six_add_sixRegularAdj_trace_and_secondMoment R hcard hreg
  dsimp only at hmom
  rw [← hQ] at hmom
  exact ⟨R, inferInstance, hreg, hQ, hmom⟩

end

end Erdos85
