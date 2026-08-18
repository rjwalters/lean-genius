import Proofs.Erdos85MuThreeMixedGridResidualEnergy

/-!
# Sum-of-squares rigidity for the mixed-grid residual sector

The slack in the residual energy bound is not merely nonnegative: twice the
slack is the sum of `(f u + f v)^2` over directed residual edges.  Equality
therefore forces `f` to change sign across every residual edge.
-/

open SimpleGraph

namespace Erdos85

/-- Exact directed-edge square identity for a finite regular graph. -/
theorem regularGraph_sum_neighbor_add_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hdeg : ∀ u, G.degree u = d)
    (f : V → ℤ) :
    (∑ u, ∑ v ∈ G.neighborFinset u, (f u + f v) ^ 2) =
      2 * ((d : ℤ) * (f ⬝ᵥ f) + f ⬝ᵥ (G.adjMatrix ℤ).mulVec f) := by
  have hfirst :
      (∑ u, ∑ _v ∈ G.neighborFinset u, f u * f u) =
        (d : ℤ) * (f ⬝ᵥ f) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    simp_rw [G.card_neighborFinset_eq_degree, hdeg]
    simp [dotProduct, Finset.mul_sum, mul_comm]
  have hsecond :
      (∑ u, ∑ v ∈ G.neighborFinset u, f v * f v) =
        (d : ℤ) * (f ⬝ᵥ f) := by
    rw [sum_neighborFinset_swap G (fun _u v => f v * f v)]
    exact hfirst
  have hcross :
      (∑ u, ∑ v ∈ G.neighborFinset u, 2 * (f u * f v)) =
        2 * (f ⬝ᵥ (G.adjMatrix ℤ).mulVec f) := by
    simp only [dotProduct, SimpleGraph.adjMatrix_mulVec_apply]
    simp_rw [Finset.mul_sum]
  simp_rw [show ∀ a b : ℤ, (a + b) ^ 2 = a * a + b * b + 2 * (a * b) by
    intro a b
    ring]
  simp_rw [Finset.sum_add_distrib]
  rw [hfirst, hsecond, hcross]
  ring

/-- Twice the free-sector energy slack is an exact sum of residual-edge
squares. -/
theorem MuThreeMixedGridCode.residual_edgeSquareSum_eq_energySlack
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {f : muThreeMixedCell K → ℤ}
    (hf : MixedGridZeroRowColumn K f) :
    (∑ u, ∑ v ∈ (mixedGridSquareResidualGraph K C).neighborFinset u,
        (f u + f v) ^ 2) =
      2 * (14 * (f ⬝ᵥ f) -
        ((C.adjMatrix ℤ).mulVec f) ⬝ᵥ ((C.adjMatrix ℤ).mulVec f)) := by
  have hsquare := regularGraph_sum_neighbor_add_sq
    (mixedGridSquareResidualGraph K C) 7
    (MuThreeMixedGridCode.squareResidualGraph_degree_eq_seven H K C code) f
  have haction := MuThreeMixedGridCode.residual_adjMatrix_mulVec_eq_on_zeroSector
    H K C code hf
  have hsymm := mixedGridIndicator_dot_adjMatrix_mulVec C f
    ((C.adjMatrix ℤ).mulVec f)
  rw [haction, dotProduct_sub, dotProduct_smul, smul_eq_mul, hsymm] at hsquare
  norm_num at hsquare ⊢
  linarith

/-- Equality in the exterior energy bound forces sign reversal across every
residual edge. -/
theorem MuThreeMixedGridCode.residual_adj_add_eq_zero_of_energy_eq_fourteen
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {f : muThreeMixedCell K → ℤ}
    (hf : MixedGridZeroRowColumn K f)
    (heq : ((C.adjMatrix ℤ).mulVec f) ⬝ᵥ ((C.adjMatrix ℤ).mulVec f) =
      14 * (f ⬝ᵥ f))
    {u v : muThreeMixedCell K}
    (huv : (mixedGridSquareResidualGraph K C).Adj u v) :
    f u + f v = 0 := by
  have hs := MuThreeMixedGridCode.residual_edgeSquareSum_eq_energySlack
    H K C code hf
  rw [heq, sub_self, mul_zero] at hs
  have houterNonneg : ∀ w ∈ (Finset.univ : Finset (muThreeMixedCell K)),
      0 ≤ ∑ z ∈ (mixedGridSquareResidualGraph K C).neighborFinset w,
        (f w + f z) ^ 2 := by
    intro w hw
    exact Finset.sum_nonneg fun z hz => sq_nonneg (f w + f z)
  have hu0 := (Finset.sum_eq_zero_iff_of_nonneg houterNonneg).mp hs
    u (Finset.mem_univ u)
  have hv0 := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => by positivity)).mp
    hu0 v (by simpa using huv)
  exact sq_eq_zero_iff.mp hv0

end Erdos85

#print axioms Erdos85.regularGraph_sum_neighbor_add_sq
#print axioms Erdos85.MuThreeMixedGridCode.residual_edgeSquareSum_eq_energySlack
#print axioms
  Erdos85.MuThreeMixedGridCode.residual_adj_add_eq_zero_of_energy_eq_fourteen
