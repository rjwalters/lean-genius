import Proofs.Erdos85MuThreeMixedGridResidualCommutation

/-!
# Quadratic energy bounds for the mixed-grid residual sector

An elementary edgewise square inequality bounds the quadratic form of a
regular graph.  Applying its lower half to the seven-regular residual graph
and substituting `A_D = 7I - A_C²` gives the sharp free-sector estimate
`‖A_C f‖² ≤ 14 ‖f‖²`, entirely over the integers.
-/

open SimpleGraph

namespace Erdos85

/-- Exchange the two ends of a directed-edge sum in an undirected graph. -/
theorem sum_neighborFinset_swap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (g : V → V → ℤ) :
    (∑ u, ∑ v ∈ G.neighborFinset u, g u v) =
      ∑ u, ∑ v ∈ G.neighborFinset u, g v u := by
  calc
    _ = ∑ u, ∑ v, if G.Adj u v then g u v else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext v
        simp [SimpleGraph.mem_neighborFinset]
      · intro v hv
        rfl
    _ = ∑ v, ∑ u, if G.Adj u v then g u v else 0 := Finset.sum_comm
    _ = ∑ u, ∑ v, if G.Adj u v then g v u else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      simp only [G.adj_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext v
        simp [SimpleGraph.mem_neighborFinset]
      · intro v hv
        rfl

/-- Lower quadratic-form bound for a finite `d`-regular simple graph, in a
division-free integer form. -/
theorem regularGraph_adjMatrix_quadratic_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hdeg : ∀ u, G.degree u = d)
    (f : V → ℤ) :
    -((d : ℤ) * (f ⬝ᵥ f)) ≤ f ⬝ᵥ (G.adjMatrix ℤ).mulVec f := by
  have hedge :
      -(∑ u, ∑ v ∈ G.neighborFinset u, (f u * f u + f v * f v)) ≤
        ∑ u, ∑ v ∈ G.neighborFinset u, 2 * (f u * f v) := by
    have hpoint (u v : V) :
        -(f u * f u + f v * f v) ≤ 2 * (f u * f v) := by
      nlinarith [sq_nonneg (f u + f v)]
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun u _hu =>
      Finset.sum_le_sum (s := G.neighborFinset u) (fun v _hv => hpoint u v))
    simpa only [Finset.sum_neg_distrib] using h
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
  have hleft :
      (∑ u, ∑ v ∈ G.neighborFinset u, (f u * f u + f v * f v)) =
        2 * ((d : ℤ) * (f ⬝ᵥ f)) := by
    simp_rw [Finset.sum_add_distrib]
    rw [hfirst, hsecond]
    ring
  have hright :
      (∑ u, ∑ v ∈ G.neighborFinset u, 2 * (f u * f v)) =
        2 * (f ⬝ᵥ (G.adjMatrix ℤ).mulVec f) := by
    simp only [dotProduct, SimpleGraph.adjMatrix_mulVec_apply]
    simp_rw [Finset.mul_sum]
  rw [hleft, hright] at hedge
  linarith

/-- **Free-sector exterior energy bound.**  The squared integer norm of
`A_C f` is at most fourteen times that of `f`. -/
theorem MuThreeMixedGridCode.adjMatrix_energy_le_fourteen_on_zeroSector
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {f : muThreeMixedCell K → ℤ}
    (hf : MixedGridZeroRowColumn K f) :
    ((C.adjMatrix ℤ).mulVec f) ⬝ᵥ ((C.adjMatrix ℤ).mulVec f) ≤
      14 * (f ⬝ᵥ f) := by
  let D := mixedGridSquareResidualGraph K C
  have hDlow := regularGraph_adjMatrix_quadratic_lower D 7
    (MuThreeMixedGridCode.squareResidualGraph_degree_eq_seven H K C code) f
  have haction := MuThreeMixedGridCode.residual_adjMatrix_mulVec_eq_on_zeroSector
    H K C code hf
  rw [haction] at hDlow
  have hsymm := mixedGridIndicator_dot_adjMatrix_mulVec C f
    ((C.adjMatrix ℤ).mulVec f)
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hsymm] at hDlow
  norm_num at hDlow
  linarith

end Erdos85

#print axioms Erdos85.regularGraph_adjMatrix_quadratic_lower
#print axioms
  Erdos85.MuThreeMixedGridCode.adjMatrix_energy_le_fourteen_on_zeroSector
