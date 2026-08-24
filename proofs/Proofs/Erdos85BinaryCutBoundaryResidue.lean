import Proofs.Erdos85ActiveBrokenRelayEulerization

/-!
# Binary cut boundary with its exact degree residue

This file formalizes `(73rnz_cjid)--(73rnz_cjif)`.  Without an even-degree
hypothesis, adjacency incidence differs from the boundary of the support cut
by precisely the potential times the ambient degree parity.  Applied to the
`O`/`D` decomposition, this converts every atomized `O` dart into its actual
two-ended edge and identifies the remaining vertex residue.
-/

open SimpleGraph

namespace Erdos85

private theorem zmod2_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · left; rfl
  · right; rfl

/-- Exact cut identity at arbitrary degree:
`Gx = ∂δ_G(supp x) + x · deg_G` over `F₂`. -/
theorem adjMatrix_mulVec_eq_binaryCut_degree_add_degreeResidue
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ZMod 2) (v : V) :
    (G.adjMatrix (ZMod 2)).mulVec x v =
      ((binaryVertexCutGraph G (f2PotentialSupport x)).degree v : ZMod 2) +
        x v * (G.degree v : ZMod 2) := by
  rw [← f2Potential_neighborSupport_card_cast G x v]
  have hpartition := Finset.card_inter_add_card_sdiff
    (G.neighborFinset v) (f2PotentialSupport x)
  have hdegree : (G.neighborFinset v).card = G.degree v :=
    G.card_neighborFinset_eq_degree v
  have hbinary := zmod2_eq_zero_or_one (x v)
  rcases hbinary with hx | hx
  · have hv : v ∉ f2PotentialSupport x := by simp [f2PotentialSupport, hx]
    rw [binaryVertexCutGraph_degree_eq, if_neg hv, hx, zero_mul, add_zero]
  · have hv : v ∈ f2PotentialSupport x := by simp [f2PotentialSupport, hx]
    rw [binaryVertexCutGraph_degree_eq, if_pos hv, hx, one_mul]
    rw [hdegree] at hpartition
    have hp :
        ((G.neighborFinset v ∩ f2PotentialSupport x).card : ZMod 2) +
          ((G.neighborFinset v \ f2PotentialSupport x).card : ZMod 2) =
            (G.degree v : ZMod 2) := by
      rw [← Nat.cast_add]
      exact congrArg (fun n : ℕ => (n : ZMod 2)) hpartition
    let a : ZMod 2 := (G.neighborFinset v ∩ f2PotentialSupport x).card
    let b : ZMod 2 := (G.neighborFinset v \ f2PotentialSupport x).card
    let d : ZMod 2 := G.degree v
    change a = b + d
    change a + b = d at hp
    have hbb : b + b = 0 := by
      rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
    calc
      a = a + 0 := by simp
      _ = a + (b + b) := by rw [hbb]
      _ = b + (a + b) := by ring
      _ = b + d := by rw [hp]

/-- `(73rnz_cjie)`: if `O` has the same degree syndrome as the `D`-cut and
`D` has odd degree, the `O`-cut residue is exactly `x(Dt+t)`. -/
theorem oCut_boundary_residue_eq_x_mul_Dt_add_t
    {V : Type*} [Fintype V] [DecidableEq V]
    (O D : SimpleGraph V) [DecidableRel O.Adj] [DecidableRel D.Adj]
    (x t : V → ZMod 2)
    (hdeg : ∀ v, (O.degree v : ZMod 2) =
      ((binaryVertexCutGraph D (f2PotentialSupport t)).degree v : ZMod 2))
    (hDodd : ∀ v, (D.degree v : ZMod 2) = 1) (v : V) :
    (O.adjMatrix (ZMod 2)).mulVec x v =
      ((binaryVertexCutGraph O (f2PotentialSupport x)).degree v : ZMod 2) +
        x v * ((D.adjMatrix (ZMod 2)).mulVec t v + t v) := by
  rw [adjMatrix_mulVec_eq_binaryCut_degree_add_degreeResidue O x v, hdeg]
  have hD := adjMatrix_mulVec_eq_binaryCut_degree_add_degreeResidue D t v
  rw [hDodd, mul_one] at hD
  rw [hD]
  have htwo : (2 : ZMod 2) = 0 := by decide
  ring_nf
  simp [htwo]

/-- Symmetry moves an adjacency action across the binary inner product. -/
theorem adjMatrix_mulVec_pairing_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x t : V → ZMod 2) :
    (∑ v, x v * (G.adjMatrix (ZMod 2)).mulVec t v) =
      ∑ v, (G.adjMatrix (ZMod 2)).mulVec x v * t v := by
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
  by_cases hij : G.Adj i j
  · simp [hij, G.adj_comm]
  · simp [hij, G.adj_comm]

/-- `(73rnz_cjif)`: under `Dx+x=line`, the total remaining cut residue is
exactly the combined line-owner parity. -/
theorem binaryCut_residue_totalMass_eq_line_pairing
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (x t line : V → ZMod 2)
    (hDx : (D.adjMatrix (ZMod 2)).mulVec x + x = line) :
    (∑ v, x v * ((D.adjMatrix (ZMod 2)).mulVec t v + t v)) =
      ∑ v, line v * t v := by
  rw [show (∑ v, x v * ((D.adjMatrix (ZMod 2)).mulVec t v + t v)) =
      (∑ v, x v * (D.adjMatrix (ZMod 2)).mulVec t v) +
        ∑ v, x v * t v by
          simp_rw [mul_add, Finset.sum_add_distrib]]
  rw [adjMatrix_mulVec_pairing_comm D x t]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have hv := congrFun hDx v
  simp only [Pi.add_apply] at hv
  rw [← hv]
  ring

end Erdos85

#print axioms Erdos85.adjMatrix_mulVec_eq_binaryCut_degree_add_degreeResidue
#print axioms Erdos85.oCut_boundary_residue_eq_x_mul_Dt_add_t
#print axioms Erdos85.adjMatrix_mulVec_pairing_comm
#print axioms Erdos85.binaryCut_residue_totalMass_eq_line_pairing
