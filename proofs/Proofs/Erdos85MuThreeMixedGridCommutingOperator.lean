import Proofs.Erdos85MuThreeMixedGridRouteEquiv

/-!
# The commuting residual-plus-rook operator

The square identity rewrites the combined residual and rook adjacency
operator as `5I + J - A_C²`.  Since the exterior is regular, `A_C` commutes
with `J`, hence with this combined operator.
-/

open SimpleGraph

namespace Erdos85

/-- The residual-plus-rook graph is exactly the complement of the exterior
common-neighbour conflict graph. -/
theorem MuThreeMixedGridCode.residual_sup_rowColumn_eq_conflict_compl
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) :
    mixedGridSquareResidualGraph K C ⊔ mixedGridRowColumnGraph K =
      (commonNeighborConflict C)ᶜ := by
  ext u v
  simp only [sup_adj, SimpleGraph.compl_adj, commonNeighborConflict_adj_iff]
  constructor
  · intro h
    rcases h with hd | hr
    · refine ⟨hd.1, ?_⟩
      intro hconflict
      have hzero := hd.2.2
      have hpos := Finset.card_pos.mpr hconflict.2
      omega
    · refine ⟨hr.1, ?_⟩
      intro hconflict
      have hzero :=
        MuThreeMixedGridCode.rowColumn_common_neighbor_card_eq_zero
          H K C code hr
      have hpos := Finset.card_pos.mpr hconflict.2
      omega
  · rintro ⟨hne, hnotconflict⟩
    have hnonempty : ¬ (C.neighborFinset u ∩ C.neighborFinset v).Nonempty := by
      intro h
      exact hnotconflict ⟨hne, h⟩
    have hzero : (C.neighborFinset u ∩ C.neighborFinset v).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hnonempty)
    by_cases hr : (mixedGridRowColumnGraph K).Adj u v
    · exact Or.inr hr
    · exact Or.inl ⟨hne, hr, hzero⟩

/-- The combined residual-plus-rook graph is 17-regular. -/
theorem MuThreeMixedGridCode.residual_sup_rowColumn_degree_eq_seventeen
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : muThreeMixedCell K) :
    (mixedGridSquareResidualGraph K C ⊔ mixedGridRowColumnGraph K).degree u = 17 := by
  have hgraph :=
    MuThreeMixedGridCode.residual_sup_rowColumn_eq_conflict_compl H K C code
  rw [← (mixedGridSquareResidualGraph K C ⊔
    mixedGridRowColumnGraph K).card_neighborFinset_eq_degree]
  have hfinset :
      (mixedGridSquareResidualGraph K C ⊔
          mixedGridRowColumnGraph K).neighborFinset u =
        (commonNeighborConflict C)ᶜ.neighborFinset u := by
    ext v
    simp only [mem_neighborFinset]
    exact iff_of_eq (congrArg
      (fun G : SimpleGraph (muThreeMixedCell K) => G.Adj u v) hgraph)
  rw [hfinset, (commonNeighborConflict C)ᶜ.card_neighborFinset_eq_degree,
    SimpleGraph.degree_compl,
    MuThreeMixedGridCode.card_mixedCell_eq_fortyEight H K C code,
    degree_commonNeighborConflict_of_regular_c4Free C code.c4Free
      (fun v => MuThreeMixedGridCode.degree_eq_six H K C code v) u]

/-- Polynomial form of the mixed-grid square identity. -/
theorem MuThreeMixedGridCode.residual_add_rowColumn_adjMatrix_eq
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) :
    (mixedGridSquareResidualGraph K C).adjMatrix ℤ +
        (mixedGridRowColumnGraph K).adjMatrix ℤ =
      (5 : ℤ) • (1 : Matrix (muThreeMixedCell K) (muThreeMixedCell K) ℤ) +
        FriendshipTheoremOQ01.onesMatrix (muThreeMixedCell K) -
          C.adjMatrix ℤ * C.adjMatrix ℤ := by
  have h := MuThreeMixedGridCode.adjMatrix_sq_add_residual_add_rowColumn
    H K C code
  rw [← h]
  abel

/-- The exterior adjacency matrix commutes with the sum of the residual and
rook adjacency matrices. -/
theorem MuThreeMixedGridCode.adjMatrix_comm_residual_add_rowColumn
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) :
    C.adjMatrix ℤ *
        ((mixedGridSquareResidualGraph K C).adjMatrix ℤ +
          (mixedGridRowColumnGraph K).adjMatrix ℤ) =
      ((mixedGridSquareResidualGraph K C).adjMatrix ℤ +
          (mixedGridRowColumnGraph K).adjMatrix ℤ) * C.adjMatrix ℤ := by
  rw [MuThreeMixedGridCode.residual_add_rowColumn_adjMatrix_eq H K C code]
  have hreg : ∀ u, C.degree u = 6 :=
    fun u => MuThreeMixedGridCode.degree_eq_six H K C code u
  have hAJ := FriendshipTheoremOQ01.onesMatrix_adjMatrix_comm C 6 hreg
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_assoc]
  rw [hAJ]

end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.residual_sup_rowColumn_eq_conflict_compl
#print axioms
  Erdos85.MuThreeMixedGridCode.residual_sup_rowColumn_degree_eq_seventeen
#print axioms
  Erdos85.MuThreeMixedGridCode.residual_add_rowColumn_adjMatrix_eq
#print axioms
  Erdos85.MuThreeMixedGridCode.adjMatrix_comm_residual_add_rowColumn
