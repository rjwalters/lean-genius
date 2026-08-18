import Proofs.Erdos85MuThreeMixedGridSquareMatrix
import Proofs.Erdos85AlternatingFourthMoment

/-!
# Commuting operators in the mixed `mu = 3` grid

The exterior adjacency operator commutes with the occupied rook graph.  The
row/column hit laws give the entrywise equality: both mixed products count
the same two hit indicators, with the same correction when the endpoints
are adjacent.  The square partition then forces commutation with the
residual defect relation as well.
-/

open SimpleGraph

namespace Erdos85

/-- The mixed two-walk counts through the rook graph are symmetric. -/
theorem MuThreeMixedGridCode.mixed_rowColumn_card_comm
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u v : muThreeMixedCell K) :
    (C.neighborFinset u ∩
        (mixedGridRowColumnGraph K).neighborFinset v).card =
      ((mixedGridRowColumnGraph K).neighborFinset u ∩
        C.neighborFinset v).card := by
  classical
  let R := mixedGridRowColumnGraph K
  have hformula : ∀ a b : muThreeMixedCell K,
      (C.neighborFinset a ∩ R.neighborFinset b).card +
          (if C.Adj a b then 2 else 0) =
        ((C.neighborFinset a).filter fun w => w.1.1 = b.1.1).card +
          ((C.neighborFinset a).filter fun w => w.1.2 = b.1.2).card := by
    intro a b
    let A := (C.neighborFinset a).filter fun w => w.1.1 = b.1.1
    let B := (C.neighborFinset a).filter fun w => w.1.2 = b.1.2
    let S := C.neighborFinset a ∩ R.neighborFinset b
    have hS : S = (A ∪ B).erase b := by
      ext w
      simp only [S, A, B, R, Finset.mem_inter, Finset.mem_erase,
        Finset.mem_union, Finset.mem_filter, mem_neighborFinset,
        mixedGridRowColumnGraph]
      constructor
      · rintro ⟨haw, hwb, hrow | hcol⟩
        · exact ⟨hwb, Or.inl ⟨haw, hrow⟩⟩
        · exact ⟨hwb, Or.inr ⟨haw, hcol⟩⟩
      · rintro ⟨hwb, ⟨haw, hrow⟩ | ⟨haw, hcol⟩⟩
        · exact ⟨haw, hwb, Or.inl hrow⟩
        · exact ⟨haw, hwb, Or.inr hcol⟩
    have hinter : (A ∩ B).card = if C.Adj a b then 1 else 0 := by
      by_cases hab : C.Adj a b
      · rw [if_pos hab]
        have heq : A ∩ B = {b} := by
          ext w
          simp only [A, B, Finset.mem_inter, Finset.mem_filter,
            Finset.mem_singleton]
          constructor
          · rintro ⟨⟨_haw, hrow⟩, _haw', hcol⟩
            apply Subtype.ext
            exact Prod.ext hrow hcol
          · rintro rfl
            exact ⟨⟨(C.mem_neighborFinset a b).mpr hab, rfl⟩,
              (C.mem_neighborFinset a b).mpr hab, rfl⟩
        rw [heq, Finset.card_singleton]
      · rw [if_neg hab, Finset.card_eq_zero]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        have hwA := (Finset.mem_inter.mp hw).1
        have hwB := (Finset.mem_inter.mp hw).2
        apply hab
        have hwb : w = b := by
          apply Subtype.ext
          exact Prod.ext (Finset.mem_filter.mp hwA).2
            (Finset.mem_filter.mp hwB).2
        simpa [hwb] using (Finset.mem_filter.mp hwA).1
    have hbUnion : b ∈ A ∪ B ↔ C.Adj a b := by
      simp [A, B, C.mem_neighborFinset]
    have hunion := Finset.card_union_add_card_inter A B
    rw [hinter] at hunion
    rw [hS]
    by_cases hab : C.Adj a b
    · have hb : b ∈ A ∪ B := hbUnion.mpr hab
      rw [Finset.card_erase_of_mem hb, if_pos hab] at hunion ⊢
      omega
    · have hb : b ∉ A ∪ B := fun h => hab (hbUnion.mp h)
      rw [Finset.erase_eq_of_notMem hb, if_neg hab] at hunion ⊢
      omega
  have huv := hformula u v
  have hvu := hformula v u
  simp only [code.row_hit, code.column_hit] at huv hvu
  have hadj : C.Adj u v ↔ C.Adj v u := C.adj_comm
  split at huv <;> split at huv <;> split at hvu <;> split at hvu <;>
    simp_all [C.adj_comm] <;> omega

/-- The exterior adjacency matrix commutes with the occupied rook graph. -/
theorem MuThreeMixedGridCode.adjMatrix_commutes_rowColumn
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) :
    C.adjMatrix ℤ * (mixedGridRowColumnGraph K).adjMatrix ℤ =
      (mixedGridRowColumnGraph K).adjMatrix ℤ * C.adjMatrix ℤ := by
  ext u v
  rw [adjMatrix_mul_subgraph_apply_eq_card_mixed,
    adjMatrix_mul_subgraph_apply_eq_card_mixed]
  exact_mod_cast code.mixed_rowColumn_card_comm H K C u v

/-- The exterior adjacency matrix also commutes with the residual square
relation.  This follows algebraically from the exact square partition once
commutation with the rook graph is known. -/
theorem MuThreeMixedGridCode.adjMatrix_commutes_squareResidual
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) :
    C.adjMatrix ℤ * (mixedGridSquareResidualGraph K C).adjMatrix ℤ =
      (mixedGridSquareResidualGraph K C).adjMatrix ℤ * C.adjMatrix ℤ := by
  let A := C.adjMatrix ℤ
  let D := (mixedGridSquareResidualGraph K C).adjMatrix ℤ
  let R := (mixedGridRowColumnGraph K).adjMatrix ℤ
  let I := (1 : Matrix (muThreeMixedCell K) (muThreeMixedCell K) ℤ)
  let J := FriendshipTheoremOQ01.onesMatrix (muThreeMixedCell K)
  have hsq : A * A + D + R = (5 : ℤ) • I + J := by
    exact code.adjMatrix_sq_add_residual_add_rowColumn H K C
  have hAR : A * R = R * A := by
    exact code.adjMatrix_commutes_rowColumn H K C
  have hAJ : A * J = J * A := by
    exact FriendshipTheoremOQ01.onesMatrix_adjMatrix_comm C 6
      (fun u => code.degree_eq_six H K C u)
  have hD : D = (5 : ℤ) • I + J - A * A - R := by
    noncomm_ring [hsq]
  change A * D = D * A
  rw [hD]
  noncomm_ring [hAR, hAJ]

/-- The rook and residual relations commute too; consequently all three
operators in the square partition are pairwise commuting symmetric integer
matrices. -/
theorem MuThreeMixedGridCode.rowColumn_commutes_squareResidual
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) :
    (mixedGridRowColumnGraph K).adjMatrix ℤ *
        (mixedGridSquareResidualGraph K C).adjMatrix ℤ =
      (mixedGridSquareResidualGraph K C).adjMatrix ℤ *
        (mixedGridRowColumnGraph K).adjMatrix ℤ := by
  let A := C.adjMatrix ℤ
  let D := (mixedGridSquareResidualGraph K C).adjMatrix ℤ
  let R := (mixedGridRowColumnGraph K).adjMatrix ℤ
  let I := (1 : Matrix (muThreeMixedCell K) (muThreeMixedCell K) ℤ)
  let J := FriendshipTheoremOQ01.onesMatrix (muThreeMixedCell K)
  have hsq : A * A + D + R = (5 : ℤ) • I + J := by
    exact code.adjMatrix_sq_add_residual_add_rowColumn H K C
  have hRA : R * A = A * R := by
    exact (code.adjMatrix_commutes_rowColumn H K C).symm
  have hRJ : R * J = J * R := by
    exact FriendshipTheoremOQ01.onesMatrix_adjMatrix_comm
      (mixedGridRowColumnGraph K) 10
      (fun u => code.rowColumnGraph_degree_eq_ten H K C u)
  have hD : D = (5 : ℤ) • I + J - A * A - R := by
    noncomm_ring [hsq]
  change R * D = D * R
  rw [hD]
  noncomm_ring [hRA, hRJ]

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.mixed_rowColumn_card_comm
#print axioms Erdos85.MuThreeMixedGridCode.adjMatrix_commutes_rowColumn
#print axioms Erdos85.MuThreeMixedGridCode.adjMatrix_commutes_squareResidual
#print axioms Erdos85.MuThreeMixedGridCode.rowColumn_commutes_squareResidual
