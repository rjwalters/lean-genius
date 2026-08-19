import Proofs.Erdos85SizeTwoEigenlineCyclicRoutingPermutation
import Proofs.Erdos85SizeTwoEigenlineCyclicDisplacementCollision

/-!
# Shifted agreement bounds for cyclic routing permutations

Node: `SIZE-TWO-EIGENLINE(q)`, beneath `GAP A-REG-NONBIP`.

Two translated sources use shifted row coordinates.  An agreement witness is
an admissible row whose shifted row is also admissible and whose two routing
permutations select the same absolute target column.  Such witnesses inject
into common neighbors of the two sources, so C4-freeness permits at most one.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

structure SizeTwoCyclicRoutingAgreement
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1)
    (routes : SizeTwoCyclicRoutingConstraints q a C)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a) where
  row : SizeTwoAdmissibleTargetRow q t.1
  shifted_admissible : t.1 ≠ row.1 - d ∧ t.1 ≠ (row.1 - d) - 1
  column_eq :
    x + (sizeTwoCyclicRowRouteTargetColumn
      q a C hcol_hit routes x t row).1 =
    (x + d) + (sizeTwoCyclicRowRouteTargetColumn
      q a C hcol_hit routes (x + d) t
        ⟨row.1 - d, shifted_admissible⟩).1

def SizeTwoCyclicRoutingAgreement.shiftedRow
    {q : ℕ} [NeZero q] {a : ZMod q}
    {C : SimpleGraph (sizeTwoCyclicExteriorCell q a)} [DecidableRel C.Adj]
    {hcol_hit} {routes : SizeTwoCyclicRoutingConstraints q a C}
    {x d : ZMod q} {t : sizeTwoAllowedDifference q a}
    (w : SizeTwoCyclicRoutingAgreement
      q a C hcol_hit routes x d t) :
    SizeTwoAdmissibleTargetRow q t.1 :=
  ⟨w.row.1 - d, w.shifted_admissible⟩

def SizeTwoCyclicRoutingAgreement.target
    {q : ℕ} [NeZero q] {a : ZMod q}
    {C : SimpleGraph (sizeTwoCyclicExteriorCell q a)} [DecidableRel C.Adj]
    {hcol_hit} {routes : SizeTwoCyclicRoutingConstraints q a C}
    {x d : ZMod q} {t : sizeTwoAllowedDifference q a}
    (w : SizeTwoCyclicRoutingAgreement
      q a C hcol_hit routes x d t) :
    sizeTwoCyclicExteriorCell q a :=
  sizeTwoCyclicCellAt q a (x + w.row.1)
    (sizeTwoCyclicRowRoute q a C routes x t w.row)

theorem SizeTwoCyclicRoutingAgreement.target_eq_shifted
    {q : ℕ} [NeZero q] {a : ZMod q}
    {C : SimpleGraph (sizeTwoCyclicExteriorCell q a)} [DecidableRel C.Adj]
    {hcol_hit} {routes : SizeTwoCyclicRoutingConstraints q a C}
    {x d : ZMod q} {t : sizeTwoAllowedDifference q a}
    (w : SizeTwoCyclicRoutingAgreement
      q a C hcol_hit routes x d t) :
    w.target = sizeTwoCyclicCellAt q a
      ((x + d) + w.shiftedRow.1)
      (sizeTwoCyclicRowRoute q a C routes (x + d) t w.shiftedRow) := by
  apply Subtype.ext
  apply Prod.ext
  · simp [SizeTwoCyclicRoutingAgreement.target,
      SizeTwoCyclicRoutingAgreement.shiftedRow,
      sizeTwoCyclicCellAt_fst, sub_eq_add_neg, add_assoc]
  · change x + w.row.1 +
        (sizeTwoCyclicRowRoute q a C routes x t w.row).1 =
      (x + d) + w.shiftedRow.1 +
        (sizeTwoCyclicRowRoute q a C routes (x + d) t w.shiftedRow).1
    simpa only [SizeTwoCyclicRoutingAgreement.shiftedRow,
      sizeTwoCyclicRowRouteTargetColumn, add_assoc] using w.column_eq

theorem SizeTwoCyclicRoutingAgreement.target_left_adj
    {q : ℕ} [NeZero q] {a : ZMod q}
    {C : SimpleGraph (sizeTwoCyclicExteriorCell q a)} [DecidableRel C.Adj]
    {hcol_hit} {routes : SizeTwoCyclicRoutingConstraints q a C}
    {x d : ZMod q} {t : sizeTwoAllowedDifference q a}
    (w : SizeTwoCyclicRoutingAgreement
      q a C hcol_hit routes x d t) :
    C.Adj (sizeTwoCyclicCellAt q a x t) w.target :=
  sizeTwoCyclicRowRoute_spec q a C routes x t w.row

theorem SizeTwoCyclicRoutingAgreement.target_right_adj
    {q : ℕ} [NeZero q] {a : ZMod q}
    {C : SimpleGraph (sizeTwoCyclicExteriorCell q a)} [DecidableRel C.Adj]
    {hcol_hit} {routes : SizeTwoCyclicRoutingConstraints q a C}
    {x d : ZMod q} {t : sizeTwoAllowedDifference q a}
    (w : SizeTwoCyclicRoutingAgreement
      q a C hcol_hit routes x d t) :
    C.Adj (sizeTwoCyclicCellAt q a (x + d) t) w.target := by
  rw [w.target_eq_shifted]
  exact sizeTwoCyclicRowRoute_spec q a C routes (x + d) t w.shiftedRow

theorem SizeTwoCyclicRoutingAgreement.target_injective
    {q : ℕ} [NeZero q] {a : ZMod q}
    {C : SimpleGraph (sizeTwoCyclicExteriorCell q a)} [DecidableRel C.Adj]
    {hcol_hit} {routes : SizeTwoCyclicRoutingConstraints q a C}
    {x d : ZMod q} {t : sizeTwoAllowedDifference q a} :
    Function.Injective (fun w : SizeTwoCyclicRoutingAgreement
      q a C hcol_hit routes x d t => w.target) := by
  intro u v huv
  have hbase := congrArg
    (fun z => (sizeTwoCyclicExteriorCellEquiv q a z).1) huv
  have hrow : u.row = v.row := by
    apply Subtype.ext
    simpa [SizeTwoCyclicRoutingAgreement.target,
      sizeTwoCyclicExteriorCellEquiv, sizeTwoCyclicCellAt] using
      add_left_cancel hbase
  cases u
  cases v
  cases hrow
  rfl

theorem SizeTwoCyclicRoutingAgreement.row_injective
    {q : ℕ} [NeZero q] {a : ZMod q}
    {C : SimpleGraph (sizeTwoCyclicExteriorCell q a)} [DecidableRel C.Adj]
    {hcol_hit} {routes : SizeTwoCyclicRoutingConstraints q a C}
    {x d : ZMod q} {t : sizeTwoAllowedDifference q a} :
    Function.Injective (fun w : SizeTwoCyclicRoutingAgreement
      q a C hcol_hit routes x d t => w.row) := by
  intro u v huv
  cases u
  cases v
  cases huv
  rfl

instance SizeTwoCyclicRoutingAgreement.instFinite
    {q : ℕ} [NeZero q] {a : ZMod q}
    {C : SimpleGraph (sizeTwoCyclicExteriorCell q a)} [DecidableRel C.Adj]
    {hcol_hit} {routes : SizeTwoCyclicRoutingConstraints q a C}
    {x d : ZMod q} {t : sizeTwoAllowedDifference q a} :
    Finite (SizeTwoCyclicRoutingAgreement
      q a C hcol_hit routes x d t) :=
  Finite.of_injective (fun w => w.row.1) (by
    intro u v h
    apply SizeTwoCyclicRoutingAgreement.row_injective
    exact Subtype.ext h)

noncomputable instance SizeTwoCyclicRoutingAgreement.instFintype
    {q : ℕ} [NeZero q] {a : ZMod q}
    {C : SimpleGraph (sizeTwoCyclicExteriorCell q a)} [DecidableRel C.Adj]
    {hcol_hit} {routes : SizeTwoCyclicRoutingConstraints q a C}
    {x d : ZMod q} {t : sizeTwoAllowedDifference q a} :
    Fintype (SizeTwoCyclicRoutingAgreement
      q a C hcol_hit routes x d t) := Fintype.ofFinite _

def SizeTwoCyclicRoutingAgreement.toCommonNeighbor
    {q : ℕ} [NeZero q] {a : ZMod q}
    {C : SimpleGraph (sizeTwoCyclicExteriorCell q a)} [DecidableRel C.Adj]
    {hcol_hit} {routes : SizeTwoCyclicRoutingConstraints q a C}
    {x d : ZMod q} {t : sizeTwoAllowedDifference q a}
    (w : SizeTwoCyclicRoutingAgreement
      q a C hcol_hit routes x d t) :
    {v : sizeTwoCyclicExteriorCell q a //
      C.Adj (sizeTwoCyclicCellAt q a x t) v ∧
      C.Adj (sizeTwoCyclicCellAt q a (x + d) t) v} :=
  ⟨w.target, w.target_left_adj, w.target_right_adj⟩

theorem sizeTwoCyclicRoutingAgreement_card_le_one
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hfree : ¬ containsC4 (sizeTwoCyclicExteriorCell q a) C)
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1)
    (routes : SizeTwoCyclicRoutingConstraints q a C)
    (x d : ZMod q) (hd : d ≠ 0)
    (t : sizeTwoAllowedDifference q a) :
    Fintype.card (SizeTwoCyclicRoutingAgreement
      q a C hcol_hit routes x d t) ≤ 1 := by
  classical
  letI : Fintype {v : sizeTwoCyclicExteriorCell q a //
      C.Adj (sizeTwoCyclicCellAt q a x t) v ∧
      C.Adj (sizeTwoCyclicCellAt q a (x + d) t) v} := Fintype.ofFinite _
  calc
    Fintype.card (SizeTwoCyclicRoutingAgreement
        q a C hcol_hit routes x d t) ≤
        Fintype.card {v : sizeTwoCyclicExteriorCell q a //
          C.Adj (sizeTwoCyclicCellAt q a x t) v ∧
          C.Adj (sizeTwoCyclicCellAt q a (x + d) t) v} :=
      Fintype.card_le_of_injective
        SizeTwoCyclicRoutingAgreement.toCommonNeighbor
        (fun _ _ h => SizeTwoCyclicRoutingAgreement.target_injective
          (congrArg Subtype.val h))
    _ = ((Finset.univ : Finset (sizeTwoCyclicExteriorCell q a)).filter fun v =>
        C.Adj (sizeTwoCyclicCellAt q a x t) v ∧
        C.Adj (sizeTwoCyclicCellAt q a (x + d) t) v).card := by
      rw [Fintype.card_subtype]
    _ ≤ 1 := sizeTwoTranslated_commonNeighbor_card_le_one
      q a C hfree t x d hd

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicRoutingAgreement_card_le_one
