import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationInvolution

/-!
# Cross-difference agreement bounds

Node: `SIZE-TWO-EIGENLINE(q)`, beneath `GAP A-REG-NONBIP`.

C4-freeness bounds common targets for every pair of distinct exterior source
cells, not merely translated sources in one difference orbit.  This file
upgrades the graph-free code accordingly.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

structure SizeTwoCyclicCrossRoutingAgreement
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hcol_hit : ∀ (v : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset v).filter fun w => w.1.2 = z).card =
        if v.1.1 = z ∨ v.1.1 = z + 1 then 0 else 1)
    (routes : SizeTwoCyclicRoutingConstraints q a C)
    (x d : ZMod q)
    (t u : sizeTwoAllowedDifference q a) where
  row : SizeTwoAdmissibleTargetRow q t.1
  shifted_admissible : u.1 ≠ row.1 - d ∧ u.1 ≠ (row.1 - d) - 1
  column_eq :
    x + (sizeTwoCyclicRowRouteTargetColumn
      q a C hcol_hit routes x t row).1 =
    (x + d) + (sizeTwoCyclicRowRouteTargetColumn
      q a C hcol_hit routes (x + d) u
        ⟨row.1 - d, shifted_admissible⟩).1

def SizeTwoCyclicCrossRoutingAgreement.shiftedRow
    {q : ℕ} [NeZero q] {a : ZMod q}
    {C : SimpleGraph (sizeTwoCyclicExteriorCell q a)} [DecidableRel C.Adj]
    {hcol_hit} {routes : SizeTwoCyclicRoutingConstraints q a C}
    {x d : ZMod q} {t u : sizeTwoAllowedDifference q a}
    (w : SizeTwoCyclicCrossRoutingAgreement
      q a C hcol_hit routes x d t u) :
    SizeTwoAdmissibleTargetRow q u.1 :=
  ⟨w.row.1 - d, w.shifted_admissible⟩

def SizeTwoCyclicCrossRoutingAgreement.target
    {q : ℕ} [NeZero q] {a : ZMod q}
    {C : SimpleGraph (sizeTwoCyclicExteriorCell q a)} [DecidableRel C.Adj]
    {hcol_hit} {routes : SizeTwoCyclicRoutingConstraints q a C}
    {x d : ZMod q} {t u : sizeTwoAllowedDifference q a}
    (w : SizeTwoCyclicCrossRoutingAgreement
      q a C hcol_hit routes x d t u) :
    sizeTwoCyclicExteriorCell q a :=
  sizeTwoCyclicCellAt q a (x + w.row.1)
    (sizeTwoCyclicRowRoute q a C routes x t w.row)

theorem SizeTwoCyclicCrossRoutingAgreement.target_eq_shifted
    {q : ℕ} [NeZero q] {a : ZMod q}
    {C : SimpleGraph (sizeTwoCyclicExteriorCell q a)} [DecidableRel C.Adj]
    {hcol_hit} {routes : SizeTwoCyclicRoutingConstraints q a C}
    {x d : ZMod q} {t u : sizeTwoAllowedDifference q a}
    (w : SizeTwoCyclicCrossRoutingAgreement
      q a C hcol_hit routes x d t u) :
    w.target = sizeTwoCyclicCellAt q a
      ((x + d) + w.shiftedRow.1)
      (sizeTwoCyclicRowRoute q a C routes (x + d) u w.shiftedRow) := by
  apply Subtype.ext
  apply Prod.ext
  · simp [SizeTwoCyclicCrossRoutingAgreement.target,
      SizeTwoCyclicCrossRoutingAgreement.shiftedRow,
      sizeTwoCyclicCellAt_fst, sub_eq_add_neg, add_assoc]
  · change x + w.row.1 +
        (sizeTwoCyclicRowRoute q a C routes x t w.row).1 =
      (x + d) + w.shiftedRow.1 +
        (sizeTwoCyclicRowRoute q a C routes (x + d) u w.shiftedRow).1
    simpa only [SizeTwoCyclicCrossRoutingAgreement.shiftedRow,
      sizeTwoCyclicRowRouteTargetColumn, add_assoc] using w.column_eq

theorem SizeTwoCyclicCrossRoutingAgreement.target_injective
    {q : ℕ} [NeZero q] {a : ZMod q}
    {C : SimpleGraph (sizeTwoCyclicExteriorCell q a)} [DecidableRel C.Adj]
    {hcol_hit} {routes : SizeTwoCyclicRoutingConstraints q a C}
    {x d : ZMod q} {t u : sizeTwoAllowedDifference q a} :
    Function.Injective (fun w : SizeTwoCyclicCrossRoutingAgreement
      q a C hcol_hit routes x d t u => w.target) := by
  intro p w hpw
  have hbase := congrArg
    (fun z => (sizeTwoCyclicExteriorCellEquiv q a z).1) hpw
  have hrow : p.row = w.row := by
    apply Subtype.ext
    simpa [SizeTwoCyclicCrossRoutingAgreement.target,
      sizeTwoCyclicExteriorCellEquiv, sizeTwoCyclicCellAt] using
      add_left_cancel hbase
  cases p
  cases w
  cases hrow
  rfl

theorem SizeTwoCyclicCrossRoutingAgreement.row_injective
    {q : ℕ} [NeZero q] {a : ZMod q}
    {C : SimpleGraph (sizeTwoCyclicExteriorCell q a)} [DecidableRel C.Adj]
    {hcol_hit} {routes : SizeTwoCyclicRoutingConstraints q a C}
    {x d : ZMod q} {t u : sizeTwoAllowedDifference q a} :
    Function.Injective (fun w : SizeTwoCyclicCrossRoutingAgreement
      q a C hcol_hit routes x d t u => w.row) := by
  intro p w h
  cases p
  cases w
  cases h
  rfl

instance SizeTwoCyclicCrossRoutingAgreement.instFinite
    {q : ℕ} [NeZero q] {a : ZMod q}
    {C : SimpleGraph (sizeTwoCyclicExteriorCell q a)} [DecidableRel C.Adj]
    {hcol_hit} {routes : SizeTwoCyclicRoutingConstraints q a C}
    {x d : ZMod q} {t u : sizeTwoAllowedDifference q a} :
    Finite (SizeTwoCyclicCrossRoutingAgreement
      q a C hcol_hit routes x d t u) :=
  Finite.of_injective (fun w => w.row.1) (by
    intro p w h
    apply SizeTwoCyclicCrossRoutingAgreement.row_injective
    exact Subtype.ext h)

noncomputable instance SizeTwoCyclicCrossRoutingAgreement.instFintype
    {q : ℕ} [NeZero q] {a : ZMod q}
    {C : SimpleGraph (sizeTwoCyclicExteriorCell q a)} [DecidableRel C.Adj]
    {hcol_hit} {routes : SizeTwoCyclicRoutingConstraints q a C}
    {x d : ZMod q} {t u : sizeTwoAllowedDifference q a} :
    Fintype (SizeTwoCyclicCrossRoutingAgreement
      q a C hcol_hit routes x d t u) := Fintype.ofFinite _

theorem sizeTwoCyclicCrossRoutingAgreement_card_le_one
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hfree : ¬ containsC4 (sizeTwoCyclicExteriorCell q a) C)
    (hcol_hit : ∀ (v : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset v).filter fun w => w.1.2 = z).card =
        if v.1.1 = z ∨ v.1.1 = z + 1 then 0 else 1)
    (routes : SizeTwoCyclicRoutingConstraints q a C)
    (x d : ZMod q) (t u : sizeTwoAllowedDifference q a)
    (hdiff : d ≠ 0 ∨ t ≠ u) :
    Fintype.card (SizeTwoCyclicCrossRoutingAgreement
      q a C hcol_hit routes x d t u) ≤ 1 := by
  classical
  rw [Fintype.card_le_one_iff]
  intro p w
  by_contra hpw
  apply hfree
  have hsource : sizeTwoCyclicCellAt q a x t ≠
      sizeTwoCyclicCellAt q a (x + d) u := by
    intro heq
    have hcoords := congrArg (sizeTwoCyclicExteriorCellEquiv q a) heq
    apply hdiff.elim
    · intro hd
      apply hd
      have hbase : x = x + d := by
        simpa [sizeTwoCyclicCellAt] using congrArg Prod.fst hcoords
      calc
        d = -x + (x + d) := by abel
        _ = -x + x := by rw [← hbase]
        _ = 0 := by abel
    · intro htu
      apply htu
      simpa [sizeTwoCyclicCellAt] using congrArg Prod.snd hcoords
  have htarget : p.target ≠ w.target := fun heq =>
    hpw (SizeTwoCyclicCrossRoutingAgreement.target_injective heq)
  have hpRight : C.Adj (sizeTwoCyclicCellAt q a (x + d) u) p.target := by
    rw [p.target_eq_shifted]
    exact sizeTwoCyclicRowRoute_spec q a C routes
      (x + d) u p.shiftedRow
  have hwRight : C.Adj (sizeTwoCyclicCellAt q a (x + d) u) w.target := by
    rw [w.target_eq_shifted]
    exact sizeTwoCyclicRowRoute_spec q a C routes
      (x + d) u w.shiftedRow
  exact containsC4_of_two_common hsource htarget
    (C.adj_symm (sizeTwoCyclicRowRoute_spec q a C routes x t p.row))
    (C.adj_symm hpRight)
    (C.adj_symm (sizeTwoCyclicRowRoute_spec q a C routes x t w.row))
    (C.adj_symm hwRight)

structure SizeTwoCrossShiftedPermutationAgreement
    (q : ℕ) [NeZero q] (a : ZMod q)
    (P : SizeTwoCyclicPermutationFamily q a)
    (x d : ZMod q) (t u : sizeTwoAllowedDifference q a) where
  row : SizeTwoAdmissibleTargetRow q t.1
  shifted_admissible : u.1 ≠ row.1 - d ∧ u.1 ≠ (row.1 - d) - 1
  column_eq :
    x + (P x t row).1 =
      (x + d) + (P (x + d) u ⟨row.1 - d, shifted_admissible⟩).1

theorem SizeTwoCrossShiftedPermutationAgreement.row_injective
    {q : ℕ} [NeZero q] {a : ZMod q}
    {P : SizeTwoCyclicPermutationFamily q a}
    {x d : ZMod q} {t u : sizeTwoAllowedDifference q a} :
    Function.Injective (fun w : SizeTwoCrossShiftedPermutationAgreement
      q a P x d t u => w.row) := by
  intro p w h
  cases p
  cases w
  cases h
  rfl

instance SizeTwoCrossShiftedPermutationAgreement.instFinite
    {q : ℕ} [NeZero q] {a : ZMod q}
    {P : SizeTwoCyclicPermutationFamily q a}
    {x d : ZMod q} {t u : sizeTwoAllowedDifference q a} :
    Finite (SizeTwoCrossShiftedPermutationAgreement q a P x d t u) :=
  Finite.of_injective (fun w => w.row.1) (by
    intro p w h
    apply SizeTwoCrossShiftedPermutationAgreement.row_injective
    exact Subtype.ext h)

noncomputable instance SizeTwoCrossShiftedPermutationAgreement.instFintype
    {q : ℕ} [NeZero q] {a : ZMod q}
    {P : SizeTwoCyclicPermutationFamily q a}
    {x d : ZMod q} {t u : sizeTwoAllowedDifference q a} :
    Fintype (SizeTwoCrossShiftedPermutationAgreement q a P x d t u) :=
  Fintype.ofFinite _

structure SizeTwoCyclicFullPermutationCode
    (q : ℕ) [NeZero q] (a : ZMod q) where
  toReciprocalCode : SizeTwoCyclicReciprocalPermutationCode q a
  cross_agreement_le_one : ∀ (x d : ZMod q)
    (t u : sizeTwoAllowedDifference q a),
    d ≠ 0 ∨ t ≠ u →
      Fintype.card (SizeTwoCrossShiftedPermutationAgreement q a
        toReciprocalCode.toPermutationCode.perm x d t u) ≤ 1

def sizeTwoCrossRoutingAgreementEquiv
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hrow_hit : ∀ (v : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset v).filter fun w => w.1.1 = y).card =
        if v.1.2 = y ∨ v.1.2 = y - 1 then 0 else 1)
    (hcol_hit : ∀ (v : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset v).filter fun w => w.1.2 = z).card =
        if v.1.1 = z ∨ v.1.1 = z + 1 then 0 else 1)
    (routes : SizeTwoCyclicRoutingConstraints q a C)
    (x d : ZMod q) (t u : sizeTwoAllowedDifference q a) :
    SizeTwoCrossShiftedPermutationAgreement q a
        (fun x t => sizeTwoCyclicRoutingEquiv
          q a C hrow_hit hcol_hit routes x t) x d t u ≃
      SizeTwoCyclicCrossRoutingAgreement
        q a C hcol_hit routes x d t u where
  toFun w := ⟨w.row, w.shifted_admissible, by
    simpa [sizeTwoCyclicRoutingEquiv] using w.column_eq⟩
  invFun w := ⟨w.row, w.shifted_admissible, by
    simpa [sizeTwoCyclicRoutingEquiv] using w.column_eq⟩
  left_inv w := by cases w; rfl
  right_inv w := by cases w; rfl

def sizeTwoCyclicFullPermutationCode_of_grid
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hfree : ¬ containsC4 (sizeTwoCyclicExteriorCell q a) C)
    (hrow_hit : ∀ (v : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset v).filter fun w => w.1.1 = y).card =
        if v.1.2 = y ∨ v.1.2 = y - 1 then 0 else 1)
    (hcol_hit : ∀ (v : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset v).filter fun w => w.1.2 = z).card =
        if v.1.1 = z ∨ v.1.1 = z + 1 then 0 else 1) :
    SizeTwoCyclicFullPermutationCode q a := by
  let routes := sizeTwoCyclicRoutingConstraints_of_hits
    q a C hrow_hit hcol_hit
  let code := sizeTwoCyclicReciprocalPermutationCode_of_grid
    q a C hfree hrow_hit hcol_hit
  refine ⟨code, ?_⟩
  intro x d t u hdiff
  change Fintype.card (SizeTwoCrossShiftedPermutationAgreement q a
    (fun x t => sizeTwoCyclicRoutingEquiv
      q a C hrow_hit hcol_hit routes x t) x d t u) ≤ 1
  rw [Fintype.card_congr (sizeTwoCrossRoutingAgreementEquiv
    q a C hrow_hit hcol_hit routes x d t u)]
  exact sizeTwoCyclicCrossRoutingAgreement_card_le_one
    q a C hfree hcol_hit routes x d t u hdiff

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicCrossRoutingAgreement_card_le_one
#print axioms Erdos85.sizeTwoCyclicFullPermutationCode_of_grid
