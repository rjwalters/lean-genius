import Proofs.Erdos85SizeTwoEigenlineCyclicRoutingAgreement

/-!
# The graph-free cyclic permutation code

Node: `SIZE-TWO-EIGENLINE(q)`, beneath `GAP A-REG-NONBIP`.

This file forgets the exterior graph after extracting its routing
permutations.  The resulting finite object is a family of bijections, one for
each base point and allowed difference, whose shifted agreements have size at
most one.  A uniform refutation may now target this algebraic code directly.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

abbrev SizeTwoCyclicPermutationFamily (q : ℕ) (a : ZMod q) :=
  ∀ (x : ZMod q) (t : sizeTwoAllowedDifference q a),
    SizeTwoAdmissibleTargetRow q t.1 ≃ SizeTwoAdmissibleTargetColumn q

structure SizeTwoShiftedPermutationAgreement
    (q : ℕ) [NeZero q] (a : ZMod q)
    (P : SizeTwoCyclicPermutationFamily q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a) where
  row : SizeTwoAdmissibleTargetRow q t.1
  shifted_admissible : t.1 ≠ row.1 - d ∧ t.1 ≠ (row.1 - d) - 1
  column_eq :
    x + (P x t row).1 =
      (x + d) + (P (x + d) t ⟨row.1 - d, shifted_admissible⟩).1

theorem SizeTwoShiftedPermutationAgreement.row_injective
    {q : ℕ} [NeZero q] {a : ZMod q} {P : SizeTwoCyclicPermutationFamily q a}
    {x d : ZMod q} {t : sizeTwoAllowedDifference q a} :
    Function.Injective (fun w : SizeTwoShiftedPermutationAgreement
      q a P x d t => w.row) := by
  intro u v huv
  cases u
  cases v
  cases huv
  rfl

instance SizeTwoShiftedPermutationAgreement.instFinite
    {q : ℕ} [NeZero q] {a : ZMod q} {P : SizeTwoCyclicPermutationFamily q a}
    {x d : ZMod q} {t : sizeTwoAllowedDifference q a} :
    Finite (SizeTwoShiftedPermutationAgreement q a P x d t) :=
  Finite.of_injective (fun w => w.row.1) (by
    intro u v h
    apply SizeTwoShiftedPermutationAgreement.row_injective
    exact Subtype.ext h)

noncomputable instance SizeTwoShiftedPermutationAgreement.instFintype
    {q : ℕ} [NeZero q] {a : ZMod q} {P : SizeTwoCyclicPermutationFamily q a}
    {x d : ZMod q} {t : sizeTwoAllowedDifference q a} :
    Fintype (SizeTwoShiftedPermutationAgreement q a P x d t) :=
  Fintype.ofFinite _

structure SizeTwoCyclicPermutationCode (q : ℕ) [NeZero q] (a : ZMod q) where
  perm : SizeTwoCyclicPermutationFamily q a
  agreement_le_one : ∀ (x d : ZMod q), d ≠ 0 →
    ∀ t : sizeTwoAllowedDifference q a,
      Fintype.card (SizeTwoShiftedPermutationAgreement
        q a perm x d t) ≤ 1

def sizeTwoRoutingAgreementEquiv
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = y).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1)
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1)
    (routes : SizeTwoCyclicRoutingConstraints q a C)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a) :
    SizeTwoShiftedPermutationAgreement q a
        (fun x t => sizeTwoCyclicRoutingEquiv
          q a C hrow_hit hcol_hit routes x t) x d t ≃
      SizeTwoCyclicRoutingAgreement
        q a C hcol_hit routes x d t where
  toFun w := ⟨w.row, w.shifted_admissible, by
    simpa [sizeTwoCyclicRoutingEquiv] using w.column_eq⟩
  invFun w := ⟨w.row, w.shifted_admissible, by
    simpa [sizeTwoCyclicRoutingEquiv] using w.column_eq⟩
  left_inv w := by cases w; rfl
  right_inv w := by cases w; rfl

def sizeTwoCyclicPermutationCode_of_grid
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hfree : ¬ containsC4 (sizeTwoCyclicExteriorCell q a) C)
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = y).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1)
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1) :
    SizeTwoCyclicPermutationCode q a := by
  let routes := sizeTwoCyclicRoutingConstraints_of_hits
    q a C hrow_hit hcol_hit
  let P : SizeTwoCyclicPermutationFamily q a := fun x t =>
    sizeTwoCyclicRoutingEquiv q a C hrow_hit hcol_hit routes x t
  refine ⟨P, ?_⟩
  intro x d hd t
  rw [Fintype.card_congr
    (sizeTwoRoutingAgreementEquiv
      q a C hrow_hit hcol_hit routes x d t)]
  exact sizeTwoCyclicRoutingAgreement_card_le_one
    q a C hfree hcol_hit routes x d hd t

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicPermutationCode_of_grid
