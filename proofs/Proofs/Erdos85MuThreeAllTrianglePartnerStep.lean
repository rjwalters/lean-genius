import Proofs.Erdos85MuThreeAllTrianglePartnerInvolutions

/-!
# The two-edge step around partner cycles

Composing column mate with row mate advances two edges around an alternating
partner component.  This permutation has no cycles of length one or two, so
every partner component has alternating graph length at least six.
-/

open SimpleGraph

namespace Erdos85

/-- Two-edge step `rho ∘ kappa` on the non-`H` partner support. -/
noncomputable def MuThreeMixedGridCode.partnerStepEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) :
    mixedGridNonHCell H K ≃ mixedGridNonHCell H K :=
  (code.columnMateEquiv H K C).trans (code.rowMateEquiv H K C)

@[simp] theorem MuThreeMixedGridCode.partnerStepEquiv_apply
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : mixedGridNonHCell H K) :
    code.partnerStepEquiv H K C u =
      code.rowMate H K C (code.columnMate H K C u) := rfl

/-- The two-edge step has no fixed point. -/
theorem MuThreeMixedGridCode.partnerStep_ne_self
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : mixedGridNonHCell H K) :
    code.partnerStepEquiv H K C u ≠ u := by
  intro h
  have hr := congrArg (code.rowMate H K C) h
  change code.rowMate H K C
      (code.rowMate H K C (code.columnMate H K C u)) =
    code.rowMate H K C u at hr
  rw [code.rowMate_rowMate H K C] at hr
  exact code.rowMate_ne_columnMate H K C u hr.symm

/-- The two-edge step has no orbit of length two. -/
theorem MuThreeMixedGridCode.partnerStep_partnerStep_ne_self
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : mixedGridNonHCell H K) :
    code.partnerStepEquiv H K C (code.partnerStepEquiv H K C u) ≠ u := by
  intro h
  have hr := congrArg (code.rowMate H K C) h
  change code.rowMate H K C
      (code.rowMate H K C
        (code.columnMate H K C
          (code.rowMate H K C (code.columnMate H K C u)))) =
    code.rowMate H K C u at hr
  rw [code.rowMate_rowMate H K C] at hr
  have hc := congrArg (code.columnMate H K C) hr
  rw [code.columnMate_columnMate H K C] at hc
  exact code.rowMate_columnMate_ne_columnMate_rowMate H K C u hc

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.partnerStep_ne_self
#print axioms Erdos85.MuThreeMixedGridCode.partnerStep_partnerStep_ne_self
