import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationReciprocity

/-!
# The routed-dart involution

Node: `SIZE-TWO-EIGENLINE(q)`, beneath `GAP A-REG-NONBIP`.

Reciprocity makes every abstract routing edge reversible.  Reversing a route
recovers its original target difference, and hence routed darts carry a
fixed-point-free-style edge reversal suitable for parity arguments.
-/

namespace Erdos85

noncomputable section

theorem SizeTwoCyclicReciprocalPermutationCode.reverse_targetDifference
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1) :
    let s := code.targetDifference x t r
    let reverseRow : SizeTwoAdmissibleTargetRow q s.1 :=
      ⟨-r.1, code.reverse_admissible x t r⟩
    code.targetDifference (x + r.1) s reverseRow = t := by
  dsimp only
  let s := code.targetDifference x t r
  let reverseRow : SizeTwoAdmissibleTargetRow q s.1 :=
    ⟨-r.1, code.reverse_admissible x t r⟩
  apply Subtype.ext
  have hcol := code.target_column_eq (x + r.1) s reverseRow
  have hrec := code.reciprocity x t r
  change reverseRow.1 +
      (code.targetDifference (x + r.1) s reverseRow).1 =
    (code.toPermutationCode.perm (x + r.1) s reverseRow).1 at hcol
  change (code.toPermutationCode.perm (x + r.1) s reverseRow).1 =
    t.1 - r.1 at hrec
  rw [hrec] at hcol
  dsimp [reverseRow] at hcol
  have := congrArg (fun z : ZMod q => r.1 + z) hcol
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this

def SizeTwoCyclicReciprocalPermutationCode.Loopless
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a) : Prop :=
  ∀ (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1),
    ¬(r.1 = 0 ∧ code.targetDifference x t r = t)

theorem sizeTwoCyclicReciprocalPermutationCode_of_grid_loopless
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hfree : ¬ containsC4 (sizeTwoCyclicExteriorCell q a) C)
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = y).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1)
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1) :
    (sizeTwoCyclicReciprocalPermutationCode_of_grid
      q a C hfree hrow_hit hcol_hit).Loopless := by
  let routes := sizeTwoCyclicRoutingConstraints_of_hits
    q a C hrow_hit hcol_hit
  intro x t r hfixed
  have hadj := sizeTwoCyclicRowRoute_spec q a C routes x t r
  apply C.loopless.irrefl (sizeTwoCyclicCellAt q a x t)
  convert hadj
  · rw [hfixed.1]
    simp
  · simpa [routes, sizeTwoCyclicReciprocalPermutationCode_of_grid] using
      hfixed.2.symm

def SizeTwoCyclicRouteDart
    (q : ℕ) [NeZero q] (a : ZMod q)
    (_code : SizeTwoCyclicReciprocalPermutationCode q a) :=
  {e : ZMod q × (sizeTwoAllowedDifference q a × ZMod q) //
    e.2.1.1 ≠ e.2.2 ∧ e.2.1.1 ≠ e.2.2 - 1}

def SizeTwoCyclicRouteDart.reverse
    {q : ℕ} [NeZero q] {a : ZMod q}
    {code : SizeTwoCyclicReciprocalPermutationCode q a}
    (e : SizeTwoCyclicRouteDart q a code) :
    SizeTwoCyclicRouteDart q a code :=
  let x := e.1.1
  let t := e.1.2.1
  let r : SizeTwoAdmissibleTargetRow q t.1 := ⟨e.1.2.2, e.2⟩
  let s := code.targetDifference x t r
  ⟨(x + r.1, (s, -r.1)), code.reverse_admissible x t r⟩

theorem SizeTwoCyclicRouteDart.reverse_reverse
    {q : ℕ} [NeZero q] {a : ZMod q}
    {code : SizeTwoCyclicReciprocalPermutationCode q a}
    (e : SizeTwoCyclicRouteDart q a code) :
    e.reverse.reverse = e := by
  rcases e with ⟨⟨x, t, r⟩, hr⟩
  apply Subtype.ext
  apply Prod.ext
  · simp [SizeTwoCyclicRouteDart.reverse]
  · apply Prod.ext
    · apply Subtype.ext
      exact congrArg Subtype.val
        (code.reverse_targetDifference x t ⟨r, hr⟩)
    · simp [SizeTwoCyclicRouteDart.reverse]

theorem SizeTwoCyclicRouteDart.reverse_ne
    {q : ℕ} [NeZero q] {a : ZMod q}
    {code : SizeTwoCyclicReciprocalPermutationCode q a}
    (hloop : code.Loopless)
    (e : SizeTwoCyclicRouteDart q a code) :
    e.reverse ≠ e := by
  rcases e with ⟨⟨x, t, r⟩, hr⟩
  intro heq
  have hb := congrArg (fun e : SizeTwoCyclicRouteDart q a code => e.1.1) heq
  have hd := congrArg (fun e : SizeTwoCyclicRouteDart q a code => e.1.2.1) heq
  apply hloop x t ⟨r, hr⟩
  constructor
  · dsimp [SizeTwoCyclicRouteDart.reverse] at hb
    apply add_left_cancel (a := x)
    simpa using hb
  · simpa [SizeTwoCyclicRouteDart.reverse] using hd

def sizeTwoCyclicRouteDartReverseEquiv
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicReciprocalPermutationCode q a) :
    SizeTwoCyclicRouteDart q a code ≃ SizeTwoCyclicRouteDart q a code where
  toFun := SizeTwoCyclicRouteDart.reverse
  invFun := SizeTwoCyclicRouteDart.reverse
  left_inv := SizeTwoCyclicRouteDart.reverse_reverse
  right_inv := SizeTwoCyclicRouteDart.reverse_reverse

end

end Erdos85

#print axioms Erdos85.SizeTwoCyclicReciprocalPermutationCode.reverse_targetDifference
#print axioms Erdos85.SizeTwoCyclicRouteDart.reverse_reverse
#print axioms Erdos85.SizeTwoCyclicRouteDart.reverse_ne
