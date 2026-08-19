import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationReconstructionC4

/-!
# The exact graph-free cyclic permutation object

A reciprocal code reconstructs symmetry, but looplessness and the full
cross-difference agreement law are separate indispensable invariants.  This
structure packages precisely the data needed to pass both ways between the
cyclic graph and its permutation encoding.
-/

namespace Erdos85

noncomputable section

structure SizeTwoCyclicExactPermutationCode
    (q : ℕ) [NeZero q] (a : ZMod q) where
  toFullCode : SizeTwoCyclicFullPermutationCode q a
  loopless : toFullCode.toReciprocalCode.Loopless

namespace SizeTwoCyclicExactPermutationCode

def toReciprocalCode
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicExactPermutationCode q a) :
    SizeTwoCyclicReciprocalPermutationCode q a :=
  code.toFullCode.toReciprocalCode

def graph
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicExactPermutationCode q a) :
    SimpleGraph (sizeTwoCyclicExteriorCell q a) :=
  sizeTwoCyclicCodeGraph q a code.toReciprocalCode

theorem graph_row_hit
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicExactPermutationCode q a)
    [DecidableRel code.graph.Adj]
    (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q) :
    ((code.graph.neighborFinset u).filter fun v => v.1.1 = y).card =
      if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1 :=
  by
    letI : DecidableRel
        (sizeTwoCyclicCodeGraph q a code.toReciprocalCode).Adj := by
      simpa [graph] using (inferInstance : DecidableRel code.graph.Adj)
    exact sizeTwoCyclicCodeGraph_row_hit q a code.toReciprocalCode
      code.loopless u y

theorem graph_column_hit
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicExactPermutationCode q a)
    [DecidableRel code.graph.Adj]
    (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q) :
    ((code.graph.neighborFinset u).filter fun v => v.1.2 = z).card =
      if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1 :=
  by
    letI : DecidableRel
        (sizeTwoCyclicCodeGraph q a code.toReciprocalCode).Adj := by
      simpa [graph] using (inferInstance : DecidableRel code.graph.Adj)
    exact sizeTwoCyclicCodeGraph_column_hit q a code.toReciprocalCode
      code.loopless u z

theorem graph_not_containsC4
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicExactPermutationCode q a) :
    ¬ containsC4 (sizeTwoCyclicExteriorCell q a) code.graph :=
  sizeTwoCyclicFullCodeGraph_not_containsC4
    q a code.toFullCode code.loopless

end SizeTwoCyclicExactPermutationCode

/-- Every C4-free cyclic grid with the normalized hit laws yields the exact
graph-free permutation object. -/
def sizeTwoCyclicExactPermutationCode_of_grid
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hfree : ¬ containsC4 (sizeTwoCyclicExteriorCell q a) C)
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = y).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1)
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1) :
    SizeTwoCyclicExactPermutationCode q a := by
  let full := sizeTwoCyclicFullPermutationCode_of_grid
    q a C hfree hrow_hit hcol_hit
  refine ⟨full, ?_⟩
  simpa [full, sizeTwoCyclicFullPermutationCode_of_grid] using
    (sizeTwoCyclicReciprocalPermutationCode_of_grid_loopless
      q a C hfree hrow_hit hcol_hit)

end

end Erdos85

#print axioms Erdos85.SizeTwoCyclicExactPermutationCode.graph_row_hit
#print axioms Erdos85.SizeTwoCyclicExactPermutationCode.graph_column_hit
#print axioms Erdos85.SizeTwoCyclicExactPermutationCode.graph_not_containsC4
#print axioms Erdos85.sizeTwoCyclicExactPermutationCode_of_grid
