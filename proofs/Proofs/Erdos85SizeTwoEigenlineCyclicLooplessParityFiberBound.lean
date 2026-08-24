import Proofs.Erdos85SizeTwoEigenlineCyclicCentralFiberSubsystem

/-!
# A loopless parity-class fiber packing target

Node: `SIZE-TWO-EIGENLINE(q)`, beneath `GAP A-REG-NONBIP`.

The all-parameter single-fiber target is false already at `q=8`.  The
smallest parameter-uniform target supported by the exact Boolean models keeps
same-fiber agreement on one whole mod-two class of allowed differences.
There are `q / 2 - 1` such fibers at the binary parameters.  This interface
retains global reciprocity and looplessness and supplies the exact
graph-facing consumer.  No exclusion theorem is asserted here.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A reciprocal loopless code whose agreement caps are retained on one
mod-two class of source-difference fibers. -/
structure SizeTwoCyclicLooplessParityFiberCode
    (q : ℕ) [NeZero q] (a : ZMod q) (h2q : 2 ∣ q)
    (parity : ZMod 2) where
  code : SizeTwoCyclicReciprocalPermutationCode q a
  loopless : code.Loopless
  agreement : ∀ t : sizeTwoAllowedDifference q a,
    ZMod.castHom h2q (ZMod 2) t.1 = parity →
      code.toRoutingData.AgreementAt t

/-- An exact code restricts to either parity-class subsystem. -/
def SizeTwoCyclicExactPermutationCode.toParityFiberCode
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicExactPermutationCode q a)
    (h2q : 2 ∣ q) (parity : ZMod 2) :
    SizeTwoCyclicLooplessParityFiberCode q a h2q parity where
  code := code.toReciprocalCode
  loopless := code.loopless
  agreement := by
    intro t _
    exact (code.toSingleFiberCode t).agreement

/-- At parameters `q,a`, one parity class of agreement caps already excludes
a loopless reciprocal code. -/
def SizeTwoCyclicLooplessParityFiberExclusion
    (q : ℕ) [NeZero q] (a : ZMod q) (h2q : 2 ∣ q) : Prop :=
  ∃ parity : ZMod 2,
    IsEmpty (SizeTwoCyclicLooplessParityFiberCode q a h2q parity)

/-- Binary-family form of the parity-class target.  Unlike the false
single-fiber proposal, this keeps `a=0` in scope, as required by the current
connected-component code package. -/
def BinarySizeTwoCyclicLooplessParityFiberBound : Prop :=
  ∀ (k : ℕ), ∀ hk : 3 ≤ k,
    let q := 2 ^ k
    ∀ a : ZMod q,
      SizeTwoCyclicLooplessParityFiberExclusion q a
        (dvd_pow_self 2 (by omega : k ≠ 0))

/-- The parity-class target directly excludes the exact cyclic code produced
by the connected-component package. -/
theorem sizeTwoCyclicExactCode_isEmpty_of_looplessParityFiberExclusion
    (q : ℕ) [NeZero q] (a : ZMod q) (h2q : 2 ∣ q)
    (hpack : SizeTwoCyclicLooplessParityFiberExclusion q a h2q) :
    IsEmpty (SizeTwoCyclicExactPermutationCode q a) := by
  constructor
  intro code
  obtain ⟨parity, hparity⟩ := hpack
  exact hparity.false (code.toParityFiberCode h2q parity)

/-- A hypothetical exterior grid yields the parity-class subsystem for both
parities, contradicting exclusion of either one. -/
theorem false_of_sizeTwoCyclicLooplessParityFiberExclusion
    (q : ℕ) [NeZero q] (a : ZMod q) (h2q : 2 ∣ q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hfree : ¬ containsC4 (sizeTwoCyclicExteriorCell q a) C)
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = y).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1)
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1)
    (hpack : SizeTwoCyclicLooplessParityFiberExclusion q a h2q) : False := by
  obtain ⟨parity, hparity⟩ := hpack
  let code := sizeTwoCyclicExactPermutationCode_of_grid
    q a C hfree hrow_hit hcol_hit
  exact hparity.false (code.toParityFiberCode h2q parity)

end

end Erdos85

#print axioms Erdos85.false_of_sizeTwoCyclicLooplessParityFiberExclusion
#print axioms
  Erdos85.sizeTwoCyclicExactCode_isEmpty_of_looplessParityFiberExclusion
