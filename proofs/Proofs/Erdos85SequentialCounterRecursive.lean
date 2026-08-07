import Proofs.Erdos85SequentialCounterReification

/-!
# Recursive presentation of PySAT's sequential counter

The byte-matched generator is written with imperative `for` loops.  This
extensionally identical presentation exposes the two loop counters as
structural recursion, making induction over allocation and clause emission
available to the soundness proof.
-/

namespace Erdos85

/-- The inner `k=0,...,t-2` portion of a fixed PySAT outer iteration. -/
def seqCounterAtMostKLoop (vars : Array Int) (t j : Nat) :
    Nat → Nat → SeqCounterGenState → SeqCounterGenState
  | 0, _, st => st
  | fuel + 1, k, st =>
      let (skj, st) := seqCounterMkYvar (k, j) st
      let st :=
        if j < vars.size - t - 1 then
          let (skj1, st) := seqCounterMkYvar (k, j + 1) st
          (seqCounterEmit [-(skj : Int), (skj1 : Int)] st).2
        else st
      let (sk1j, st) := seqCounterMkYvar (k + 1, j) st
      let st := (seqCounterEmit
        [-(vars.getD (j + k + 1) 0), -(skj : Int), (sk1j : Int)] st).2
      seqCounterAtMostKLoop vars t j fuel (k + 1) st

/-- One complete outer iteration at coordinate `j`. -/
def seqCounterAtMostJStep (vars : Array Int) (t j : Nat)
    (st : SeqCounterGenState) : SeqCounterGenState :=
  let (s0j, st) := seqCounterMkYvar (0, j) st
  let st := (seqCounterEmit [-(vars.getD j 0), (s0j : Int)] st).2
  let st := seqCounterAtMostKLoop vars t j (t - 1) 0 st
  let (stj, st) := seqCounterMkYvar (t - 1, j) st
  let st :=
    if j < vars.size - t - 1 then
      let (stj1, st) := seqCounterMkYvar (t - 1, j + 1) st
      (seqCounterEmit [-(stj : Int), (stj1 : Int)] st).2
    else st
  (seqCounterEmit [-(vars.getD (j + t) 0), -(stj : Int)] st).2

/-- The outer `j=0,...,n-t-1` loop as structural recursion. -/
def seqCounterAtMostJLoop (vars : Array Int) (t : Nat) :
    Nat → Nat → SeqCounterGenState → SeqCounterGenState
  | 0, _, st => st
  | fuel + 1, j, st =>
      seqCounterAtMostJLoop vars t fuel (j + 1)
        (seqCounterAtMostJStep vars t j st)

/-- Recursive form of `seqCounterAtMostCore`. -/
def seqCounterAtMostCoreRecursive
    (top : Nat) (vars : Array Int) (t : Nat) : SeqCounterGenState :=
  if 0 < t ∧ t + 1 < vars.size then
    seqCounterAtMostJLoop vars t (vars.size - t) 0 { top := top }
  else
    { top := top }

/-- The recursive presentation agrees with the authoritative five-input
PySAT reference, including clause order and auxiliary IDs. -/
theorem seqCounterAtMostCoreRecursive_reference_five_two :
    seqCounterAtMostCoreRecursive 5 #[1, 2, 3, 4, 5] 2 =
      seqCounterAtMostCore 5 #[1, 2, 3, 4, 5] 2 := by
  native_decide

/-- Production degree-seven block agrees exactly with the imperative
generator. -/
theorem seqCounterAtMostCoreRecursive_reference_48_7 :
    seqCounterAtMostCoreRecursive 1176 seqCounterReferenceVars48 7 =
      seqCounterAtMostCore 1176 seqCounterReferenceVars48 7 := by
  native_decide

/-- Production degree-eight block agrees exactly with the imperative
generator. -/
theorem seqCounterAtMostCoreRecursive_reference_48_8 :
    seqCounterAtMostCoreRecursive 1176 seqCounterReferenceVars48 8 =
      seqCounterAtMostCore 1176 seqCounterReferenceVars48 8 := by
  native_decide

end Erdos85
