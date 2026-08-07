import Proofs.Erdos85SequentialCounter

/-!
# Exact PySAT sequential-counter clause generation

This is a direct functional transcription of `python-sat/cardenc/seqcounter.hh`:
the irredundant Knuth/Healy variant used by `CardEnc` for nontrivial
`atmost` constraints.  Auxiliary variables are keyed by `(k,j)`, allocated
on first encounter, and clauses are emitted in the same nested-loop order.

Matching this order is important: an LRAT proof refers to initial clauses by
their DIMACS positions, so logical equivalence of encodings is not enough.
-/

namespace Erdos85

abbrev DimacsClause := List Int

structure SeqCounterGenState where
  top : Nat
  ids : List ((Nat × Nat) × Nat) := []
  clauses : Array DimacsClause := #[]
deriving Repr, DecidableEq

def seqCounterLookup (key : Nat × Nat) :
    List ((Nat × Nat) × Nat) → Option Nat
  | [] => none
  | (entry :: rest) => if entry.1 = key then some entry.2 else seqCounterLookup key rest

/-- PySAT's `mk_yvar`: reuse an allocated pair, or allocate `top+1`. -/
def seqCounterMkYvar (key : Nat × Nat) : StateM SeqCounterGenState Nat := fun st =>
  match seqCounterLookup key st.ids with
  | some id => (id, st)
  | none =>
      let id := st.top + 1
      (id, { st with top := id, ids := (key, id) :: st.ids })

def seqCounterEmit (clause : DimacsClause) : StateM SeqCounterGenState Unit :=
  modify fun st => { st with clauses := st.clauses.push clause }

/-- One inner-loop iteration at coordinate `(k,j)`. -/
def seqCounterAtMostKStep (vars : Array Int) (t j k : Nat)
    (st : SeqCounterGenState) : SeqCounterGenState :=
  let (skj, st) := seqCounterMkYvar (k, j) st
  let st :=
    if j < vars.size - t - 1 then
      let (skj1, st) := seqCounterMkYvar (k, j + 1) st
      (seqCounterEmit [-(skj : Int), (skj1 : Int)] st).2
    else st
  let (sk1j, st) := seqCounterMkYvar (k + 1, j) st
  (seqCounterEmit
    [-(vars.getD (j + k + 1) 0), -(skj : Int), (sk1j : Int)] st).2

/-- The inner `k=0,...,t-2` portion of a fixed PySAT outer iteration. -/
def seqCounterAtMostKLoop (vars : Array Int) (t j : Nat) :
    Nat → Nat → SeqCounterGenState → SeqCounterGenState
  | 0, _, st => st
  | fuel + 1, k, st =>
      seqCounterAtMostKLoop vars t j fuel (k + 1)
        (seqCounterAtMostKStep vars t j k st)

/-- Allocate and emit the base clause at the start of outer iteration `j`. -/
def seqCounterAtMostJPrefix (vars : Array Int) (j : Nat)
    (st : SeqCounterGenState) : SeqCounterGenState :=
  let (s0j, st) := seqCounterMkYvar (0, j) st
  (seqCounterEmit [-(vars.getD j 0), (s0j : Int)] st).2

/-- Emit the last horizontal clause, when present, and overflow clause at the
end of outer iteration `j`. -/
def seqCounterAtMostJFinish (vars : Array Int) (t j : Nat)
    (st : SeqCounterGenState) : SeqCounterGenState :=
  let (stj, st) := seqCounterMkYvar (t - 1, j) st
  let st :=
    if j < vars.size - t - 1 then
      let (stj1, st) := seqCounterMkYvar (t - 1, j + 1) st
      (seqCounterEmit [-(stj : Int), (stj1 : Int)] st).2
    else st
  (seqCounterEmit [-(vars.getD (j + t) 0), -(stj : Int)] st).2

/-- One complete outer iteration at coordinate `j`. -/
def seqCounterAtMostJStep (vars : Array Int) (t j : Nat)
    (st : SeqCounterGenState) : SeqCounterGenState :=
  seqCounterAtMostJFinish vars t j <|
    seqCounterAtMostKLoop vars t j (t - 1) 0 <|
      seqCounterAtMostJPrefix vars j st

/-- The outer `j=0,...,n-t-1` loop as structural recursion. -/
def seqCounterAtMostJLoop (vars : Array Int) (t : Nat) :
    Nat → Nat → SeqCounterGenState → SeqCounterGenState
  | 0, _, st => st
  | fuel + 1, j, st =>
      seqCounterAtMostJLoop vars t fuel (j + 1)
        (seqCounterAtMostJStep vars t j st)

/-- Core of PySAT's `seqcounter_encode_atmostN` in the nontrivial range
`0 < t < vars.length - 1`.  Outside that range this core intentionally emits
nothing; the trivial unit/single-clause cases are handled by the surrounding
cardinality generator. -/
def seqCounterAtMostCore
    (top : Nat) (vars : Array Int) (t : Nat) : SeqCounterGenState :=
  if 0 < t ∧ t + 1 < vars.size then
    seqCounterAtMostJLoop vars t (vars.size - t) 0 { top := top }
  else
    { top := top }

/-- PySAT's `seqcounter_encode_atleastN`: negate the input literals and
encode an at-most bound of `n-t`. -/
def seqCounterAtLeastCore
    (top : Nat) (vars : Array Int) (t : Nat) : SeqCounterGenState :=
  seqCounterAtMostCore top (vars.map fun v => -v) (vars.size - t)

/-- Nontrivial `CardEnc.equals` block: at-least first, then at-most, with a
fresh auxiliary-pair map but the updated global top variable. -/
def seqCounterEqualsCore
    (top : Nat) (vars : Array Int) (t : Nat) : SeqCounterGenState :=
  let lower := seqCounterAtLeastCore top vars t
  let upper := seqCounterAtMostCore lower.top vars t
  { upper with clauses := lower.clauses ++ upper.clauses }

/-- Reference output from PySAT for `atmost([1,2,3,4,5], 2)` with
auxiliaries beginning at 6.  This kernel-reduced test pins down both clause
order and first-encounter auxiliary allocation. -/
theorem seqCounterAtMostCore_reference_five_two :
    let out := seqCounterAtMostCore 5 #[1, 2, 3, 4, 5] 2
    out.top = 11 ∧ out.clauses.toList =
      [[-1, 6], [-6, 7], [-2, -6, 8], [-8, 9], [-3, -8],
       [-2, 7], [-7, 10], [-3, -7, 9], [-9, 11], [-4, -9],
       [-3, 10], [-4, -10, 11], [-5, -11]] := by
  native_decide

/-- Full reference output of `CardEnc.equals([1,2,3,4,5],2,seqcounter)`.
This pins down the at-least/at-most block order and the reset of the
pair-to-variable map between blocks. -/
theorem seqCounterEqualsCore_reference_five_two :
    let out := seqCounterEqualsCore 5 #[1, 2, 3, 4, 5] 2
    out.top = 17 ∧ out.clauses.toList =
      [[1, 6], [-6, 7], [2, -6, 8], [-8, 9], [3, -8, 10],
       [-10, 11], [4, -10], [2, 7], [3, -7, 9], [4, -9, 11], [5, -11],
       [-1, 12], [-12, 13], [-2, -12, 14], [-14, 15], [-3, -14],
       [-2, 13], [-13, 16], [-3, -13, 15], [-15, 17], [-4, -15],
       [-3, 16], [-4, -16, 17], [-5, -17]] := by
  native_decide

def seqCounterReferenceVars48 : Array Int :=
  (Array.range 48).map fun i => (i + 1 : Nat)

/-- Production-size checks against PySAT: the degree-seven equality block
uses `574` auxiliaries and emits `1148` clauses. -/
theorem seqCounterEqualsCore_reference_48_7 :
    let out := seqCounterEqualsCore 1176 seqCounterReferenceVars48 7
    out.top = 1750 ∧ out.clauses.size = 1148 := by
  native_decide

/-- The degree-eight equality block uses `640` auxiliaries and emits `1280`
clauses, exactly as the certificate generator. -/
theorem seqCounterEqualsCore_reference_48_8 :
    let out := seqCounterEqualsCore 1176 seqCounterReferenceVars48 8
    out.top = 1816 ∧ out.clauses.size = 1280 := by
  native_decide

end Erdos85
