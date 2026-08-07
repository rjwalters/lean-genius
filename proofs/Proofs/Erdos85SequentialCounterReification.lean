import Proofs.Erdos85SequentialCounterGenerator
import Proofs.Erdos85SequentialCounterClauses

/-!
# Reifying sequential-counter atoms as DIMACS variables

These elementary state lemmas isolate the only imperative aspect of the
PySAT transcription: `mk_yvar` memoizes a key, while clause emission leaves
the allocation table unchanged.  They are the invariants used to relate the
numeric generator to the symbolic clause soundness theorems.
-/

namespace Erdos85

/-- Every call to `mk_yvar` leaves the returned identifier registered under
the requested Knuth coordinate. -/
theorem seqCounterMkYvar_lookup (key : Nat × Nat) (st : SeqCounterGenState) :
    let out := seqCounterMkYvar key st
    seqCounterLookup key out.2.ids = some out.1 := by
  simp only [seqCounterMkYvar]
  split
  next id h => exact h
  next h => simp [seqCounterLookup]

/-- Allocating a counter variable never changes clauses already emitted. -/
theorem seqCounterMkYvar_clauses (key : Nat × Nat)
    (st : SeqCounterGenState) :
    (seqCounterMkYvar key st).2.clauses = st.clauses := by
  simp only [seqCounterMkYvar]
  split <;> rfl

/-- Emitting a clause does not change the auxiliary-variable table. -/
theorem seqCounterEmit_ids (clause : DimacsClause)
    (st : SeqCounterGenState) :
    (seqCounterEmit clause st).2.ids = st.ids := by
  rfl

/-- Emitting a clause does not change the current greatest DIMACS ID. -/
theorem seqCounterEmit_top (clause : DimacsClause)
    (st : SeqCounterGenState) :
    (seqCounterEmit clause st).2.top = st.top := by
  rfl

/-- A successful lookup is a genuine entry in the allocation table. -/
theorem seqCounterLookup_mem {key : Nat × Nat} {id : Nat}
    {ids : List ((Nat × Nat) × Nat)}
    (h : seqCounterLookup key ids = some id) : (key, id) ∈ ids := by
  induction ids with
  | nil => simp [seqCounterLookup] at h
  | cons entry rest ih =>
      simp only [seqCounterLookup] at h
      split at h
      · next heq =>
          have hid : entry.2 = id := Option.some.inj h
          have hentry : entry = (key, id) := Prod.ext heq hid
          simp [hentry]
      · next _ => exact List.mem_cons_of_mem _ (ih h)

/-- If a key was already allocated, `mk_yvar` is observationally the
identity and returns its existing identifier. -/
theorem seqCounterMkYvar_of_lookup {key : Nat × Nat} {id : Nat}
    {st : SeqCounterGenState} (h : seqCounterLookup key st.ids = some id) :
    seqCounterMkYvar key st = (id, st) := by
  simp [seqCounterMkYvar, h]

/-- If a key is fresh, `mk_yvar` allocates exactly `top+1` and prepends the
correspondence to the table. -/
theorem seqCounterMkYvar_of_fresh {key : Nat × Nat}
    {st : SeqCounterGenState} (h : seqCounterLookup key st.ids = none) :
    seqCounterMkYvar key st =
      (st.top + 1,
        { top := st.top + 1
          ids := (key, st.top + 1) :: st.ids
          clauses := st.clauses }) := by
  simp [seqCounterMkYvar, h]

end Erdos85
