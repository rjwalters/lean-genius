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

/-! ## Signed DIMACS semantics -/

abbrev DimacsValuation := Nat → Bool

/-- DIMACS variables are positive integers; a negative integer denotes the
Boolean negation of the variable with the same absolute identifier. -/
def dimacsLitValue (val : DimacsValuation) (lit : Int) : Bool :=
  if 0 < lit then val lit.natAbs else !(val lit.natAbs)

def dimacsClauseSatisfied (val : DimacsValuation)
    (clause : DimacsClause) : Prop :=
  ∃ lit ∈ clause, dimacsLitValue val lit = true

theorem dimacsLitValue_neg (val : DimacsValuation) {lit : Int}
    (hlit : lit ≠ 0) :
    dimacsLitValue val (-lit) = !(dimacsLitValue val lit) := by
  unfold dimacsLitValue
  rw [Int.natAbs_neg]
  by_cases hpos : 0 < lit
  · have hnonneg : 0 ≤ lit := hpos.le
    simp [hpos, hnonneg]
  · have hlt : lit < 0 := by omega
    simp [hpos, hlt]

theorem dimacsLitValue_natCast (val : DimacsValuation) {id : Nat}
    (hid : 0 < id) : dimacsLitValue val (id : Int) = val id := by
  simp [dimacsLitValue, hid]

/-- Numeric reification of the base clause. -/
theorem dimacs_seqCounter_base_clause_satisfied {n : Nat}
    (x : Fin n → Bool) (val : DimacsValuation) (j : Nat) (hj : j < n)
    (inputId auxId : Nat) (hinput : 0 < inputId) (haux : 0 < auxId)
    (hinputVal : val inputId = x ⟨j, hj⟩)
    (hauxVal : val auxId = seqCounterWitness x j 0) :
    dimacsClauseSatisfied val [-(inputId : Int), (auxId : Int)] := by
  by_cases hx : x ⟨j, hj⟩ = true
  · refine ⟨(auxId : Int), by simp, ?_⟩
    rw [dimacsLitValue_natCast val haux, hauxVal,
      seqCounterKnuth_base x j hj hx]
  · refine ⟨-(inputId : Int), by simp, ?_⟩
    rw [dimacsLitValue_neg val (by exact_mod_cast hinput.ne'),
      dimacsLitValue_natCast val hinput, hinputVal]
    cases hval : x ⟨j, hj⟩ <;> simp_all

/-- Numeric reification of the horizontal clause. -/
theorem dimacs_seqCounter_horizontal_clause_satisfied {n : Nat}
    (x : Fin n → Bool) (val : DimacsValuation) (k j : Nat)
    (hnext : j + k + 1 < n) (leftId rightId : Nat)
    (hleft : 0 < leftId) (hright : 0 < rightId)
    (hleftVal : val leftId = seqCounterWitness x (j + k) k)
    (hrightVal : val rightId = seqCounterWitness x (j + 1 + k) k) :
    dimacsClauseSatisfied val [-(leftId : Int), (rightId : Int)] := by
  by_cases hs : seqCounterWitness x (j + k) k = true
  · refine ⟨(rightId : Int), by simp, ?_⟩
    rw [dimacsLitValue_natCast val hright, hrightVal,
      seqCounterKnuth_horizontal x k j hnext hs]
  · refine ⟨-(leftId : Int), by simp, ?_⟩
    rw [dimacsLitValue_neg val (by exact_mod_cast hleft.ne'),
      dimacsLitValue_natCast val hleft, hleftVal]
    cases hval : seqCounterWitness x (j + k) k <;> simp_all

/-- Numeric reification of the diagonal clause. -/
theorem dimacs_seqCounter_diagonal_clause_satisfied {n : Nat}
    (x : Fin n → Bool) (val : DimacsValuation) (k j : Nat)
    (hidx : j + k + 1 < n) (inputId leftId rightId : Nat)
    (hinput : 0 < inputId) (hleft : 0 < leftId) (hright : 0 < rightId)
    (hinputVal : val inputId = x ⟨j + k + 1, hidx⟩)
    (hleftVal : val leftId = seqCounterWitness x (j + k) k)
    (hrightVal : val rightId = seqCounterWitness x (j + (k + 1)) (k + 1)) :
    dimacsClauseSatisfied val
      [-(inputId : Int), -(leftId : Int), (rightId : Int)] := by
  by_cases hx : x ⟨j + k + 1, hidx⟩ = true
  · by_cases hs : seqCounterWitness x (j + k) k = true
    · refine ⟨(rightId : Int), by simp, ?_⟩
      rw [dimacsLitValue_natCast val hright, hrightVal,
        seqCounterKnuth_diagonal x k j hidx hx hs]
    · refine ⟨-(leftId : Int), by simp, ?_⟩
      rw [dimacsLitValue_neg val (by exact_mod_cast hleft.ne'),
        dimacsLitValue_natCast val hleft, hleftVal]
      cases hval : seqCounterWitness x (j + k) k <;> simp_all
  · refine ⟨-(inputId : Int), by simp, ?_⟩
    rw [dimacsLitValue_neg val (by exact_mod_cast hinput.ne'),
      dimacsLitValue_natCast val hinput, hinputVal]
    cases hval : x ⟨j + k + 1, hidx⟩ <;> simp_all

/-- Numeric reification of the terminal overflow clause. -/
theorem dimacs_seqCounter_overflow_clause_satisfied {n : Nat}
    (x : Fin n → Bool) (val : DimacsValuation) (t j : Nat)
    (ht : 0 < t) (hidx : j + t < n) (htotal : seqPrefixTrue x n ≤ t)
    (inputId auxId : Nat) (hinput : 0 < inputId) (haux : 0 < auxId)
    (hinputVal : val inputId = x ⟨j + t, hidx⟩)
    (hauxVal : val auxId = seqCounterWitness x (j + (t - 1)) (t - 1)) :
    dimacsClauseSatisfied val [-(inputId : Int), -(auxId : Int)] := by
  by_cases hx : x ⟨j + t, hidx⟩ = true
  · refine ⟨-(auxId : Int), by simp, ?_⟩
    rw [dimacsLitValue_neg val (by exact_mod_cast haux.ne'),
      dimacsLitValue_natCast val haux, hauxVal,
      seqCounterKnuth_no_overflow x t j ht hidx htotal hx]
    rfl
  · refine ⟨-(inputId : Int), by simp, ?_⟩
    rw [dimacsLitValue_neg val (by exact_mod_cast hinput.ne'),
      dimacsLitValue_natCast val hinput, hinputVal]
    cases hval : x ⟨j + t, hidx⟩ <;> simp_all

end Erdos85
