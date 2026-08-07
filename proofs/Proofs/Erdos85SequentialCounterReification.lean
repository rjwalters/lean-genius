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

/-- The identifier returned by `mk_yvar` is immediately present in its
updated allocation table. -/
theorem seqCounterMkYvar_mem (key : Nat × Nat) (st : SeqCounterGenState) :
    let out := seqCounterMkYvar key st
    (key, out.1) ∈ out.2.ids := by
  exact seqCounterLookup_mem (seqCounterMkYvar_lookup key st)

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

/-! ## Allocation-table integrity -/

/-- Keys and identifiers are unique, and every auxiliary identifier lies in
the interval opened above the block's initial `top`. -/
structure SeqCounterAllocationInvariant (initialTop : Nat)
    (st : SeqCounterGenState) : Prop where
  top_bound : initialTop ≤ st.top
  keys_nodup : (st.ids.map Prod.fst).Nodup
  ids_nodup : (st.ids.map Prod.snd).Nodup
  id_bounds : ∀ entry ∈ st.ids,
    initialTop < entry.2 ∧ entry.2 ≤ st.top

theorem seqCounterLookup_eq_none_iff (key : Nat × Nat)
    (ids : List ((Nat × Nat) × Nat)) :
    seqCounterLookup key ids = none ↔ key ∉ ids.map Prod.fst := by
  induction ids with
  | nil => simp [seqCounterLookup]
  | cons entry rest ih =>
      by_cases heq : entry.1 = key
      · simp [seqCounterLookup, heq]
      · have hne : key ≠ entry.1 := fun h => heq h.symm
        simp [seqCounterLookup, heq, hne, ih]

theorem seqCounterLookup_eq_none_of_not_mem (key : Nat × Nat)
    {ids : List ((Nat × Nat) × Nat)}
    (hkey : key ∉ ids.map Prod.fst) :
    seqCounterLookup key ids = none :=
  (seqCounterLookup_eq_none_iff key ids).mpr hkey

theorem seqCounterAllocationInvariant_initial (top : Nat) :
    SeqCounterAllocationInvariant top ({ top := top } : SeqCounterGenState) := by
  constructor <;> simp

/-- `mk_yvar` preserves allocation integrity.  This is the key fact that
makes the final table a genuine reification rather than a many-to-one map. -/
theorem seqCounterAllocationInvariant_mkYvar
    {initialTop : Nat} {st : SeqCounterGenState}
    (hinv : SeqCounterAllocationInvariant initialTop st)
    (key : Nat × Nat) :
    SeqCounterAllocationInvariant initialTop (seqCounterMkYvar key st).2 := by
  unfold seqCounterMkYvar
  split
  next id hlookup => simpa using hinv
  next hlookup =>
    simp only
    constructor
    · exact hinv.top_bound.trans (Nat.le_succ _)
    · simp only [List.map_cons, List.nodup_cons]
      exact ⟨(seqCounterLookup_eq_none_iff key st.ids).mp hlookup,
        hinv.keys_nodup⟩
    · simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmem
        have hbound := (hinv.id_bounds entry hentry).2
        omega
      · exact hinv.ids_nodup
    · intro entry hentry
      simp only [List.mem_cons] at hentry
      rcases hentry with rfl | hentry
      · change initialTop < st.top + 1 ∧ st.top + 1 ≤ st.top + 1
        exact ⟨Nat.lt_succ_of_le hinv.top_bound, le_rfl⟩
      · have hb := hinv.id_bounds entry hentry
        exact ⟨hb.1, hb.2.trans (Nat.le_succ _)⟩

theorem seqCounterAllocationInvariant_emit
    {initialTop : Nat} {st : SeqCounterGenState}
    (hinv : SeqCounterAllocationInvariant initialTop st)
    (clause : DimacsClause) :
    SeqCounterAllocationInvariant initialTop (seqCounterEmit clause st).2 := by
  constructor
  · exact hinv.top_bound
  · exact hinv.keys_nodup
  · exact hinv.ids_nodup
  · exact hinv.id_bounds

/-- Later generator states retain every earlier key-to-ID correspondence. -/
def SeqCounterIdsExtend (before after : SeqCounterGenState) : Prop :=
  ∀ entry ∈ before.ids, entry ∈ after.ids

theorem SeqCounterIdsExtend.refl (st : SeqCounterGenState) :
    SeqCounterIdsExtend st st := by
  intro entry hentry
  exact hentry

theorem SeqCounterIdsExtend.trans {a b c : SeqCounterGenState}
    (hab : SeqCounterIdsExtend a b) (hbc : SeqCounterIdsExtend b c) :
    SeqCounterIdsExtend a c := by
  intro entry hentry
  exact hbc entry (hab entry hentry)

theorem seqCounterIdsExtend_mkYvar (key : Nat × Nat)
    (st : SeqCounterGenState) :
    SeqCounterIdsExtend st (seqCounterMkYvar key st).2 := by
  unfold seqCounterMkYvar
  split
  · exact SeqCounterIdsExtend.refl st
  · intro entry hentry
    exact List.mem_cons_of_mem _ hentry

theorem seqCounterIdsExtend_emit (clause : DimacsClause)
    (st : SeqCounterGenState) :
    SeqCounterIdsExtend st (seqCounterEmit clause st).2 := by
  exact SeqCounterIdsExtend.refl st

theorem seqCounterIdsExtend_preserves_mem {before after : SeqCounterGenState}
    (hext : SeqCounterIdsExtend before after) {entry : (Nat × Nat) × Nat}
    (hentry : entry ∈ before.ids) : entry ∈ after.ids :=
  hext entry hentry

/-- Later generator states retain every clause emitted by earlier states. -/
def SeqCounterClausesExtend (before after : SeqCounterGenState) : Prop :=
  ∀ clause ∈ before.clauses, clause ∈ after.clauses

theorem SeqCounterClausesExtend.refl (st : SeqCounterGenState) :
    SeqCounterClausesExtend st st := by
  intro clause hclause
  exact hclause

theorem SeqCounterClausesExtend.trans {a b c : SeqCounterGenState}
    (hab : SeqCounterClausesExtend a b)
    (hbc : SeqCounterClausesExtend b c) :
    SeqCounterClausesExtend a c := by
  intro clause hclause
  exact hbc clause (hab clause hclause)

theorem seqCounterClausesExtend_mkYvar (key : Nat × Nat)
    (st : SeqCounterGenState) :
    SeqCounterClausesExtend st (seqCounterMkYvar key st).2 := by
  intro clause hclause
  rw [seqCounterMkYvar_clauses]
  exact hclause

theorem seqCounterClausesExtend_emit (clause : DimacsClause)
    (st : SeqCounterGenState) :
    SeqCounterClausesExtend st (seqCounterEmit clause st).2 := by
  intro old hold
  change old ∈ st.clauses.push clause
  have hdisj : old ∈ st.clauses ∨ old = clause := Or.inl hold
  simpa using hdisj

/-- A just-emitted clause belongs to the updated state. -/
theorem seqCounterEmit_mem (clause : DimacsClause)
    (st : SeqCounterGenState) :
    clause ∈ (seqCounterEmit clause st).2.clauses := by
  change clause ∈ st.clauses.push clause
  exact Array.mem_push_self

/-- Reverse lookup used to interpret a final numeric auxiliary identifier. -/
def seqCounterKeyLookup (id : Nat) :
    List ((Nat × Nat) × Nat) → Option (Nat × Nat)
  | [] => none
  | entry :: rest =>
      if entry.2 = id then some entry.1 else seqCounterKeyLookup id rest

theorem seqCounterKeyLookup_of_mem {key : Nat × Nat} {id : Nat}
    {ids : List ((Nat × Nat) × Nat)}
    (hnodup : (ids.map Prod.snd).Nodup)
    (hmem : (key, id) ∈ ids) :
    seqCounterKeyLookup id ids = some key := by
  induction ids with
  | nil => simp at hmem
  | cons entry rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp [seqCounterKeyLookup]
      · have hidmem : id ∈ rest.map Prod.snd := by
          exact List.mem_map.mpr ⟨(key, id), hmem, rfl⟩
        have hne : entry.2 ≠ id := fun heq => hnodup.1 (heq ▸ hidmem)
        simp [seqCounterKeyLookup, hne, ih hnodup.2 hmem]

/-- Canonical truth value assigned to a numeric auxiliary ID by the final
allocation table.  Unallocated IDs default to `false`. -/
def seqCounterTableVal {n : Nat} (x : Fin n → Bool)
    (ids : List ((Nat × Nat) × Nat)) : Nat → Bool := fun id =>
  match seqCounterKeyLookup id ids with
  | some (k, j) => seqCounterWitness x (j + k) k
  | none => false

theorem seqCounterTableVal_of_mem {n : Nat} (x : Fin n → Bool)
    {key : Nat × Nat} {id : Nat} {ids : List ((Nat × Nat) × Nat)}
    (hnodup : (ids.map Prod.snd).Nodup)
    (hmem : (key, id) ∈ ids) :
    seqCounterTableVal x ids id =
      seqCounterWitness x (key.2 + key.1) key.1 := by
  rw [seqCounterTableVal, seqCounterKeyLookup_of_mem hnodup hmem]

/-! ## Signed DIMACS semantics -/

abbrev DimacsValuation := Nat → Bool

/-- Final valuation of one counter block: identifiers belonging to the
pre-existing CNF retain their supplied values, while freshly allocated IDs
are read from the counter table. -/
def seqCounterBlockVal {n : Nat} (inputVal : DimacsValuation)
    (initialTop : Nat) (x : Fin n → Bool)
    (ids : List ((Nat × Nat) × Nat)) : DimacsValuation := fun id =>
  if id ≤ initialTop then inputVal id else seqCounterTableVal x ids id

theorem seqCounterBlockVal_input {n : Nat} (inputVal : DimacsValuation)
    (initialTop : Nat) (x : Fin n → Bool)
    (ids : List ((Nat × Nat) × Nat)) {id : Nat}
    (hid : id ≤ initialTop) :
    seqCounterBlockVal inputVal initialTop x ids id = inputVal id := by
  simp [seqCounterBlockVal, hid]

theorem seqCounterBlockVal_aux {n : Nat} (inputVal : DimacsValuation)
    {initialTop : Nat} (x : Fin n → Bool) {st : SeqCounterGenState}
    (hinv : SeqCounterAllocationInvariant initialTop st)
    {key : Nat × Nat} {id : Nat} (hmem : (key, id) ∈ st.ids) :
    seqCounterBlockVal inputVal initialTop x st.ids id =
      seqCounterWitness x (key.2 + key.1) key.1 := by
  have hbound := hinv.id_bounds (key, id) hmem
  rw [seqCounterBlockVal]
  simp only [not_le.mpr hbound.1]
  exact seqCounterTableVal_of_mem x hinv.ids_nodup hmem

/-- DIMACS variables are positive integers; a negative integer denotes the
Boolean negation of the variable with the same absolute identifier. -/
def dimacsLitValue (val : DimacsValuation) (lit : Int) : Bool :=
  if 0 < lit then val lit.natAbs else !(val lit.natAbs)

theorem dimacsLitValue_block_of_natAbs_le {n : Nat}
    (inputVal : DimacsValuation) (initialTop : Nat) (x : Fin n → Bool)
    (ids : List ((Nat × Nat) × Nat)) {lit : Int}
    (hlit : lit.natAbs ≤ initialTop) :
    dimacsLitValue (seqCounterBlockVal inputVal initialTop x ids) lit =
      dimacsLitValue inputVal lit := by
  simp [dimacsLitValue, seqCounterBlockVal, hlit]

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

/-! The generator's at-least block passes negated input literals to the same
at-most core.  The following variants therefore allow the input literal
itself to have either sign. -/

theorem dimacs_seqCounter_base_clause_satisfied_signed {n : Nat}
    (x : Fin n → Bool) (val : DimacsValuation) (j : Nat) (hj : j < n)
    (inputLit : Int) (auxId : Nat) (hinput : inputLit ≠ 0)
    (haux : 0 < auxId)
    (hinputVal : dimacsLitValue val inputLit = x ⟨j, hj⟩)
    (hauxVal : val auxId = seqCounterWitness x j 0) :
    dimacsClauseSatisfied val [-inputLit, (auxId : Int)] := by
  by_cases hx : x ⟨j, hj⟩ = true
  · refine ⟨(auxId : Int), by simp, ?_⟩
    rw [dimacsLitValue_natCast val haux, hauxVal,
      seqCounterKnuth_base x j hj hx]
  · refine ⟨-inputLit, by simp, ?_⟩
    rw [dimacsLitValue_neg val hinput, hinputVal]
    cases hval : x ⟨j, hj⟩ <;> simp_all

theorem dimacs_seqCounter_diagonal_clause_satisfied_signed {n : Nat}
    (x : Fin n → Bool) (val : DimacsValuation) (k j : Nat)
    (hidx : j + k + 1 < n) (inputLit : Int) (leftId rightId : Nat)
    (hinput : inputLit ≠ 0) (hleft : 0 < leftId) (hright : 0 < rightId)
    (hinputVal : dimacsLitValue val inputLit = x ⟨j + k + 1, hidx⟩)
    (hleftVal : val leftId = seqCounterWitness x (j + k) k)
    (hrightVal : val rightId = seqCounterWitness x (j + (k + 1)) (k + 1)) :
    dimacsClauseSatisfied val [-inputLit, -(leftId : Int), (rightId : Int)] := by
  by_cases hx : x ⟨j + k + 1, hidx⟩ = true
  · by_cases hs : seqCounterWitness x (j + k) k = true
    · refine ⟨(rightId : Int), by simp, ?_⟩
      rw [dimacsLitValue_natCast val hright, hrightVal,
        seqCounterKnuth_diagonal x k j hidx hx hs]
    · refine ⟨-(leftId : Int), by simp, ?_⟩
      rw [dimacsLitValue_neg val (by exact_mod_cast hleft.ne'),
        dimacsLitValue_natCast val hleft, hleftVal]
      cases hval : seqCounterWitness x (j + k) k <;> simp_all
  · refine ⟨-inputLit, by simp, ?_⟩
    rw [dimacsLitValue_neg val hinput, hinputVal]
    cases hval : x ⟨j + k + 1, hidx⟩ <;> simp_all

theorem dimacs_seqCounter_overflow_clause_satisfied_signed {n : Nat}
    (x : Fin n → Bool) (val : DimacsValuation) (t j : Nat)
    (ht : 0 < t) (hidx : j + t < n) (htotal : seqPrefixTrue x n ≤ t)
    (inputLit : Int) (auxId : Nat) (hinput : inputLit ≠ 0)
    (haux : 0 < auxId)
    (hinputVal : dimacsLitValue val inputLit = x ⟨j + t, hidx⟩)
    (hauxVal : val auxId = seqCounterWitness x (j + (t - 1)) (t - 1)) :
    dimacsClauseSatisfied val [-inputLit, -(auxId : Int)] := by
  by_cases hx : x ⟨j + t, hidx⟩ = true
  · refine ⟨-(auxId : Int), by simp, ?_⟩
    rw [dimacsLitValue_neg val (by exact_mod_cast haux.ne'),
      dimacsLitValue_natCast val haux, hauxVal,
      seqCounterKnuth_no_overflow x t j ht hidx htotal hx]
    rfl
  · refine ⟨-inputLit, by simp, ?_⟩
    rw [dimacsLitValue_neg val hinput, hinputVal]
    cases hval : x ⟨j + t, hidx⟩ <;> simp_all

end Erdos85
