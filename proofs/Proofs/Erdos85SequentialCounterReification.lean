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

/-- One inner-loop iteration preserves allocation integrity. -/
theorem seqCounterAllocationInvariant_kStep
    {initialTop : Nat} {st : SeqCounterGenState}
    (hinv : SeqCounterAllocationInvariant initialTop st)
    (vars : Array Int) (t j k : Nat) :
    SeqCounterAllocationInvariant initialTop
      (seqCounterAtMostKStep vars t j k st) := by
  simp only [seqCounterAtMostKStep]
  generalize h₁ : seqCounterMkYvar (k, j) st = out₁
  rcases out₁ with ⟨skj, st₁⟩
  have hinv₁ : SeqCounterAllocationInvariant initialTop st₁ := by
    have h := seqCounterAllocationInvariant_mkYvar hinv (k, j)
    rw [h₁] at h
    exact h
  by_cases hj : j < vars.size - t - 1
  · simp only [hj, ↓reduceIte]
    generalize h₂ : seqCounterMkYvar (k, j + 1) st₁ = out₂
    rcases out₂ with ⟨skj1, st₂⟩
    have hinv₂ : SeqCounterAllocationInvariant initialTop st₂ := by
      have h := seqCounterAllocationInvariant_mkYvar hinv₁ (k, j + 1)
      rw [h₂] at h
      exact h
    let st₃ := (seqCounterEmit [-(skj : Int), (skj1 : Int)] st₂).2
    have hinv₃ : SeqCounterAllocationInvariant initialTop st₃ :=
      seqCounterAllocationInvariant_emit hinv₂ _
    generalize h₄ : seqCounterMkYvar (k + 1, j) st₃ = out₄
    rcases out₄ with ⟨sk1j, st₄⟩
    have hinv₄ : SeqCounterAllocationInvariant initialTop st₄ := by
      have h := seqCounterAllocationInvariant_mkYvar hinv₃ (k + 1, j)
      rw [h₄] at h
      exact h
    exact seqCounterAllocationInvariant_emit hinv₄ _
  · simp only [hj, ↓reduceIte]
    generalize h₂ : seqCounterMkYvar (k + 1, j) st₁ = out₂
    rcases out₂ with ⟨sk1j, st₂⟩
    have hinv₂ : SeqCounterAllocationInvariant initialTop st₂ := by
      have h := seqCounterAllocationInvariant_mkYvar hinv₁ (k + 1, j)
      rw [h₂] at h
      exact h
    exact seqCounterAllocationInvariant_emit hinv₂ _

/-- The structurally recursive inner loop preserves allocation integrity. -/
theorem seqCounterAllocationInvariant_kLoop
    {initialTop : Nat} {st : SeqCounterGenState}
    (hinv : SeqCounterAllocationInvariant initialTop st)
    (vars : Array Int) (t j fuel k : Nat) :
    SeqCounterAllocationInvariant initialTop
      (seqCounterAtMostKLoop vars t j fuel k st) := by
  induction fuel generalizing k st with
  | zero => exact hinv
  | succ fuel ih =>
      simp only [seqCounterAtMostKLoop]
      apply ih
      exact seqCounterAllocationInvariant_kStep hinv vars t j k

/-- The base-clause prefix preserves allocation integrity. -/
theorem seqCounterAllocationInvariant_jPrefix
    {initialTop : Nat} {st : SeqCounterGenState}
    (hinv : SeqCounterAllocationInvariant initialTop st)
    (vars : Array Int) (j : Nat) :
    SeqCounterAllocationInvariant initialTop
      (seqCounterAtMostJPrefix vars j st) := by
  simp only [seqCounterAtMostJPrefix]
  generalize h₁ : seqCounterMkYvar (0, j) st = out₁
  rcases out₁ with ⟨s0j, st₁⟩
  have hinv₁ : SeqCounterAllocationInvariant initialTop st₁ := by
    have h := seqCounterAllocationInvariant_mkYvar hinv (0, j)
    rw [h₁] at h
    exact h
  exact seqCounterAllocationInvariant_emit hinv₁ _

/-- The terminal horizontal/overflow suffix preserves allocation integrity. -/
theorem seqCounterAllocationInvariant_jFinish
    {initialTop : Nat} {st : SeqCounterGenState}
    (hinv : SeqCounterAllocationInvariant initialTop st)
    (vars : Array Int) (t j : Nat) :
    SeqCounterAllocationInvariant initialTop
      (seqCounterAtMostJFinish vars t j st) := by
  simp only [seqCounterAtMostJFinish]
  generalize h₁ : seqCounterMkYvar (t - 1, j) st = out₁
  rcases out₁ with ⟨stj, st₁⟩
  have hinv₁ : SeqCounterAllocationInvariant initialTop st₁ := by
    have h := seqCounterAllocationInvariant_mkYvar hinv (t - 1, j)
    rw [h₁] at h
    exact h
  by_cases hj : j < vars.size - t - 1
  · simp only [hj, ↓reduceIte]
    generalize h₂ : seqCounterMkYvar (t - 1, j + 1) st₁ = out₂
    rcases out₂ with ⟨stj1, st₂⟩
    have hinv₂ : SeqCounterAllocationInvariant initialTop st₂ := by
      have h := seqCounterAllocationInvariant_mkYvar hinv₁ (t - 1, j + 1)
      rw [h₂] at h
      exact h
    let st₃ := (seqCounterEmit [-(stj : Int), (stj1 : Int)] st₂).2
    have hinv₃ : SeqCounterAllocationInvariant initialTop st₃ :=
      seqCounterAllocationInvariant_emit hinv₂ _
    exact seqCounterAllocationInvariant_emit hinv₃ _
  · simp only [hj, ↓reduceIte]
    exact seqCounterAllocationInvariant_emit hinv₁ _

/-- One outer-loop iteration preserves allocation integrity. -/
theorem seqCounterAllocationInvariant_jStep
    {initialTop : Nat} {st : SeqCounterGenState}
    (hinv : SeqCounterAllocationInvariant initialTop st)
    (vars : Array Int) (t j : Nat) :
    SeqCounterAllocationInvariant initialTop
      (seqCounterAtMostJStep vars t j st) := by
  apply seqCounterAllocationInvariant_jFinish
  apply seqCounterAllocationInvariant_kLoop
  exact seqCounterAllocationInvariant_jPrefix hinv vars j

/-- The structurally recursive outer loop preserves allocation integrity. -/
theorem seqCounterAllocationInvariant_jLoop
    {initialTop : Nat} {st : SeqCounterGenState}
    (hinv : SeqCounterAllocationInvariant initialTop st)
    (vars : Array Int) (t fuel j : Nat) :
    SeqCounterAllocationInvariant initialTop
      (seqCounterAtMostJLoop vars t fuel j st) := by
  induction fuel generalizing j st with
  | zero => exact hinv
  | succ fuel ih =>
      simp only [seqCounterAtMostJLoop]
      apply ih
      exact seqCounterAllocationInvariant_jStep hinv vars t j

/-- The exact PySAT at-most generator always has a conflict-free allocation
table above its supplied initial top. -/
theorem seqCounterAtMostCore_allocationInvariant
    (top : Nat) (vars : Array Int) (t : Nat) :
    SeqCounterAllocationInvariant top (seqCounterAtMostCore top vars t) := by
  unfold seqCounterAtMostCore
  split
  · apply seqCounterAllocationInvariant_jLoop
    exact seqCounterAllocationInvariant_initial top
  · exact seqCounterAllocationInvariant_initial top

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

theorem seqCounterIdsExtend_kStep (vars : Array Int) (t j k : Nat)
    (st : SeqCounterGenState) :
    SeqCounterIdsExtend st (seqCounterAtMostKStep vars t j k st) := by
  simp only [seqCounterAtMostKStep]
  generalize h₁ : seqCounterMkYvar (k, j) st = out₁
  rcases out₁ with ⟨skj, st₁⟩
  have hext₁ : SeqCounterIdsExtend st st₁ := by
    have h := seqCounterIdsExtend_mkYvar (k, j) st
    rw [h₁] at h
    exact h
  by_cases hj : j < vars.size - t - 1
  · simp only [hj, ↓reduceIte]
    generalize h₂ : seqCounterMkYvar (k, j + 1) st₁ = out₂
    rcases out₂ with ⟨skj1, st₂⟩
    have hext₂ : SeqCounterIdsExtend st₁ st₂ := by
      have h := seqCounterIdsExtend_mkYvar (k, j + 1) st₁
      rw [h₂] at h
      exact h
    let st₃ := (seqCounterEmit [-(skj : Int), (skj1 : Int)] st₂).2
    have hext₃ : SeqCounterIdsExtend st₂ st₃ :=
      seqCounterIdsExtend_emit _ st₂
    generalize h₄ : seqCounterMkYvar (k + 1, j) st₃ = out₄
    rcases out₄ with ⟨sk1j, st₄⟩
    have hext₄ : SeqCounterIdsExtend st₃ st₄ := by
      have h := seqCounterIdsExtend_mkYvar (k + 1, j) st₃
      rw [h₄] at h
      exact h
    have hext₅ : SeqCounterIdsExtend st₄
        (seqCounterEmit
          [-(vars.getD (j + k + 1) 0), -(skj : Int), (sk1j : Int)] st₄).2 :=
      seqCounterIdsExtend_emit _ st₄
    exact hext₁.trans (hext₂.trans (hext₃.trans (hext₄.trans hext₅)))
  · simp only [hj, ↓reduceIte]
    generalize h₂ : seqCounterMkYvar (k + 1, j) st₁ = out₂
    rcases out₂ with ⟨sk1j, st₂⟩
    have hext₂ : SeqCounterIdsExtend st₁ st₂ := by
      have h := seqCounterIdsExtend_mkYvar (k + 1, j) st₁
      rw [h₂] at h
      exact h
    have hext₃ : SeqCounterIdsExtend st₂
        (seqCounterEmit
          [-(vars.getD (j + k + 1) 0), -(skj : Int), (sk1j : Int)] st₂).2 :=
      seqCounterIdsExtend_emit _ st₂
    exact hext₁.trans (hext₂.trans hext₃)

theorem seqCounterIdsExtend_kLoop (vars : Array Int) (t j fuel k : Nat)
    (st : SeqCounterGenState) :
    SeqCounterIdsExtend st (seqCounterAtMostKLoop vars t j fuel k st) := by
  induction fuel generalizing k st with
  | zero => exact SeqCounterIdsExtend.refl st
  | succ fuel ih =>
      simp only [seqCounterAtMostKLoop]
      exact (seqCounterIdsExtend_kStep vars t j k st).trans (ih _ _)

theorem seqCounterIdsExtend_jPrefix (vars : Array Int) (j : Nat)
    (st : SeqCounterGenState) :
    SeqCounterIdsExtend st (seqCounterAtMostJPrefix vars j st) := by
  simp only [seqCounterAtMostJPrefix]
  generalize h₁ : seqCounterMkYvar (0, j) st = out₁
  rcases out₁ with ⟨s0j, st₁⟩
  have hext₁ : SeqCounterIdsExtend st st₁ := by
    have h := seqCounterIdsExtend_mkYvar (0, j) st
    rw [h₁] at h
    exact h
  exact hext₁.trans (seqCounterIdsExtend_emit _ st₁)

theorem seqCounterIdsExtend_jFinish (vars : Array Int) (t j : Nat)
    (st : SeqCounterGenState) :
    SeqCounterIdsExtend st (seqCounterAtMostJFinish vars t j st) := by
  simp only [seqCounterAtMostJFinish]
  generalize h₁ : seqCounterMkYvar (t - 1, j) st = out₁
  rcases out₁ with ⟨stj, st₁⟩
  have hext₁ : SeqCounterIdsExtend st st₁ := by
    have h := seqCounterIdsExtend_mkYvar (t - 1, j) st
    rw [h₁] at h
    exact h
  by_cases hj : j < vars.size - t - 1
  · simp only [hj, ↓reduceIte]
    generalize h₂ : seqCounterMkYvar (t - 1, j + 1) st₁ = out₂
    rcases out₂ with ⟨stj1, st₂⟩
    have hext₂ : SeqCounterIdsExtend st₁ st₂ := by
      have h := seqCounterIdsExtend_mkYvar (t - 1, j + 1) st₁
      rw [h₂] at h
      exact h
    let st₃ := (seqCounterEmit [-(stj : Int), (stj1 : Int)] st₂).2
    have hext₃ : SeqCounterIdsExtend st₂ st₃ :=
      seqCounterIdsExtend_emit _ st₂
    have hext₄ : SeqCounterIdsExtend st₃
        (seqCounterEmit [-(vars.getD (j + t) 0), -(stj : Int)] st₃).2 :=
      seqCounterIdsExtend_emit _ st₃
    exact hext₁.trans (hext₂.trans (hext₃.trans hext₄))
  · simp only [hj, ↓reduceIte]
    exact hext₁.trans (seqCounterIdsExtend_emit _ st₁)

theorem seqCounterIdsExtend_jStep (vars : Array Int) (t j : Nat)
    (st : SeqCounterGenState) :
    SeqCounterIdsExtend st (seqCounterAtMostJStep vars t j st) := by
  exact (seqCounterIdsExtend_jPrefix vars j st).trans <|
    (seqCounterIdsExtend_kLoop vars t j (t - 1) 0 _).trans <|
      seqCounterIdsExtend_jFinish vars t j _

theorem seqCounterIdsExtend_jLoop (vars : Array Int) (t fuel j : Nat)
    (st : SeqCounterGenState) :
    SeqCounterIdsExtend st (seqCounterAtMostJLoop vars t fuel j st) := by
  induction fuel generalizing j st with
  | zero => exact SeqCounterIdsExtend.refl st
  | succ fuel ih =>
      simp only [seqCounterAtMostJLoop]
      exact (seqCounterIdsExtend_jStep vars t j st).trans (ih _ _)

theorem seqCounterAtMostCore_idsExtend
    (top : Nat) (vars : Array Int) (t : Nat) :
    SeqCounterIdsExtend ({ top := top } : SeqCounterGenState)
      (seqCounterAtMostCore top vars t) := by
  unfold seqCounterAtMostCore
  split
  · exact seqCounterIdsExtend_jLoop vars t (vars.size - t) 0 _
  · exact SeqCounterIdsExtend.refl _

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

def dimacsFormulaSatisfied (val : DimacsValuation)
    (clauses : Array DimacsClause) : Prop :=
  ∀ clause ∈ clauses, dimacsClauseSatisfied val clause

def dimacsClauseBounded (top : Nat) (clause : DimacsClause) : Prop :=
  ∀ lit ∈ clause, lit.natAbs ≤ top

def dimacsFormulaBounded (top : Nat) (clauses : Array DimacsClause) : Prop :=
  ∀ clause ∈ clauses, dimacsClauseBounded top clause

theorem dimacsLitValue_eq_of_agree (val₁ val₂ : DimacsValuation)
    {lit : Int} (hagree : val₁ lit.natAbs = val₂ lit.natAbs) :
    dimacsLitValue val₁ lit = dimacsLitValue val₂ lit := by
  simp only [dimacsLitValue]
  split <;> simp [hagree]

theorem dimacsClauseSatisfied_of_agree {val₁ val₂ : DimacsValuation}
    {clause : DimacsClause}
    (hclause : dimacsClauseSatisfied val₁ clause)
    (hagree : ∀ lit ∈ clause, val₁ lit.natAbs = val₂ lit.natAbs) :
    dimacsClauseSatisfied val₂ clause := by
  obtain ⟨lit, hlit, htrue⟩ := hclause
  exact ⟨lit, hlit, by
    rw [← dimacsLitValue_eq_of_agree val₁ val₂ (hagree lit hlit)]
    exact htrue⟩

theorem dimacsFormulaSatisfied_of_bounded_agree
    {val₁ val₂ : DimacsValuation} {top : Nat} {clauses : Array DimacsClause}
    (hsat : dimacsFormulaSatisfied val₁ clauses)
    (hbounded : dimacsFormulaBounded top clauses)
    (hagree : ∀ id, id ≤ top → val₁ id = val₂ id) :
    dimacsFormulaSatisfied val₂ clauses := by
  intro clause hclause
  apply dimacsClauseSatisfied_of_agree (hsat clause hclause)
  intro lit hlit
  exact hagree lit.natAbs (hbounded clause hclause lit hlit)

theorem dimacsFormulaBounded_empty (top : Nat) :
    dimacsFormulaBounded top #[] := by
  intro clause hclause
  simp at hclause

theorem dimacsFormulaBounded_mono {a b : Nat} {clauses : Array DimacsClause}
    (hab : a ≤ b) (hbounded : dimacsFormulaBounded a clauses) :
    dimacsFormulaBounded b clauses := by
  intro clause hclause lit hlit
  exact (hbounded clause hclause lit hlit).trans hab

theorem dimacsFormulaBounded_emit {top : Nat} {st : SeqCounterGenState}
    {clause : DimacsClause}
    (hprevious : dimacsFormulaBounded top st.clauses)
    (hclause : dimacsClauseBounded top clause) :
    dimacsFormulaBounded top (seqCounterEmit clause st).2.clauses := by
  intro candidate hcandidate
  change candidate ∈ st.clauses.push clause at hcandidate
  simp only [Array.mem_push] at hcandidate
  rcases hcandidate with hold | rfl
  · exact hprevious candidate hold
  · exact hclause

theorem dimacsFormulaBounded_mkYvar {top : Nat} {st : SeqCounterGenState}
    (key : Nat × Nat) (hprevious : dimacsFormulaBounded top st.clauses) :
    dimacsFormulaBounded top (seqCounterMkYvar key st).2.clauses := by
  rw [seqCounterMkYvar_clauses]
  exact hprevious

theorem dimacsSeqCounter_base_bounded
    {initialTop : Nat} {final : SeqCounterGenState}
    (hinv : SeqCounterAllocationInvariant initialTop final)
    {inputLit : Int} (hinput : inputLit.natAbs ≤ initialTop)
    {key : Nat × Nat} {auxId : Nat} (haux : (key, auxId) ∈ final.ids) :
    dimacsClauseBounded final.top [-inputLit, (auxId : Int)] := by
  intro lit hlit
  simp at hlit
  rcases hlit with rfl | rfl
  · simpa using hinput.trans hinv.top_bound
  · simpa using (hinv.id_bounds (key, auxId) haux).2

theorem dimacsSeqCounter_horizontal_bounded
    {initialTop : Nat} {final : SeqCounterGenState}
    (hinv : SeqCounterAllocationInvariant initialTop final)
    {leftKey rightKey : Nat × Nat} {leftId rightId : Nat}
    (hleft : (leftKey, leftId) ∈ final.ids)
    (hright : (rightKey, rightId) ∈ final.ids) :
    dimacsClauseBounded final.top [-(leftId : Int), (rightId : Int)] := by
  intro lit hlit
  simp at hlit
  rcases hlit with rfl | rfl
  · simpa using (hinv.id_bounds (leftKey, leftId) hleft).2
  · simpa using (hinv.id_bounds (rightKey, rightId) hright).2

theorem dimacsSeqCounter_diagonal_bounded
    {initialTop : Nat} {final : SeqCounterGenState}
    (hinv : SeqCounterAllocationInvariant initialTop final)
    {inputLit : Int} (hinput : inputLit.natAbs ≤ initialTop)
    {leftKey rightKey : Nat × Nat} {leftId rightId : Nat}
    (hleft : (leftKey, leftId) ∈ final.ids)
    (hright : (rightKey, rightId) ∈ final.ids) :
    dimacsClauseBounded final.top
      [-inputLit, -(leftId : Int), (rightId : Int)] := by
  intro lit hlit
  simp at hlit
  rcases hlit with rfl | rfl | rfl
  · simpa using hinput.trans hinv.top_bound
  · simpa using (hinv.id_bounds (leftKey, leftId) hleft).2
  · simpa using (hinv.id_bounds (rightKey, rightId) hright).2

theorem dimacsSeqCounter_overflow_bounded
    {initialTop : Nat} {final : SeqCounterGenState}
    (hinv : SeqCounterAllocationInvariant initialTop final)
    {inputLit : Int} (hinput : inputLit.natAbs ≤ initialTop)
    {key : Nat × Nat} {auxId : Nat} (haux : (key, auxId) ∈ final.ids) :
    dimacsClauseBounded final.top [-inputLit, -(auxId : Int)] := by
  intro lit hlit
  simp at hlit
  rcases hlit with rfl | rfl
  · simpa using hinput.trans hinv.top_bound
  · simpa using (hinv.id_bounds (key, auxId) haux).2

/-- The signed input-literal array reifies a Boolean row below the block's
initial auxiliary-variable boundary. -/
structure SeqCounterInputReifies {n : Nat} (inputVal : DimacsValuation)
    (initialTop : Nat) (vars : Array Int) (x : Fin n → Bool) : Prop where
  size_eq : vars.size = n
  nonzero : ∀ i, ∀ _hi : i < n, vars.getD i 0 ≠ 0
  bounded : ∀ i, ∀ _hi : i < n, (vars.getD i 0).natAbs ≤ initialTop
  value : ∀ i, ∀ hi : i < n,
    dimacsLitValue inputVal (vars.getD i 0) = x ⟨i, hi⟩

theorem SeqCounterInputReifies.block_value {n : Nat}
    {inputVal : DimacsValuation} {initialTop : Nat} {vars : Array Int}
    {x : Fin n → Bool} (h : SeqCounterInputReifies inputVal initialTop vars x)
    (ids : List ((Nat × Nat) × Nat)) (i : Nat) (hi : i < n) :
    dimacsLitValue (seqCounterBlockVal inputVal initialTop x ids)
      (vars.getD i 0) = x ⟨i, hi⟩ := by
  rw [dimacsLitValue_block_of_natAbs_le inputVal initialTop x ids
    (h.bounded i hi)]
  exact h.value i hi

theorem dimacsFormulaSatisfied_empty (val : DimacsValuation) :
    dimacsFormulaSatisfied val #[] := by
  intro clause hclause
  simp at hclause

theorem dimacsFormulaSatisfied_emit {val : DimacsValuation}
    {st : SeqCounterGenState} {clause : DimacsClause}
    (hprevious : dimacsFormulaSatisfied val st.clauses)
    (hclause : dimacsClauseSatisfied val clause) :
    dimacsFormulaSatisfied val (seqCounterEmit clause st).2.clauses := by
  intro candidate hcandidate
  change candidate ∈ st.clauses.push clause at hcandidate
  simp only [Array.mem_push] at hcandidate
  rcases hcandidate with hold | rfl
  · exact hprevious candidate hold
  · exact hclause

theorem dimacsFormulaSatisfied_mkYvar {val : DimacsValuation}
    {st : SeqCounterGenState} (key : Nat × Nat)
    (hprevious : dimacsFormulaSatisfied val st.clauses) :
    dimacsFormulaSatisfied val (seqCounterMkYvar key st).2.clauses := by
  rw [seqCounterMkYvar_clauses]
  exact hprevious

theorem seqCounterAux_positive_of_mem
    {initialTop : Nat} {st : SeqCounterGenState}
    (hinv : SeqCounterAllocationInvariant initialTop st)
    {key : Nat × Nat} {id : Nat} (hmem : (key, id) ∈ st.ids) :
    0 < id := by
  have hbound := (hinv.id_bounds (key, id) hmem).1
  omega

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

/-! ## Soundness of the recursive generator steps -/

/-- One inner generator step preserves satisfaction under any eventual final
table extending the step's output. -/
theorem seqCounterAtMostKStep_formulaSatisfied
    (inputVal : DimacsValuation) (initialTop : Nat) (vars : Array Int)
    (x : Fin vars.size → Bool) (hinput :
      SeqCounterInputReifies inputVal initialTop vars x)
    (t j k : Nat) (hk : k < t - 1) (hj : j < vars.size - t)
    (st final : SeqCounterGenState)
    (hfinalInv : SeqCounterAllocationInvariant initialTop final)
    (hfuture : SeqCounterIdsExtend
      (seqCounterAtMostKStep vars t j k st) final)
    (hprevious : dimacsFormulaSatisfied
      (seqCounterBlockVal inputVal initialTop x final.ids) st.clauses) :
    dimacsFormulaSatisfied
      (seqCounterBlockVal inputVal initialTop x final.ids)
      (seqCounterAtMostKStep vars t j k st).clauses := by
  let val := seqCounterBlockVal inputVal initialTop x final.ids
  simp only [seqCounterAtMostKStep] at hfuture ⊢
  generalize h₁ : seqCounterMkYvar (k, j) st = out₁ at hfuture ⊢
  rcases out₁ with ⟨skj, st₁⟩
  have hmem₁ : ((k, j), skj) ∈ st₁.ids := by
    have h := seqCounterMkYvar_mem (k, j) st
    rw [h₁] at h
    exact h
  have hsat₁ : dimacsFormulaSatisfied val st₁.clauses := by
    have h := dimacsFormulaSatisfied_mkYvar (k, j) hprevious
    rw [h₁] at h
    exact h
  by_cases hhorizontal : j < vars.size - t - 1
  · simp only [hhorizontal, ↓reduceIte] at hfuture ⊢
    generalize h₂ : seqCounterMkYvar (k, j + 1) st₁ = out₂ at hfuture ⊢
    rcases out₂ with ⟨skj1, st₂⟩
    have hext₁₂ : SeqCounterIdsExtend st₁ st₂ := by
      have h := seqCounterIdsExtend_mkYvar (k, j + 1) st₁
      rw [h₂] at h
      exact h
    have hmem₂ : ((k, j + 1), skj1) ∈ st₂.ids := by
      have h := seqCounterMkYvar_mem (k, j + 1) st₁
      rw [h₂] at h
      exact h
    have hsat₂ : dimacsFormulaSatisfied val st₂.clauses := by
      have h := dimacsFormulaSatisfied_mkYvar (k, j + 1) hsat₁
      rw [h₂] at h
      exact h
    let horizontal := [-(skj : Int), (skj1 : Int)]
    let st₃ := (seqCounterEmit horizontal st₂).2
    have hext₂₃ : SeqCounterIdsExtend st₂ st₃ :=
      seqCounterIdsExtend_emit horizontal st₂
    generalize h₄ : seqCounterMkYvar (k + 1, j) st₃ = out₄ at hfuture ⊢
    rcases out₄ with ⟨sk1j, st₄⟩
    have hext₃₄ : SeqCounterIdsExtend st₃ st₄ := by
      have h := seqCounterIdsExtend_mkYvar (k + 1, j) st₃
      rw [h₄] at h
      exact h
    let diagonal :=
      [-(vars.getD (j + k + 1) 0), -(skj : Int), (sk1j : Int)]
    let stepOut := (seqCounterEmit diagonal st₄).2
    have hext₄o : SeqCounterIdsExtend st₄ stepOut :=
      seqCounterIdsExtend_emit diagonal st₄
    have hext₁f : SeqCounterIdsExtend st₁ final :=
      hext₁₂.trans (hext₂₃.trans (hext₃₄.trans (hext₄o.trans hfuture)))
    have hext₂f : SeqCounterIdsExtend st₂ final :=
      hext₂₃.trans (hext₃₄.trans (hext₄o.trans hfuture))
    have hext₃f : SeqCounterIdsExtend st₃ final :=
      hext₃₄.trans (hext₄o.trans hfuture)
    have hext₄f : SeqCounterIdsExtend st₄ final := hext₄o.trans hfuture
    have hmem₁f := hext₁f _ hmem₁
    have hmem₂f := hext₂f _ hmem₂
    have hhorizontalSat : dimacsClauseSatisfied val horizontal := by
      apply dimacs_seqCounter_horizontal_clause_satisfied x val k j
      · omega
      · exact seqCounterAux_positive_of_mem hfinalInv hmem₁f
      · exact seqCounterAux_positive_of_mem hfinalInv hmem₂f
      · simpa [val] using seqCounterBlockVal_aux inputVal x hfinalInv hmem₁f
      · simpa [val, Nat.add_assoc] using
          seqCounterBlockVal_aux inputVal x hfinalInv hmem₂f
    have hsat₃ : dimacsFormulaSatisfied val st₃.clauses :=
      dimacsFormulaSatisfied_emit hsat₂ hhorizontalSat
    have hmem₄ : ((k + 1, j), sk1j) ∈ st₄.ids := by
      have h := seqCounterMkYvar_mem (k + 1, j) st₃
      rw [h₄] at h
      exact h
    have hmem₄f := hext₄f _ hmem₄
    have hsat₄ : dimacsFormulaSatisfied val st₄.clauses := by
      have h := dimacsFormulaSatisfied_mkYvar (k + 1, j) hsat₃
      rw [h₄] at h
      exact h
    have hdiagSat : dimacsClauseSatisfied val diagonal := by
      have htSize : t ≤ vars.size := by omega
      have hidx : j + k + 1 < vars.size := by
        have hsub : vars.size - t + t = vars.size := Nat.sub_add_cancel htSize
        omega
      have hinputValue : dimacsLitValue val
          (vars.getD (j + k + 1) 0) = x ⟨j + k + 1, hidx⟩ := by
        simpa [val] using hinput.block_value final.ids _ hidx
      have hleftValue : val skj = seqCounterWitness x (j + k) k := by
        simpa [val] using seqCounterBlockVal_aux inputVal x hfinalInv hmem₁f
      have hrightValue : val sk1j =
          seqCounterWitness x (j + (k + 1)) (k + 1) := by
        simpa [val, Nat.add_assoc] using
          seqCounterBlockVal_aux inputVal x hfinalInv hmem₄f
      exact dimacs_seqCounter_diagonal_clause_satisfied_signed x val k j hidx
        (vars.getD (j + k + 1) 0) skj sk1j
        (hinput.nonzero _ hidx)
        (seqCounterAux_positive_of_mem hfinalInv hmem₁f)
        (seqCounterAux_positive_of_mem hfinalInv hmem₄f)
        hinputValue hleftValue hrightValue
    exact dimacsFormulaSatisfied_emit hsat₄ hdiagSat
  · simp only [hhorizontal, ↓reduceIte] at hfuture ⊢
    generalize h₂ : seqCounterMkYvar (k + 1, j) st₁ = out₂ at hfuture ⊢
    rcases out₂ with ⟨sk1j, st₂⟩
    have hext₁₂ : SeqCounterIdsExtend st₁ st₂ := by
      have h := seqCounterIdsExtend_mkYvar (k + 1, j) st₁
      rw [h₂] at h
      exact h
    let diagonal :=
      [-(vars.getD (j + k + 1) 0), -(skj : Int), (sk1j : Int)]
    let stepOut := (seqCounterEmit diagonal st₂).2
    have hext₂o : SeqCounterIdsExtend st₂ stepOut :=
      seqCounterIdsExtend_emit diagonal st₂
    have hext₁f : SeqCounterIdsExtend st₁ final :=
      hext₁₂.trans (hext₂o.trans hfuture)
    have hext₂f : SeqCounterIdsExtend st₂ final := hext₂o.trans hfuture
    have hmem₁f := hext₁f _ hmem₁
    have hmem₂ : ((k + 1, j), sk1j) ∈ st₂.ids := by
      have h := seqCounterMkYvar_mem (k + 1, j) st₁
      rw [h₂] at h
      exact h
    have hmem₂f := hext₂f _ hmem₂
    have hsat₂ : dimacsFormulaSatisfied val st₂.clauses := by
      have h := dimacsFormulaSatisfied_mkYvar (k + 1, j) hsat₁
      rw [h₂] at h
      exact h
    have hdiagSat : dimacsClauseSatisfied val diagonal := by
      have htSize : t ≤ vars.size := by omega
      have hidx : j + k + 1 < vars.size := by
        have hsub : vars.size - t + t = vars.size := Nat.sub_add_cancel htSize
        omega
      have hinputValue : dimacsLitValue val
          (vars.getD (j + k + 1) 0) = x ⟨j + k + 1, hidx⟩ := by
        simpa [val] using hinput.block_value final.ids _ hidx
      have hleftValue : val skj = seqCounterWitness x (j + k) k := by
        simpa [val] using seqCounterBlockVal_aux inputVal x hfinalInv hmem₁f
      have hrightValue : val sk1j =
          seqCounterWitness x (j + (k + 1)) (k + 1) := by
        simpa [val, Nat.add_assoc] using
          seqCounterBlockVal_aux inputVal x hfinalInv hmem₂f
      exact dimacs_seqCounter_diagonal_clause_satisfied_signed x val k j hidx
        (vars.getD (j + k + 1) 0) skj sk1j
        (hinput.nonzero _ hidx)
        (seqCounterAux_positive_of_mem hfinalInv hmem₁f)
        (seqCounterAux_positive_of_mem hfinalInv hmem₂f)
        hinputValue hleftValue hrightValue
    exact dimacsFormulaSatisfied_emit hsat₂ hdiagSat

/-- Every inner-loop iteration preserves satisfaction under the eventual
final table. -/
theorem seqCounterAtMostKLoop_formulaSatisfied
    (inputVal : DimacsValuation) (initialTop : Nat) (vars : Array Int)
    (x : Fin vars.size → Bool)
    (hinput : SeqCounterInputReifies inputVal initialTop vars x)
    (t j fuel k : Nat) (hkfuel : k + fuel ≤ t - 1)
    (hj : j < vars.size - t) (st final : SeqCounterGenState)
    (hfinalInv : SeqCounterAllocationInvariant initialTop final)
    (hfuture : SeqCounterIdsExtend
      (seqCounterAtMostKLoop vars t j fuel k st) final)
    (hprevious : dimacsFormulaSatisfied
      (seqCounterBlockVal inputVal initialTop x final.ids) st.clauses) :
    dimacsFormulaSatisfied
      (seqCounterBlockVal inputVal initialTop x final.ids)
      (seqCounterAtMostKLoop vars t j fuel k st).clauses := by
  induction fuel generalizing k st with
  | zero => exact hprevious
  | succ fuel ih =>
      simp only [seqCounterAtMostKLoop] at hfuture ⊢
      let stepOut := seqCounterAtMostKStep vars t j k st
      have hext : SeqCounterIdsExtend stepOut final :=
        (seqCounterIdsExtend_kLoop vars t j fuel (k + 1) stepOut).trans hfuture
      have hstep : dimacsFormulaSatisfied
          (seqCounterBlockVal inputVal initialTop x final.ids)
          stepOut.clauses :=
        seqCounterAtMostKStep_formulaSatisfied inputVal initialTop vars x
          hinput t j k (by omega) hj st final hfinalInv hext hprevious
      apply ih
      · omega
      · exact hfuture
      · exact hstep

/-- The base clause at the start of one outer iteration is sound. -/
theorem seqCounterAtMostJPrefix_formulaSatisfied
    (inputVal : DimacsValuation) (initialTop : Nat) (vars : Array Int)
    (x : Fin vars.size → Bool)
    (hinput : SeqCounterInputReifies inputVal initialTop vars x)
    (j : Nat) (hj : j < vars.size) (st final : SeqCounterGenState)
    (hfinalInv : SeqCounterAllocationInvariant initialTop final)
    (hfuture : SeqCounterIdsExtend
      (seqCounterAtMostJPrefix vars j st) final)
    (hprevious : dimacsFormulaSatisfied
      (seqCounterBlockVal inputVal initialTop x final.ids) st.clauses) :
    dimacsFormulaSatisfied
      (seqCounterBlockVal inputVal initialTop x final.ids)
      (seqCounterAtMostJPrefix vars j st).clauses := by
  let val := seqCounterBlockVal inputVal initialTop x final.ids
  simp only [seqCounterAtMostJPrefix] at hfuture ⊢
  generalize h₁ : seqCounterMkYvar (0, j) st = out₁ at hfuture ⊢
  rcases out₁ with ⟨s0j, st₁⟩
  have hmem₁ : ((0, j), s0j) ∈ st₁.ids := by
    have h := seqCounterMkYvar_mem (0, j) st
    rw [h₁] at h
    exact h
  have hext₁o : SeqCounterIdsExtend st₁
      (seqCounterEmit [-(vars.getD j 0), (s0j : Int)] st₁).2 :=
    seqCounterIdsExtend_emit _ st₁
  have hmem₁f := (hext₁o.trans hfuture) _ hmem₁
  have hsat₁ : dimacsFormulaSatisfied val st₁.clauses := by
    have h := dimacsFormulaSatisfied_mkYvar (0, j) hprevious
    rw [h₁] at h
    exact h
  have hinputValue : dimacsLitValue val (vars.getD j 0) = x ⟨j, hj⟩ := by
    simpa [val] using hinput.block_value final.ids j hj
  have hauxValue : val s0j = seqCounterWitness x j 0 := by
    simpa [val] using seqCounterBlockVal_aux inputVal x hfinalInv hmem₁f
  have hbase : dimacsClauseSatisfied val
      [-(vars.getD j 0), (s0j : Int)] :=
    dimacs_seqCounter_base_clause_satisfied_signed x val j hj
      (vars.getD j 0) s0j (hinput.nonzero j hj)
      (seqCounterAux_positive_of_mem hfinalInv hmem₁f)
      hinputValue hauxValue
  exact dimacsFormulaSatisfied_emit hsat₁ hbase

/-- The last horizontal clause and overflow clause ending an outer iteration
are sound. -/
theorem seqCounterAtMostJFinish_formulaSatisfied
    (inputVal : DimacsValuation) (initialTop : Nat) (vars : Array Int)
    (x : Fin vars.size → Bool)
    (hinput : SeqCounterInputReifies inputVal initialTop vars x)
    (t j : Nat) (ht : 0 < t) (hj : j < vars.size - t)
    (htotal : seqPrefixTrue x vars.size ≤ t)
    (st final : SeqCounterGenState)
    (hfinalInv : SeqCounterAllocationInvariant initialTop final)
    (hfuture : SeqCounterIdsExtend
      (seqCounterAtMostJFinish vars t j st) final)
    (hprevious : dimacsFormulaSatisfied
      (seqCounterBlockVal inputVal initialTop x final.ids) st.clauses) :
    dimacsFormulaSatisfied
      (seqCounterBlockVal inputVal initialTop x final.ids)
      (seqCounterAtMostJFinish vars t j st).clauses := by
  let val := seqCounterBlockVal inputVal initialTop x final.ids
  simp only [seqCounterAtMostJFinish] at hfuture ⊢
  generalize h₁ : seqCounterMkYvar (t - 1, j) st = out₁ at hfuture ⊢
  rcases out₁ with ⟨stj, st₁⟩
  have hmem₁ : ((t - 1, j), stj) ∈ st₁.ids := by
    have h := seqCounterMkYvar_mem (t - 1, j) st
    rw [h₁] at h
    exact h
  have hsat₁ : dimacsFormulaSatisfied val st₁.clauses := by
    have h := dimacsFormulaSatisfied_mkYvar (t - 1, j) hprevious
    rw [h₁] at h
    exact h
  have htSize : t ≤ vars.size := by omega
  have hoverIdx : j + t < vars.size := by
    have hsub : vars.size - t + t = vars.size := Nat.sub_add_cancel htSize
    omega
  by_cases hhorizontal : j < vars.size - t - 1
  · simp only [hhorizontal, ↓reduceIte] at hfuture ⊢
    generalize h₂ : seqCounterMkYvar (t - 1, j + 1) st₁ = out₂ at hfuture ⊢
    rcases out₂ with ⟨stj1, st₂⟩
    have hext₁₂ : SeqCounterIdsExtend st₁ st₂ := by
      have h := seqCounterIdsExtend_mkYvar (t - 1, j + 1) st₁
      rw [h₂] at h
      exact h
    have hmem₂ : ((t - 1, j + 1), stj1) ∈ st₂.ids := by
      have h := seqCounterMkYvar_mem (t - 1, j + 1) st₁
      rw [h₂] at h
      exact h
    have hsat₂ : dimacsFormulaSatisfied val st₂.clauses := by
      have h := dimacsFormulaSatisfied_mkYvar (t - 1, j + 1) hsat₁
      rw [h₂] at h
      exact h
    let horizontal := [-(stj : Int), (stj1 : Int)]
    let st₃ := (seqCounterEmit horizontal st₂).2
    have hext₂₃ : SeqCounterIdsExtend st₂ st₃ :=
      seqCounterIdsExtend_emit horizontal st₂
    let overflow := [-(vars.getD (j + t) 0), -(stj : Int)]
    let finishOut := (seqCounterEmit overflow st₃).2
    have hext₃o : SeqCounterIdsExtend st₃ finishOut :=
      seqCounterIdsExtend_emit overflow st₃
    have hext₁f : SeqCounterIdsExtend st₁ final :=
      hext₁₂.trans (hext₂₃.trans (hext₃o.trans hfuture))
    have hext₂f : SeqCounterIdsExtend st₂ final :=
      hext₂₃.trans (hext₃o.trans hfuture)
    have hmem₁f := hext₁f _ hmem₁
    have hmem₂f := hext₂f _ hmem₂
    have hhorizontalSat : dimacsClauseSatisfied val horizontal := by
      apply dimacs_seqCounter_horizontal_clause_satisfied x val (t - 1) j
      · omega
      · exact seqCounterAux_positive_of_mem hfinalInv hmem₁f
      · exact seqCounterAux_positive_of_mem hfinalInv hmem₂f
      · simpa [val] using seqCounterBlockVal_aux inputVal x hfinalInv hmem₁f
      · simpa [val, Nat.add_assoc] using
          seqCounterBlockVal_aux inputVal x hfinalInv hmem₂f
    have hsat₃ : dimacsFormulaSatisfied val st₃.clauses :=
      dimacsFormulaSatisfied_emit hsat₂ hhorizontalSat
    have hinputValue : dimacsLitValue val (vars.getD (j + t) 0) =
        x ⟨j + t, hoverIdx⟩ := by
      simpa [val] using hinput.block_value final.ids _ hoverIdx
    have hauxValue : val stj =
        seqCounterWitness x (j + (t - 1)) (t - 1) := by
      simpa [val] using seqCounterBlockVal_aux inputVal x hfinalInv hmem₁f
    have hoverflowSat : dimacsClauseSatisfied val overflow :=
      dimacs_seqCounter_overflow_clause_satisfied_signed x val t j ht
        hoverIdx htotal (vars.getD (j + t) 0) stj
        (hinput.nonzero _ hoverIdx)
        (seqCounterAux_positive_of_mem hfinalInv hmem₁f)
        hinputValue hauxValue
    exact dimacsFormulaSatisfied_emit hsat₃ hoverflowSat
  · simp only [hhorizontal, ↓reduceIte] at hfuture ⊢
    let overflow := [-(vars.getD (j + t) 0), -(stj : Int)]
    let finishOut := (seqCounterEmit overflow st₁).2
    have hext₁o : SeqCounterIdsExtend st₁ finishOut :=
      seqCounterIdsExtend_emit overflow st₁
    have hmem₁f := (hext₁o.trans hfuture) _ hmem₁
    have hinputValue : dimacsLitValue val (vars.getD (j + t) 0) =
        x ⟨j + t, hoverIdx⟩ := by
      simpa [val] using hinput.block_value final.ids _ hoverIdx
    have hauxValue : val stj =
        seqCounterWitness x (j + (t - 1)) (t - 1) := by
      simpa [val] using seqCounterBlockVal_aux inputVal x hfinalInv hmem₁f
    have hoverflowSat : dimacsClauseSatisfied val overflow :=
      dimacs_seqCounter_overflow_clause_satisfied_signed x val t j ht
        hoverIdx htotal (vars.getD (j + t) 0) stj
        (hinput.nonzero _ hoverIdx)
        (seqCounterAux_positive_of_mem hfinalInv hmem₁f)
        hinputValue hauxValue
    exact dimacsFormulaSatisfied_emit hsat₁ hoverflowSat

/-- A complete outer iteration preserves satisfaction under the final table. -/
theorem seqCounterAtMostJStep_formulaSatisfied
    (inputVal : DimacsValuation) (initialTop : Nat) (vars : Array Int)
    (x : Fin vars.size → Bool)
    (hinput : SeqCounterInputReifies inputVal initialTop vars x)
    (t j : Nat) (ht : 0 < t) (hj : j < vars.size - t)
    (htotal : seqPrefixTrue x vars.size ≤ t)
    (st final : SeqCounterGenState)
    (hfinalInv : SeqCounterAllocationInvariant initialTop final)
    (hfuture : SeqCounterIdsExtend
      (seqCounterAtMostJStep vars t j st) final)
    (hprevious : dimacsFormulaSatisfied
      (seqCounterBlockVal inputVal initialTop x final.ids) st.clauses) :
    dimacsFormulaSatisfied
      (seqCounterBlockVal inputVal initialTop x final.ids)
      (seqCounterAtMostJStep vars t j st).clauses := by
  let prefixOut := seqCounterAtMostJPrefix vars j st
  let innerOut := seqCounterAtMostKLoop vars t j (t - 1) 0 prefixOut
  have hpq : SeqCounterIdsExtend prefixOut innerOut :=
    seqCounterIdsExtend_kLoop vars t j (t - 1) 0 prefixOut
  have hqo : SeqCounterIdsExtend innerOut
      (seqCounterAtMostJFinish vars t j innerOut) :=
    seqCounterIdsExtend_jFinish vars t j innerOut
  have hpFuture : SeqCounterIdsExtend prefixOut final :=
    hpq.trans (hqo.trans hfuture)
  have hqFuture : SeqCounterIdsExtend innerOut final := hqo.trans hfuture
  have hjSize : j < vars.size := lt_of_lt_of_le hj (Nat.sub_le _ _)
  have hprefixSat : dimacsFormulaSatisfied
      (seqCounterBlockVal inputVal initialTop x final.ids) prefixOut.clauses :=
    seqCounterAtMostJPrefix_formulaSatisfied inputVal initialTop vars x hinput
      j hjSize st final hfinalInv hpFuture hprevious
  have hinnerSat : dimacsFormulaSatisfied
      (seqCounterBlockVal inputVal initialTop x final.ids) innerOut.clauses :=
    seqCounterAtMostKLoop_formulaSatisfied inputVal initialTop vars x hinput
      t j (t - 1) 0 (by omega) hj prefixOut final hfinalInv hqFuture hprefixSat
  exact seqCounterAtMostJFinish_formulaSatisfied inputVal initialTop vars x
    hinput t j ht hj htotal innerOut final hfinalInv hfuture hinnerSat

/-- Every outer-loop iteration preserves satisfaction under the eventual
final table. -/
theorem seqCounterAtMostJLoop_formulaSatisfied
    (inputVal : DimacsValuation) (initialTop : Nat) (vars : Array Int)
    (x : Fin vars.size → Bool)
    (hinput : SeqCounterInputReifies inputVal initialTop vars x)
    (t fuel j : Nat) (ht : 0 < t)
    (hjfuel : j + fuel ≤ vars.size - t)
    (htotal : seqPrefixTrue x vars.size ≤ t)
    (st final : SeqCounterGenState)
    (hfinalInv : SeqCounterAllocationInvariant initialTop final)
    (hfuture : SeqCounterIdsExtend
      (seqCounterAtMostJLoop vars t fuel j st) final)
    (hprevious : dimacsFormulaSatisfied
      (seqCounterBlockVal inputVal initialTop x final.ids) st.clauses) :
    dimacsFormulaSatisfied
      (seqCounterBlockVal inputVal initialTop x final.ids)
      (seqCounterAtMostJLoop vars t fuel j st).clauses := by
  induction fuel generalizing j st with
  | zero => exact hprevious
  | succ fuel ih =>
      simp only [seqCounterAtMostJLoop] at hfuture ⊢
      let stepOut := seqCounterAtMostJStep vars t j st
      have hext : SeqCounterIdsExtend stepOut final :=
        (seqCounterIdsExtend_jLoop vars t fuel (j + 1) stepOut).trans hfuture
      have hstep : dimacsFormulaSatisfied
          (seqCounterBlockVal inputVal initialTop x final.ids)
          stepOut.clauses :=
        seqCounterAtMostJStep_formulaSatisfied inputVal initialTop vars x
          hinput t j ht (by omega) htotal st final hfinalInv hext hprevious
      apply ih
      · omega
      · exact hfuture
      · exact hstep

/-- Soundness of the exact byte-matched PySAT at-most core: the canonical
extension of any reified input row satisfying the bound satisfies every
generated clause. -/
theorem seqCounterAtMostCore_formulaSatisfied
    (inputVal : DimacsValuation) (top : Nat) (vars : Array Int)
    (x : Fin vars.size → Bool)
    (hinput : SeqCounterInputReifies inputVal top vars x)
    (t : Nat) (htotal : seqPrefixTrue x vars.size ≤ t) :
    dimacsFormulaSatisfied
      (seqCounterBlockVal inputVal top x
        (seqCounterAtMostCore top vars t).ids)
      (seqCounterAtMostCore top vars t).clauses := by
  unfold seqCounterAtMostCore
  split
  next hnontrivial =>
    apply seqCounterAtMostJLoop_formulaSatisfied inputVal top vars x hinput
      t (vars.size - t) 0 hnontrivial.1 (by omega) htotal
      ({ top := top } : SeqCounterGenState)
      (seqCounterAtMostJLoop vars t (vars.size - t) 0 { top := top })
    · apply seqCounterAllocationInvariant_jLoop
      exact seqCounterAllocationInvariant_initial top
    · exact SeqCounterIdsExtend.refl _
    · exact dimacsFormulaSatisfied_empty _
  next _ => exact dimacsFormulaSatisfied_empty _

/-! ## Complement and at-least blocks -/

/-- Boolean complement transported to the index type of the mapped negative
literal array. -/
def seqCounterMappedNegRow (vars : Array Int) (x : Fin vars.size → Bool) :
    Fin (vars.map fun v => -v).size → Bool := fun i =>
  !x ⟨i.val, by simpa using i.isLt⟩

theorem seqCounterInputReifies_map_neg
    (inputVal : DimacsValuation) (top : Nat) (vars : Array Int)
    (x : Fin vars.size → Bool)
    (hinput : SeqCounterInputReifies inputVal top vars x) :
    SeqCounterInputReifies inputVal top (vars.map fun v => -v)
      (seqCounterMappedNegRow vars x) := by
  constructor
  · rfl
  · intro i hi
    have hi' : i < vars.size := by simpa using hi
    have hn := hinput.nonzero i hi'
    simp [Array.getD, hi'] at hn
    simpa [Array.getD, hi'] using hn
  · intro i hi
    have hi' : i < vars.size := by simpa using hi
    have hb := hinput.bounded i hi'
    simp [Array.getD, hi'] at hb
    simpa [Array.getD, hi', Int.natAbs_neg] using hb
  · intro i hi
    have hi' : i < vars.size := by simpa using hi
    have hn := hinput.nonzero i hi'
    have hv := hinput.value i hi'
    simp [Array.getD, hi'] at hn hv ⊢
    rw [dimacsLitValue_neg inputVal hn, hv]
    rfl

theorem seqPrefixTrue_mappedNeg_add (vars : Array Int)
    (x : Fin vars.size → Bool) :
    seqPrefixTrue x vars.size +
      seqPrefixTrue (seqCounterMappedNegRow vars x)
        (vars.map fun v => -v).size = vars.size := by
  convert seqPrefixTrue_neg_add x using 1
  congr 1
  simp only [Array.size_map]
  unfold seqPrefixTrue
  congr 1
  ext i
  simp [seqCounterMappedNegRow, seqNeg]

/-- Soundness of PySAT's at-least block, obtained exactly as PySAT does:
negate the input literals and invoke the at-most core at bound `n-t`. -/
theorem seqCounterAtLeastCore_formulaSatisfied
    (inputVal : DimacsValuation) (top : Nat) (vars : Array Int)
    (x : Fin vars.size → Bool)
    (hinput : SeqCounterInputReifies inputVal top vars x)
    (t : Nat) (hlower : t ≤ seqPrefixTrue x vars.size) :
    let negRow := seqCounterMappedNegRow vars x
    dimacsFormulaSatisfied
      (seqCounterBlockVal inputVal top negRow
        (seqCounterAtLeastCore top vars t).ids)
      (seqCounterAtLeastCore top vars t).clauses := by
  dsimp only
  unfold seqCounterAtLeastCore
  apply seqCounterAtMostCore_formulaSatisfied inputVal top
    (vars.map fun v => -v) (seqCounterMappedNegRow vars x)
    (seqCounterInputReifies_map_neg inputVal top vars x hinput)
  have hsum := seqPrefixTrue_mappedNeg_add vars x
  omega

/-! ## Literal bounds for valuation gluing -/

theorem seqCounterAtMostKStep_formulaBounded
    (inputVal : DimacsValuation) (initialTop : Nat) (vars : Array Int)
    (x : Fin vars.size → Bool)
    (hinput : SeqCounterInputReifies inputVal initialTop vars x)
    (t j k : Nat) (hk : k < t - 1) (hj : j < vars.size - t)
    (st final : SeqCounterGenState)
    (hfinalInv : SeqCounterAllocationInvariant initialTop final)
    (hfuture : SeqCounterIdsExtend
      (seqCounterAtMostKStep vars t j k st) final)
    (hprevious : dimacsFormulaBounded final.top st.clauses) :
    dimacsFormulaBounded final.top
      (seqCounterAtMostKStep vars t j k st).clauses := by
  simp only [seqCounterAtMostKStep] at hfuture ⊢
  generalize h₁ : seqCounterMkYvar (k, j) st = out₁ at hfuture ⊢
  rcases out₁ with ⟨skj, st₁⟩
  have hmem₁ : ((k, j), skj) ∈ st₁.ids := by
    have h := seqCounterMkYvar_mem (k, j) st
    rw [h₁] at h
    exact h
  have hbound₁ : dimacsFormulaBounded final.top st₁.clauses := by
    have h := dimacsFormulaBounded_mkYvar (k, j) hprevious
    rw [h₁] at h
    exact h
  have htSize : t ≤ vars.size := by omega
  have hidx : j + k + 1 < vars.size := by
    have hsub : vars.size - t + t = vars.size := Nat.sub_add_cancel htSize
    omega
  by_cases hhorizontal : j < vars.size - t - 1
  · simp only [hhorizontal, ↓reduceIte] at hfuture ⊢
    generalize h₂ : seqCounterMkYvar (k, j + 1) st₁ = out₂ at hfuture ⊢
    rcases out₂ with ⟨skj1, st₂⟩
    have hext₁₂ : SeqCounterIdsExtend st₁ st₂ := by
      have h := seqCounterIdsExtend_mkYvar (k, j + 1) st₁
      rw [h₂] at h
      exact h
    have hmem₂ : ((k, j + 1), skj1) ∈ st₂.ids := by
      have h := seqCounterMkYvar_mem (k, j + 1) st₁
      rw [h₂] at h
      exact h
    have hbound₂ : dimacsFormulaBounded final.top st₂.clauses := by
      have h := dimacsFormulaBounded_mkYvar (k, j + 1) hbound₁
      rw [h₂] at h
      exact h
    let horizontal := [-(skj : Int), (skj1 : Int)]
    let st₃ := (seqCounterEmit horizontal st₂).2
    have hext₂₃ : SeqCounterIdsExtend st₂ st₃ :=
      seqCounterIdsExtend_emit horizontal st₂
    generalize h₄ : seqCounterMkYvar (k + 1, j) st₃ = out₄ at hfuture ⊢
    rcases out₄ with ⟨sk1j, st₄⟩
    have hext₃₄ : SeqCounterIdsExtend st₃ st₄ := by
      have h := seqCounterIdsExtend_mkYvar (k + 1, j) st₃
      rw [h₄] at h
      exact h
    let diagonal :=
      [-(vars.getD (j + k + 1) 0), -(skj : Int), (sk1j : Int)]
    let stepOut := (seqCounterEmit diagonal st₄).2
    have hext₄o : SeqCounterIdsExtend st₄ stepOut :=
      seqCounterIdsExtend_emit diagonal st₄
    have hext₁f : SeqCounterIdsExtend st₁ final :=
      hext₁₂.trans (hext₂₃.trans (hext₃₄.trans (hext₄o.trans hfuture)))
    have hext₂f : SeqCounterIdsExtend st₂ final :=
      hext₂₃.trans (hext₃₄.trans (hext₄o.trans hfuture))
    have hext₄f : SeqCounterIdsExtend st₄ final := hext₄o.trans hfuture
    have hmem₁f := hext₁f _ hmem₁
    have hmem₂f := hext₂f _ hmem₂
    have hhorizontalBound : dimacsClauseBounded final.top horizontal :=
      dimacsSeqCounter_horizontal_bounded hfinalInv hmem₁f hmem₂f
    have hbound₃ : dimacsFormulaBounded final.top st₃.clauses :=
      dimacsFormulaBounded_emit hbound₂ hhorizontalBound
    have hmem₄ : ((k + 1, j), sk1j) ∈ st₄.ids := by
      have h := seqCounterMkYvar_mem (k + 1, j) st₃
      rw [h₄] at h
      exact h
    have hmem₄f := hext₄f _ hmem₄
    have hbound₄ : dimacsFormulaBounded final.top st₄.clauses := by
      have h := dimacsFormulaBounded_mkYvar (k + 1, j) hbound₃
      rw [h₄] at h
      exact h
    have hdiagBound : dimacsClauseBounded final.top diagonal :=
      dimacsSeqCounter_diagonal_bounded hfinalInv
        (hinput.bounded _ hidx) hmem₁f hmem₄f
    exact dimacsFormulaBounded_emit hbound₄ hdiagBound
  · simp only [hhorizontal, ↓reduceIte] at hfuture ⊢
    generalize h₂ : seqCounterMkYvar (k + 1, j) st₁ = out₂ at hfuture ⊢
    rcases out₂ with ⟨sk1j, st₂⟩
    have hext₁₂ : SeqCounterIdsExtend st₁ st₂ := by
      have h := seqCounterIdsExtend_mkYvar (k + 1, j) st₁
      rw [h₂] at h
      exact h
    let diagonal :=
      [-(vars.getD (j + k + 1) 0), -(skj : Int), (sk1j : Int)]
    let stepOut := (seqCounterEmit diagonal st₂).2
    have hext₂o : SeqCounterIdsExtend st₂ stepOut :=
      seqCounterIdsExtend_emit diagonal st₂
    have hext₁f : SeqCounterIdsExtend st₁ final :=
      hext₁₂.trans (hext₂o.trans hfuture)
    have hext₂f : SeqCounterIdsExtend st₂ final := hext₂o.trans hfuture
    have hmem₁f := hext₁f _ hmem₁
    have hmem₂ : ((k + 1, j), sk1j) ∈ st₂.ids := by
      have h := seqCounterMkYvar_mem (k + 1, j) st₁
      rw [h₂] at h
      exact h
    have hmem₂f := hext₂f _ hmem₂
    have hbound₂ : dimacsFormulaBounded final.top st₂.clauses := by
      have h := dimacsFormulaBounded_mkYvar (k + 1, j) hbound₁
      rw [h₂] at h
      exact h
    have hdiagBound : dimacsClauseBounded final.top diagonal :=
      dimacsSeqCounter_diagonal_bounded hfinalInv
        (hinput.bounded _ hidx) hmem₁f hmem₂f
    exact dimacsFormulaBounded_emit hbound₂ hdiagBound

theorem seqCounterAtMostKLoop_formulaBounded
    (inputVal : DimacsValuation) (initialTop : Nat) (vars : Array Int)
    (x : Fin vars.size → Bool)
    (hinput : SeqCounterInputReifies inputVal initialTop vars x)
    (t j fuel k : Nat) (hkfuel : k + fuel ≤ t - 1)
    (hj : j < vars.size - t) (st final : SeqCounterGenState)
    (hfinalInv : SeqCounterAllocationInvariant initialTop final)
    (hfuture : SeqCounterIdsExtend
      (seqCounterAtMostKLoop vars t j fuel k st) final)
    (hprevious : dimacsFormulaBounded final.top st.clauses) :
    dimacsFormulaBounded final.top
      (seqCounterAtMostKLoop vars t j fuel k st).clauses := by
  induction fuel generalizing k st with
  | zero => exact hprevious
  | succ fuel ih =>
      simp only [seqCounterAtMostKLoop] at hfuture ⊢
      let stepOut := seqCounterAtMostKStep vars t j k st
      have hext : SeqCounterIdsExtend stepOut final :=
        (seqCounterIdsExtend_kLoop vars t j fuel (k + 1) stepOut).trans hfuture
      have hstep : dimacsFormulaBounded final.top stepOut.clauses :=
        seqCounterAtMostKStep_formulaBounded inputVal initialTop vars x hinput
          t j k (by omega) hj st final hfinalInv hext hprevious
      apply ih
      · omega
      · exact hfuture
      · exact hstep

theorem seqCounterAtMostJPrefix_formulaBounded
    (inputVal : DimacsValuation) (initialTop : Nat) (vars : Array Int)
    (x : Fin vars.size → Bool)
    (hinput : SeqCounterInputReifies inputVal initialTop vars x)
    (j : Nat) (hj : j < vars.size) (st final : SeqCounterGenState)
    (hfinalInv : SeqCounterAllocationInvariant initialTop final)
    (hfuture : SeqCounterIdsExtend
      (seqCounterAtMostJPrefix vars j st) final)
    (hprevious : dimacsFormulaBounded final.top st.clauses) :
    dimacsFormulaBounded final.top
      (seqCounterAtMostJPrefix vars j st).clauses := by
  simp only [seqCounterAtMostJPrefix] at hfuture ⊢
  generalize h₁ : seqCounterMkYvar (0, j) st = out₁ at hfuture ⊢
  rcases out₁ with ⟨s0j, st₁⟩
  have hmem₁ : ((0, j), s0j) ∈ st₁.ids := by
    have h := seqCounterMkYvar_mem (0, j) st
    rw [h₁] at h
    exact h
  have hext₁o : SeqCounterIdsExtend st₁
      (seqCounterEmit [-(vars.getD j 0), (s0j : Int)] st₁).2 :=
    seqCounterIdsExtend_emit _ st₁
  have hmem₁f := (hext₁o.trans hfuture) _ hmem₁
  have hbound₁ : dimacsFormulaBounded final.top st₁.clauses := by
    have h := dimacsFormulaBounded_mkYvar (0, j) hprevious
    rw [h₁] at h
    exact h
  have hbaseBound : dimacsClauseBounded final.top
      [-(vars.getD j 0), (s0j : Int)] :=
    dimacsSeqCounter_base_bounded hfinalInv
      (hinput.bounded j hj) hmem₁f
  exact dimacsFormulaBounded_emit hbound₁ hbaseBound

theorem seqCounterAtMostJFinish_formulaBounded
    (inputVal : DimacsValuation) (initialTop : Nat) (vars : Array Int)
    (x : Fin vars.size → Bool)
    (hinput : SeqCounterInputReifies inputVal initialTop vars x)
    (t j : Nat) (_ht : 0 < t) (hj : j < vars.size - t)
    (st final : SeqCounterGenState)
    (hfinalInv : SeqCounterAllocationInvariant initialTop final)
    (hfuture : SeqCounterIdsExtend
      (seqCounterAtMostJFinish vars t j st) final)
    (hprevious : dimacsFormulaBounded final.top st.clauses) :
    dimacsFormulaBounded final.top
      (seqCounterAtMostJFinish vars t j st).clauses := by
  simp only [seqCounterAtMostJFinish] at hfuture ⊢
  generalize h₁ : seqCounterMkYvar (t - 1, j) st = out₁ at hfuture ⊢
  rcases out₁ with ⟨stj, st₁⟩
  have hmem₁ : ((t - 1, j), stj) ∈ st₁.ids := by
    have h := seqCounterMkYvar_mem (t - 1, j) st
    rw [h₁] at h
    exact h
  have hbound₁ : dimacsFormulaBounded final.top st₁.clauses := by
    have h := dimacsFormulaBounded_mkYvar (t - 1, j) hprevious
    rw [h₁] at h
    exact h
  have htSize : t ≤ vars.size := by omega
  have hoverIdx : j + t < vars.size := by
    have hsub : vars.size - t + t = vars.size := Nat.sub_add_cancel htSize
    omega
  by_cases hhorizontal : j < vars.size - t - 1
  · simp only [hhorizontal, ↓reduceIte] at hfuture ⊢
    generalize h₂ : seqCounterMkYvar (t - 1, j + 1) st₁ = out₂ at hfuture ⊢
    rcases out₂ with ⟨stj1, st₂⟩
    have hext₁₂ : SeqCounterIdsExtend st₁ st₂ := by
      have h := seqCounterIdsExtend_mkYvar (t - 1, j + 1) st₁
      rw [h₂] at h
      exact h
    have hmem₂ : ((t - 1, j + 1), stj1) ∈ st₂.ids := by
      have h := seqCounterMkYvar_mem (t - 1, j + 1) st₁
      rw [h₂] at h
      exact h
    have hbound₂ : dimacsFormulaBounded final.top st₂.clauses := by
      have h := dimacsFormulaBounded_mkYvar (t - 1, j + 1) hbound₁
      rw [h₂] at h
      exact h
    let horizontal := [-(stj : Int), (stj1 : Int)]
    let st₃ := (seqCounterEmit horizontal st₂).2
    have hext₂₃ : SeqCounterIdsExtend st₂ st₃ :=
      seqCounterIdsExtend_emit horizontal st₂
    let overflow := [-(vars.getD (j + t) 0), -(stj : Int)]
    let finishOut := (seqCounterEmit overflow st₃).2
    have hext₃o : SeqCounterIdsExtend st₃ finishOut :=
      seqCounterIdsExtend_emit overflow st₃
    have hext₁f : SeqCounterIdsExtend st₁ final :=
      hext₁₂.trans (hext₂₃.trans (hext₃o.trans hfuture))
    have hext₂f : SeqCounterIdsExtend st₂ final :=
      hext₂₃.trans (hext₃o.trans hfuture)
    have hmem₁f := hext₁f _ hmem₁
    have hmem₂f := hext₂f _ hmem₂
    have hhorizontalBound : dimacsClauseBounded final.top horizontal :=
      dimacsSeqCounter_horizontal_bounded hfinalInv hmem₁f hmem₂f
    have hbound₃ : dimacsFormulaBounded final.top st₃.clauses :=
      dimacsFormulaBounded_emit hbound₂ hhorizontalBound
    have hoverflowBound : dimacsClauseBounded final.top overflow :=
      dimacsSeqCounter_overflow_bounded hfinalInv
        (hinput.bounded _ hoverIdx) hmem₁f
    exact dimacsFormulaBounded_emit hbound₃ hoverflowBound
  · simp only [hhorizontal, ↓reduceIte] at hfuture ⊢
    let overflow := [-(vars.getD (j + t) 0), -(stj : Int)]
    let finishOut := (seqCounterEmit overflow st₁).2
    have hext₁o : SeqCounterIdsExtend st₁ finishOut :=
      seqCounterIdsExtend_emit overflow st₁
    have hmem₁f := (hext₁o.trans hfuture) _ hmem₁
    have hoverflowBound : dimacsClauseBounded final.top overflow :=
      dimacsSeqCounter_overflow_bounded hfinalInv
        (hinput.bounded _ hoverIdx) hmem₁f
    exact dimacsFormulaBounded_emit hbound₁ hoverflowBound

theorem seqCounterAtMostJStep_formulaBounded
    (inputVal : DimacsValuation) (initialTop : Nat) (vars : Array Int)
    (x : Fin vars.size → Bool)
    (hinput : SeqCounterInputReifies inputVal initialTop vars x)
    (t j : Nat) (ht : 0 < t) (hj : j < vars.size - t)
    (st final : SeqCounterGenState)
    (hfinalInv : SeqCounterAllocationInvariant initialTop final)
    (hfuture : SeqCounterIdsExtend
      (seqCounterAtMostJStep vars t j st) final)
    (hprevious : dimacsFormulaBounded final.top st.clauses) :
    dimacsFormulaBounded final.top
      (seqCounterAtMostJStep vars t j st).clauses := by
  let prefixOut := seqCounterAtMostJPrefix vars j st
  let innerOut := seqCounterAtMostKLoop vars t j (t - 1) 0 prefixOut
  have hpq : SeqCounterIdsExtend prefixOut innerOut :=
    seqCounterIdsExtend_kLoop vars t j (t - 1) 0 prefixOut
  have hqo : SeqCounterIdsExtend innerOut
      (seqCounterAtMostJFinish vars t j innerOut) :=
    seqCounterIdsExtend_jFinish vars t j innerOut
  have hpFuture : SeqCounterIdsExtend prefixOut final :=
    hpq.trans (hqo.trans hfuture)
  have hqFuture : SeqCounterIdsExtend innerOut final := hqo.trans hfuture
  have hjSize : j < vars.size := lt_of_lt_of_le hj (Nat.sub_le _ _)
  have hprefixBound : dimacsFormulaBounded final.top prefixOut.clauses :=
    seqCounterAtMostJPrefix_formulaBounded inputVal initialTop vars x hinput
      j hjSize st final hfinalInv hpFuture hprevious
  have hinnerBound : dimacsFormulaBounded final.top innerOut.clauses :=
    seqCounterAtMostKLoop_formulaBounded inputVal initialTop vars x hinput
      t j (t - 1) 0 (by omega) hj prefixOut final hfinalInv hqFuture hprefixBound
  exact seqCounterAtMostJFinish_formulaBounded inputVal initialTop vars x
    hinput t j ht hj innerOut final hfinalInv hfuture hinnerBound

theorem seqCounterAtMostJLoop_formulaBounded
    (inputVal : DimacsValuation) (initialTop : Nat) (vars : Array Int)
    (x : Fin vars.size → Bool)
    (hinput : SeqCounterInputReifies inputVal initialTop vars x)
    (t fuel j : Nat) (ht : 0 < t)
    (hjfuel : j + fuel ≤ vars.size - t)
    (st final : SeqCounterGenState)
    (hfinalInv : SeqCounterAllocationInvariant initialTop final)
    (hfuture : SeqCounterIdsExtend
      (seqCounterAtMostJLoop vars t fuel j st) final)
    (hprevious : dimacsFormulaBounded final.top st.clauses) :
    dimacsFormulaBounded final.top
      (seqCounterAtMostJLoop vars t fuel j st).clauses := by
  induction fuel generalizing j st with
  | zero => exact hprevious
  | succ fuel ih =>
      simp only [seqCounterAtMostJLoop] at hfuture ⊢
      let stepOut := seqCounterAtMostJStep vars t j st
      have hext : SeqCounterIdsExtend stepOut final :=
        (seqCounterIdsExtend_jLoop vars t fuel (j + 1) stepOut).trans hfuture
      have hstep : dimacsFormulaBounded final.top stepOut.clauses :=
        seqCounterAtMostJStep_formulaBounded inputVal initialTop vars x hinput
          t j ht (by omega) st final hfinalInv hext hprevious
      apply ih
      · omega
      · exact hfuture
      · exact hstep

/-- Every literal emitted by the exact at-most core is at most the final top
identifier. -/
theorem seqCounterAtMostCore_formulaBounded
    (inputVal : DimacsValuation) (top : Nat) (vars : Array Int)
    (x : Fin vars.size → Bool)
    (hinput : SeqCounterInputReifies inputVal top vars x) (t : Nat) :
    dimacsFormulaBounded (seqCounterAtMostCore top vars t).top
      (seqCounterAtMostCore top vars t).clauses := by
  unfold seqCounterAtMostCore
  split
  next hnontrivial =>
    apply seqCounterAtMostJLoop_formulaBounded inputVal top vars x hinput
      t (vars.size - t) 0 hnontrivial.1 (by omega)
      ({ top := top } : SeqCounterGenState)
      (seqCounterAtMostJLoop vars t (vars.size - t) 0 { top := top })
    · apply seqCounterAllocationInvariant_jLoop
      exact seqCounterAllocationInvariant_initial top
    · exact SeqCounterIdsExtend.refl _
    · exact dimacsFormulaBounded_empty _
  next _ => exact dimacsFormulaBounded_empty _

theorem seqCounterAtLeastCore_formulaBounded
    (inputVal : DimacsValuation) (top : Nat) (vars : Array Int)
    (x : Fin vars.size → Bool)
    (hinput : SeqCounterInputReifies inputVal top vars x) (t : Nat) :
    dimacsFormulaBounded (seqCounterAtLeastCore top vars t).top
      (seqCounterAtLeastCore top vars t).clauses := by
  unfold seqCounterAtLeastCore
  exact seqCounterAtMostCore_formulaBounded inputVal top
    (vars.map fun v => -v) (seqCounterMappedNegRow vars x)
    (seqCounterInputReifies_map_neg inputVal top vars x hinput) (vars.size - t)

/-- Adding an auxiliary layer above `top` does not change any original input
literal and permits raising the boundary to a later top. -/
theorem SeqCounterInputReifies.liftBlock {n m : Nat}
    {inputVal : DimacsValuation} {top newTop : Nat} {vars : Array Int}
    {x : Fin n → Bool} (hinput : SeqCounterInputReifies inputVal top vars x)
    (y : Fin m → Bool) (ids : List ((Nat × Nat) × Nat))
    (htop : top ≤ newTop) :
    SeqCounterInputReifies (seqCounterBlockVal inputVal top y ids)
      newTop vars x := by
  constructor
  · exact hinput.size_eq
  · exact hinput.nonzero
  · intro i hi
    exact (hinput.bounded i hi).trans htop
  · intro i hi
    rw [dimacsLitValue_block_of_natAbs_le inputVal top y ids
      (hinput.bounded i hi)]
    exact hinput.value i hi

theorem dimacsFormulaSatisfied_append {val : DimacsValuation}
    {left right : Array DimacsClause}
    (hleft : dimacsFormulaSatisfied val left)
    (hright : dimacsFormulaSatisfied val right) :
    dimacsFormulaSatisfied val (left ++ right) := by
  intro clause hclause
  simp only [Array.mem_append] at hclause
  rcases hclause with hclause | hclause
  · exact hleft clause hclause
  · exact hright clause hclause

/-- Soundness of the full PySAT equality block.  Its valuation is layered:
first the complemented-row lower counter, then the original-row upper counter
above `lower.top`. -/
theorem seqCounterEqualsCore_formulaSatisfied
    (inputVal : DimacsValuation) (top : Nat) (vars : Array Int)
    (x : Fin vars.size → Bool)
    (hinput : SeqCounterInputReifies inputVal top vars x)
    (t : Nat) (hcount : seqPrefixTrue x vars.size = t) :
    let negRow := seqCounterMappedNegRow vars x
    let lower := seqCounterAtLeastCore top vars t
    let lowerVal := seqCounterBlockVal inputVal top negRow lower.ids
    let upper := seqCounterAtMostCore lower.top vars t
    let upperVal := seqCounterBlockVal lowerVal lower.top x upper.ids
    dimacsFormulaSatisfied upperVal
      (seqCounterEqualsCore top vars t).clauses := by
  dsimp only
  let negRow := seqCounterMappedNegRow vars x
  let lower := seqCounterAtLeastCore top vars t
  let lowerVal := seqCounterBlockVal inputVal top negRow lower.ids
  let upper := seqCounterAtMostCore lower.top vars t
  let upperVal := seqCounterBlockVal lowerVal lower.top x upper.ids
  have hlowerSat : dimacsFormulaSatisfied lowerVal lower.clauses := by
    simpa [lower, lowerVal, negRow] using
      seqCounterAtLeastCore_formulaSatisfied inputVal top vars x hinput t
        (by omega)
  have hlowerBound : dimacsFormulaBounded lower.top lower.clauses := by
    simpa [lower] using
      seqCounterAtLeastCore_formulaBounded inputVal top vars x hinput t
  have hlowerInv : SeqCounterAllocationInvariant top lower := by
    simpa [lower, seqCounterAtLeastCore] using
      seqCounterAtMostCore_allocationInvariant top
        (vars.map fun v => -v) (vars.size - t)
  have hlowerSatUpper : dimacsFormulaSatisfied upperVal lower.clauses := by
    apply dimacsFormulaSatisfied_of_bounded_agree hlowerSat hlowerBound
    intro id hid
    exact (seqCounterBlockVal_input lowerVal lower.top x upper.ids hid).symm
  have hinputUpper : SeqCounterInputReifies lowerVal lower.top vars x := by
    exact hinput.liftBlock negRow lower.ids hlowerInv.top_bound
  have hupperSat : dimacsFormulaSatisfied upperVal upper.clauses := by
    simpa [upper, upperVal] using
      seqCounterAtMostCore_formulaSatisfied lowerVal lower.top vars x
        hinputUpper t (by omega)
  simpa [seqCounterEqualsCore, lower, upper] using
    dimacsFormulaSatisfied_append hlowerSatUpper hupperSat

end Erdos85
