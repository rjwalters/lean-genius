import Proofs.Erdos85OrderFortyNineDegreeBlocks

/-!
# Nonzero literals in the order-49 degree-counter blocks

`orderFortyNineDegreeBlocks h` folds PySAT's sequential-counter equality
encoding over all 49 vertex rows.  The generated CNF must contain no literal
`0` (a DIMACS clause terminator) before it can be translated clausewise into
a `Std.Sat.CNF`.  Previously this was checked by kernel `decide` over the
whole generated formula, which is far too expensive for a clean rebuild.

This file proves it structurally (`orderFortyNineDegreeBlocks_nonzero_all`,
stated with the literal condition unfolded so that it sits below
`Erdos85DimacsSatBridge` in the import graph): every emitted literal is either an input
literal of the row (a positive edge index) or an auxiliary variable, and every
auxiliary variable is allocated as `top + 1 > 0`.  The proof mirrors the
`formulaBounded` induction in `Erdos85SequentialCounterReification`, but the
invariant needs neither valuations nor an allocation bound.
-/

namespace Erdos85

/-- Nonzero-literal invariant of the sequential-counter generator state:
every emitted clause is free of the literal `0`, and every allocated
auxiliary identifier is positive. -/
def SeqCounterNonzeroState (st : SeqCounterGenState) : Prop :=
  (∀ clause ∈ st.clauses, ∀ lit ∈ clause, lit ≠ 0) ∧
    ∀ entry ∈ st.ids, 0 < entry.2

theorem seqCounterNonzeroState_initial (top : Nat) :
    SeqCounterNonzeroState { top := top } := by
  refine ⟨?_, ?_⟩ <;> intro x hx <;> simp at hx

theorem seqCounterNonzeroState_mkYvar {st : SeqCounterGenState}
    (h : SeqCounterNonzeroState st) (key : Nat × Nat) :
    SeqCounterNonzeroState (seqCounterMkYvar key st).2 ∧
      0 < (seqCounterMkYvar key st).1 := by
  unfold seqCounterMkYvar
  rcases hlook : seqCounterLookup key st.ids with _ | id
  · refine ⟨⟨h.1, ?_⟩, Nat.succ_pos _⟩
    intro entry hentry
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | hentry
    · exact Nat.succ_pos _
    · exact h.2 entry hentry
  · exact ⟨h, h.2 _ (seqCounterLookup_mem hlook)⟩

theorem seqCounterNonzeroState_emit {st : SeqCounterGenState}
    (h : SeqCounterNonzeroState st) {clause : DimacsClause}
    (hclause : ∀ lit ∈ clause, lit ≠ 0) :
    SeqCounterNonzeroState (seqCounterEmit clause st).2 := by
  refine ⟨?_, h.2⟩
  intro candidate hcandidate
  change candidate ∈ st.clauses.push clause at hcandidate
  simp only [Array.mem_push] at hcandidate
  rcases hcandidate with hold | rfl
  · exact h.1 candidate hold
  · exact hclause

theorem seqCounterAtMostKStep_nonzero (vars : Array Int)
    (hvars : ∀ i, i < vars.size → vars.getD i 0 ≠ 0)
    (t j k : Nat) (hk : k < t - 1) (hj : j < vars.size - t)
    {st : SeqCounterGenState} (hst : SeqCounterNonzeroState st) :
    SeqCounterNonzeroState (seqCounterAtMostKStep vars t j k st) := by
  simp only [seqCounterAtMostKStep]
  obtain ⟨h₁, hskj⟩ := seqCounterNonzeroState_mkYvar hst (k, j)
  generalize hout₁ : seqCounterMkYvar (k, j) st = out₁ at h₁ hskj ⊢
  rcases out₁ with ⟨skj, st₁⟩
  have hidx : j + k + 1 < vars.size := by omega
  have hin := hvars _ hidx
  by_cases hhorizontal : j < vars.size - t - 1
  · simp only [hhorizontal, ↓reduceIte]
    obtain ⟨h₂, hskj1⟩ := seqCounterNonzeroState_mkYvar h₁ (k, j + 1)
    generalize hout₂ : seqCounterMkYvar (k, j + 1) st₁ = out₂ at h₂ hskj1 ⊢
    rcases out₂ with ⟨skj1, st₂⟩
    have h₃ : SeqCounterNonzeroState
        (seqCounterEmit [-(skj : Int), (skj1 : Int)] st₂).2 :=
      seqCounterNonzeroState_emit h₂ (by
        intro lit hlit
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hlit
        omega)
    obtain ⟨h₄, hsk1j⟩ := seqCounterNonzeroState_mkYvar h₃ (k + 1, j)
    generalize hout₄ : seqCounterMkYvar (k + 1, j)
      (seqCounterEmit [-(skj : Int), (skj1 : Int)] st₂).2 = out₄ at h₄ hsk1j ⊢
    rcases out₄ with ⟨sk1j, st₄⟩
    exact seqCounterNonzeroState_emit h₄ (by
      intro lit hlit
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hlit
      omega)
  · simp only [hhorizontal, ↓reduceIte]
    obtain ⟨h₂, hsk1j⟩ := seqCounterNonzeroState_mkYvar h₁ (k + 1, j)
    generalize hout₂ : seqCounterMkYvar (k + 1, j) st₁ = out₂ at h₂ hsk1j ⊢
    rcases out₂ with ⟨sk1j, st₂⟩
    exact seqCounterNonzeroState_emit h₂ (by
      intro lit hlit
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hlit
      omega)

theorem seqCounterAtMostKLoop_nonzero (vars : Array Int)
    (hvars : ∀ i, i < vars.size → vars.getD i 0 ≠ 0)
    (t j fuel k : Nat) (hkfuel : k + fuel ≤ t - 1)
    (hj : j < vars.size - t)
    {st : SeqCounterGenState} (hst : SeqCounterNonzeroState st) :
    SeqCounterNonzeroState (seqCounterAtMostKLoop vars t j fuel k st) := by
  induction fuel generalizing k st with
  | zero => exact hst
  | succ fuel ih =>
      simp only [seqCounterAtMostKLoop]
      apply ih (k + 1) (by omega)
      exact seqCounterAtMostKStep_nonzero vars hvars t j k (by omega) hj hst

theorem seqCounterAtMostJPrefix_nonzero (vars : Array Int)
    (hvars : ∀ i, i < vars.size → vars.getD i 0 ≠ 0)
    (j : Nat) (hj : j < vars.size)
    {st : SeqCounterGenState} (hst : SeqCounterNonzeroState st) :
    SeqCounterNonzeroState (seqCounterAtMostJPrefix vars j st) := by
  simp only [seqCounterAtMostJPrefix]
  obtain ⟨h₁, hs0j⟩ := seqCounterNonzeroState_mkYvar hst (0, j)
  generalize hout₁ : seqCounterMkYvar (0, j) st = out₁ at h₁ hs0j ⊢
  rcases out₁ with ⟨s0j, st₁⟩
  have hin := hvars _ hj
  exact seqCounterNonzeroState_emit h₁ (by
    intro lit hlit
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hlit
    omega)

theorem seqCounterAtMostJFinish_nonzero (vars : Array Int)
    (hvars : ∀ i, i < vars.size → vars.getD i 0 ≠ 0)
    (t j : Nat) (hj : j < vars.size - t)
    {st : SeqCounterGenState} (hst : SeqCounterNonzeroState st) :
    SeqCounterNonzeroState (seqCounterAtMostJFinish vars t j st) := by
  simp only [seqCounterAtMostJFinish]
  obtain ⟨h₁, hstj⟩ := seqCounterNonzeroState_mkYvar hst (t - 1, j)
  generalize hout₁ : seqCounterMkYvar (t - 1, j) st = out₁ at h₁ hstj ⊢
  rcases out₁ with ⟨stj, st₁⟩
  have hidx : j + t < vars.size := by omega
  have hin := hvars _ hidx
  by_cases hhorizontal : j < vars.size - t - 1
  · simp only [hhorizontal, ↓reduceIte]
    obtain ⟨h₂, hstj1⟩ := seqCounterNonzeroState_mkYvar h₁ (t - 1, j + 1)
    generalize hout₂ : seqCounterMkYvar (t - 1, j + 1) st₁ = out₂ at h₂ hstj1 ⊢
    rcases out₂ with ⟨stj1, st₂⟩
    have h₃ : SeqCounterNonzeroState
        (seqCounterEmit [-(stj : Int), (stj1 : Int)] st₂).2 :=
      seqCounterNonzeroState_emit h₂ (by
        intro lit hlit
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hlit
        omega)
    exact seqCounterNonzeroState_emit h₃ (by
      intro lit hlit
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hlit
      omega)
  · simp only [hhorizontal, ↓reduceIte]
    exact seqCounterNonzeroState_emit h₁ (by
      intro lit hlit
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hlit
      omega)

theorem seqCounterAtMostJStep_nonzero (vars : Array Int)
    (hvars : ∀ i, i < vars.size → vars.getD i 0 ≠ 0)
    (t j : Nat) (ht : 0 < t) (hj : j < vars.size - t)
    {st : SeqCounterGenState} (hst : SeqCounterNonzeroState st) :
    SeqCounterNonzeroState (seqCounterAtMostJStep vars t j st) := by
  simp only [seqCounterAtMostJStep]
  apply seqCounterAtMostJFinish_nonzero vars hvars t j hj
  apply seqCounterAtMostKLoop_nonzero vars hvars t j (t - 1) 0 (by omega) hj
  exact seqCounterAtMostJPrefix_nonzero vars hvars j (by omega) hst

theorem seqCounterAtMostJLoop_nonzero (vars : Array Int)
    (hvars : ∀ i, i < vars.size → vars.getD i 0 ≠ 0)
    (t fuel j : Nat) (ht : 0 < t) (hjfuel : j + fuel ≤ vars.size - t)
    {st : SeqCounterGenState} (hst : SeqCounterNonzeroState st) :
    SeqCounterNonzeroState (seqCounterAtMostJLoop vars t fuel j st) := by
  induction fuel generalizing j st with
  | zero => exact hst
  | succ fuel ih =>
      simp only [seqCounterAtMostJLoop]
      apply ih (j + 1) (by omega)
      exact seqCounterAtMostJStep_nonzero vars hvars t j ht (by omega) hst

theorem seqCounterAtMostCore_nonzero (top : Nat) (vars : Array Int)
    (hvars : ∀ i, i < vars.size → vars.getD i 0 ≠ 0) (t : Nat) :
    SeqCounterNonzeroState (seqCounterAtMostCore top vars t) := by
  unfold seqCounterAtMostCore
  split
  · next hnontrivial =>
      exact seqCounterAtMostJLoop_nonzero vars hvars t (vars.size - t) 0
        hnontrivial.1 (by omega) (seqCounterNonzeroState_initial top)
  · exact seqCounterNonzeroState_initial top

theorem seqCounterAtLeastCore_nonzero (top : Nat) (vars : Array Int)
    (hvars : ∀ i, i < vars.size → vars.getD i 0 ≠ 0) (t : Nat) :
    SeqCounterNonzeroState (seqCounterAtLeastCore top vars t) := by
  unfold seqCounterAtLeastCore
  apply seqCounterAtMostCore_nonzero
  intro i hi
  simp only [Array.size_map] at hi
  simp [Array.getD, hi, Array.getElem_map]
  have := hvars i hi
  simp [Array.getD, hi] at this
  exact this

theorem seqCounterEqualsCore_nonzero (top : Nat) (vars : Array Int)
    (hvars : ∀ i, i < vars.size → vars.getD i 0 ≠ 0) (t : Nat) :
    ∀ clause ∈ (seqCounterEqualsCore top vars t).clauses,
      ∀ lit ∈ clause, lit ≠ 0 := by
  intro clause hclause
  simp only [seqCounterEqualsCore, Array.mem_append] at hclause
  rcases hclause with hlower | hupper
  · exact (seqCounterAtLeastCore_nonzero top vars hvars t).1 clause hlower
  · exact (seqCounterAtMostCore_nonzero _ vars hvars t).1 clause hupper

/-- Every literal of a DIMACS row is a positive edge index. -/
theorem orderFortyNineDimacsRow_getD_nonzero (i : Fin 49) :
    ∀ k, k < (orderFortyNineDimacsRow i).size →
      (orderFortyNineDimacsRow i).getD k 0 ≠ 0 := by
  intro k hk
  have hk' : k < 48 := by simpa [orderFortyNineDimacsRow] using hk
  simp [orderFortyNineDimacsRow, Array.getD, hk', orderFortyNineEdgeLiteral]
  omega

theorem orderFortyNineDegreeBlockStep_nonzero (h : Nat)
    {st : SeqCounterGenState}
    (hst : ∀ clause ∈ st.clauses, ∀ lit ∈ clause, lit ≠ 0) (i : Fin 49) :
    ∀ clause ∈ (orderFortyNineDegreeBlockStep h st i).clauses,
      ∀ lit ∈ clause, lit ≠ 0 := by
  intro clause hclause
  simp only [orderFortyNineDegreeBlockStep, Array.mem_append] at hclause
  rcases hclause with hold | hnew
  · exact hst clause hold
  · exact seqCounterEqualsCore_nonzero st.top (orderFortyNineDimacsRow i)
      (orderFortyNineDimacsRow_getD_nonzero i) _ clause hnew

theorem orderFortyNineDegreeBlocksLoop_nonzero (h : Nat) :
    ∀ (rows : List (Fin 49)) (st : SeqCounterGenState),
      (∀ clause ∈ st.clauses, ∀ lit ∈ clause, lit ≠ 0) →
      ∀ clause ∈ (orderFortyNineDegreeBlocksLoop h rows st).clauses,
        ∀ lit ∈ clause, lit ≠ 0 := by
  intro rows
  induction rows with
  | nil => intro st hst; simpa [orderFortyNineDegreeBlocksLoop] using hst
  | cons i rest ih =>
      intro st hst
      simp only [orderFortyNineDegreeBlocksLoop]
      exact ih _ (orderFortyNineDegreeBlockStep_nonzero h hst i)

/-- The generated degree-counter blocks contain no literal `0`, for every
high count `h`.  Standard-axiom replacement for the former whole-formula
`decide`. -/
theorem orderFortyNineDegreeBlocks_nonzero_all (h : Nat) :
    ∀ clause ∈ (orderFortyNineDegreeBlocks h).clauses,
      ∀ lit ∈ clause, lit ≠ 0 := by
  unfold orderFortyNineDegreeBlocks
  apply orderFortyNineDegreeBlocksLoop_nonzero
  intro clause hclause
  simp at hclause

end Erdos85
