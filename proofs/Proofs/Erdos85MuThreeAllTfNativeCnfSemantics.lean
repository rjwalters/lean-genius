import Proofs.Erdos85MuThreeAllTfNativeCnf
import Proofs.Erdos85SequentialCounterReification

/-! # Semantic building blocks for the native all-triangle-free CNF

The executable generator stores a DIMACS prefix as `Mu3NativeCnfState`, while
the sequential-counter soundness library is phrased for a bare incoming top
and clause array.  The theorems below are the state-level adapters used by the
row/column and common-neighbor folds.  In particular, each adapter returns a
valuation which still agrees with the incoming valuation on every old ID.
-/

namespace Erdos85

/-- Add one exact-cardinality block to a satisfied native-generator prefix.
The returned canonical valuation satisfies the enlarged prefix, its clauses
are bounded by the new top, and all old variable values are unchanged. -/
theorem mu3NativeEquals_formulaSatisfied_append
    (st : Mu3NativeCnfState) (inputVal : DimacsValuation)
    (vars : Array Int) (x : Fin vars.size → Bool)
    (hprefixSat : dimacsFormulaSatisfied inputVal st.clauses)
    (hprefixBound : dimacsFormulaBounded st.top st.clauses)
    (hinput : SeqCounterInputReifies inputVal st.top vars x)
    (target : Nat) (hcount : seqPrefixTrue x vars.size = target) :
    let nextVal := seqCounterEqualsVal inputVal st.top vars x target
    dimacsFormulaSatisfied nextVal
      (mu3NativeEquals vars target st).clauses ∧
    dimacsFormulaBounded (mu3NativeEquals vars target st).top
      (mu3NativeEquals vars target st).clauses ∧
    ∀ id, id ≤ st.top → nextVal id = inputVal id := by
  simpa [mu3NativeEquals, mu3NativeAppendCounter] using
    seqCounterEqualsVal_formulaSatisfied_append inputVal st.top st.clauses
      vars x hprefixSat hprefixBound hinput target hcount

/-- Canonical valuation for an at-most block appended to an existing prefix. -/
def mu3NativeAtMostVal (st : Mu3NativeCnfState)
    (inputVal : DimacsValuation) (vars : Array Int)
    (x : Fin vars.size → Bool) (target : Nat) : DimacsValuation :=
  seqCounterBlockVal inputVal st.top x (seqCounterAtMost st.top vars target).ids

/-- Add one at-most-cardinality block to a satisfied native-generator prefix.
This is the C4 common-neighbor counter adapter. -/
theorem mu3NativeAtMost_formulaSatisfied_append
    (st : Mu3NativeCnfState) (inputVal : DimacsValuation)
    (vars : Array Int) (x : Fin vars.size → Bool)
    (hprefixSat : dimacsFormulaSatisfied inputVal st.clauses)
    (hprefixBound : dimacsFormulaBounded st.top st.clauses)
    (hinput : SeqCounterInputReifies inputVal st.top vars x)
    (target : Nat) (htotal : seqPrefixTrue x vars.size ≤ target) :
    let nextVal := mu3NativeAtMostVal st inputVal vars x target
    dimacsFormulaSatisfied nextVal
      (mu3NativeAtMost vars target st).clauses ∧
    dimacsFormulaBounded (mu3NativeAtMost vars target st).top
      (mu3NativeAtMost vars target st).clauses ∧
    ∀ id, id ≤ st.top → nextVal id = inputVal id := by
  let out := seqCounterAtMost st.top vars target
  let nextVal := mu3NativeAtMostVal st inputVal vars x target
  have hprefixNext : dimacsFormulaSatisfied nextVal st.clauses := by
    apply dimacsFormulaSatisfied_of_bounded_agree hprefixSat hprefixBound
    intro id hid
    exact (seqCounterBlockVal_input inputVal st.top x out.ids hid).symm
  have hblock : dimacsFormulaSatisfied nextVal out.clauses := by
    simpa [nextVal, mu3NativeAtMostVal, out] using
      seqCounterAtMost_formulaSatisfied inputVal st.top vars x hinput
        target htotal
  have htop : st.top ≤ out.top := by
    simpa [out] using seqCounterAtMost_top_bound st.top vars target
  have hprefixFinal : dimacsFormulaBounded out.top st.clauses :=
    dimacsFormulaBounded_mono htop hprefixBound
  have hblockBound : dimacsFormulaBounded out.top out.clauses := by
    simpa [out] using
      seqCounterAtMost_formulaBounded inputVal st.top vars x hinput target
  refine ⟨?_, ?_, ?_⟩
  · simpa [mu3NativeAtMost, mu3NativeAppendCounter, out, nextVal] using
      dimacsFormulaSatisfied_append hprefixNext hblock
  · simpa [mu3NativeAtMost, mu3NativeAppendCounter, out] using
      dimacsFormulaBounded_append hprefixFinal hblockBound
  · intro id hid
    simpa [nextVal, mu3NativeAtMostVal, out] using
      seqCounterBlockVal_input inputVal st.top x out.ids hid

/-! ## Fresh conjunction variables -/

/-- The three-clause Tseitin block used for every potential common neighbor. -/
def mu3NativeConjStep (a b : Nat)
    (st : Mu3NativeCnfState) : Nat × Mu3NativeCnfState :=
  let (aux, st) := mu3NativeFresh st
  let st := mu3NativeEmit [-((aux : Nat) : Int), (a : Int)] st
  let st := mu3NativeEmit [-((aux : Nat) : Int), (b : Int)] st
  let st := mu3NativeEmit [-((a : Nat) : Int), -((b : Nat) : Int),
    ((aux : Nat) : Int)] st
  (aux, st)

/-- Extend a valuation by setting the freshly allocated identifier to `a ∧ b`. -/
def mu3NativeConjVal (st : Mu3NativeCnfState)
    (inputVal : DimacsValuation) (a b : Nat) : DimacsValuation := fun id =>
  if id = st.top + 1 then inputVal a && inputVal b else inputVal id

private theorem mu3NativeConjVal_old
    (st : Mu3NativeCnfState) (inputVal : DimacsValuation) (a b id : Nat)
    (hid : id ≤ st.top) :
    mu3NativeConjVal st inputVal a b id = inputVal id := by
  simp [mu3NativeConjVal, Nat.ne_of_lt (lt_of_le_of_lt hid (Nat.lt_succ_self _))]

private theorem dimacsFormulaSatisfied_push_native
    {val : DimacsValuation} {clauses : Array DimacsClause}
    {clause : DimacsClause}
    (hprefix : dimacsFormulaSatisfied val clauses)
    (hclause : dimacsClauseSatisfied val clause) :
    dimacsFormulaSatisfied val (clauses.push clause) := by
  intro c hc
  rw [Array.mem_push] at hc
  rcases hc with hc | rfl
  · exact hprefix c hc
  · exact hclause

/-- Soundness of one explicit common-neighbor conjunction block. -/
theorem mu3NativeConjStep_formulaSatisfied_append
    (st : Mu3NativeCnfState) (inputVal : DimacsValuation) (a b : Nat)
    (ha : 0 < a) (haTop : a ≤ st.top)
    (hb : 0 < b) (hbTop : b ≤ st.top)
    (hprefixSat : dimacsFormulaSatisfied inputVal st.clauses)
    (hprefixBound : dimacsFormulaBounded st.top st.clauses) :
    let nextVal := mu3NativeConjVal st inputVal a b
    let out := mu3NativeConjStep a b st
    dimacsFormulaSatisfied nextVal out.2.clauses ∧
    dimacsFormulaBounded out.2.top out.2.clauses ∧
    out.1 = st.top + 1 ∧
    nextVal out.1 = (inputVal a && inputVal b) ∧
    ∀ id, id ≤ st.top → nextVal id = inputVal id := by
  let aux := st.top + 1
  let nextVal := mu3NativeConjVal st inputVal a b
  have hprefixNext : dimacsFormulaSatisfied nextVal st.clauses := by
    apply dimacsFormulaSatisfied_of_bounded_agree hprefixSat hprefixBound
    intro id hid
    exact (mu3NativeConjVal_old st inputVal a b id hid).symm
  have hca : dimacsClauseSatisfied nextVal [-((aux : Nat) : Int), (a : Int)] := by
    by_cases hA : inputVal a = true
    · refine ⟨(a : Int), by simp, ?_⟩
      rw [dimacsLitValue_natCast nextVal ha]
      dsimp [nextVal]
      rw [mu3NativeConjVal_old st inputVal a b a haTop, hA]
    · refine ⟨-((aux : Nat) : Int), by simp, ?_⟩
      rw [dimacsLitValue_neg nextVal (by exact_mod_cast (Nat.succ_ne_zero st.top))]
      rw [dimacsLitValue_natCast nextVal (by omega)]
      simp [nextVal, mu3NativeConjVal, aux, Bool.and_eq_true, hA]
  have hcb : dimacsClauseSatisfied nextVal [-((aux : Nat) : Int), (b : Int)] := by
    by_cases hB : inputVal b = true
    · refine ⟨(b : Int), by simp, ?_⟩
      rw [dimacsLitValue_natCast nextVal hb]
      dsimp [nextVal]
      rw [mu3NativeConjVal_old st inputVal a b b hbTop, hB]
    · refine ⟨-((aux : Nat) : Int), by simp, ?_⟩
      rw [dimacsLitValue_neg nextVal (by exact_mod_cast (Nat.succ_ne_zero st.top))]
      rw [dimacsLitValue_natCast nextVal (by omega)]
      simp [nextVal, mu3NativeConjVal, aux, Bool.and_eq_true, hB]
  have hcand : dimacsClauseSatisfied nextVal
      [-((a : Nat) : Int), -((b : Nat) : Int), ((aux : Nat) : Int)] := by
    by_cases hA : inputVal a = true
    · by_cases hB : inputVal b = true
      · refine ⟨(aux : Int), by simp, ?_⟩
        rw [dimacsLitValue_natCast nextVal (by omega)]
        simp [nextVal, mu3NativeConjVal, aux, hA, hB]
      · refine ⟨-((b : Nat) : Int), by simp, ?_⟩
        rw [dimacsLitValue_neg nextVal (by exact_mod_cast hb.ne')]
        rw [dimacsLitValue_natCast nextVal hb]
        dsimp [nextVal]
        rw [mu3NativeConjVal_old st inputVal a b b hbTop]
        cases hv : inputVal b <;> simp_all
    · refine ⟨-((a : Nat) : Int), by simp, ?_⟩
      rw [dimacsLitValue_neg nextVal (by exact_mod_cast ha.ne')]
      rw [dimacsLitValue_natCast nextVal ha]
      dsimp [nextVal]
      rw [mu3NativeConjVal_old st inputVal a b a haTop]
      cases hv : inputVal a <;> simp_all
  have hsat1 := dimacsFormulaSatisfied_push_native hprefixNext hca
  have hsat2 := dimacsFormulaSatisfied_push_native hsat1 hcb
  have hsat3 := dimacsFormulaSatisfied_push_native hsat2 hcand
  have htop : (mu3NativeConjStep a b st).2.top = aux := by
    simp [mu3NativeConjStep, mu3NativeFresh, mu3NativeEmit, aux]
  have hbound : dimacsFormulaBounded aux
      (mu3NativeConjStep a b st).2.clauses := by
    intro clause hclause lit hlit
    simp [mu3NativeConjStep, mu3NativeFresh, mu3NativeEmit,
      Array.mem_push] at hclause
    rcases hclause with ((hclause | rfl) | rfl) | rfl
    · exact (hprefixBound clause hclause lit hlit).trans (Nat.le_succ _)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hlit
      rcases hlit with rfl | rfl <;> simp [aux, Int.natAbs_neg] <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hlit
      rcases hlit with rfl | rfl <;> simp [aux, Int.natAbs_neg] <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hlit
      rcases hlit with rfl | rfl | rfl <;>
        simp [aux, Int.natAbs_neg] <;> omega
  refine ⟨?_, htop ▸ hbound, ?_, ?_, ?_⟩
  · change dimacsFormulaSatisfied nextVal
      (((st.clauses.push [-((aux : Nat) : Int), (a : Int)]).push
        [-((aux : Nat) : Int), (b : Int)]).push
        [-((a : Nat) : Int), -((b : Nat) : Int), ((aux : Nat) : Int)])
    exact hsat3
  · simp [mu3NativeConjStep, mu3NativeFresh, aux]
  · simp [nextVal, mu3NativeConjVal, mu3NativeConjStep,
      mu3NativeFresh, aux]
  · intro id hid
    exact mu3NativeConjVal_old st inputVal a b id hid

end Erdos85
