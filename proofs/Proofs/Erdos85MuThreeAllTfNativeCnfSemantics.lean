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

abbrev Mu3NativeCardSpec := Array Int × Nat

/-- The row and column exact-cardinality blocks, flattened in precisely the
same order as `mu3NativeHitBlocks`. -/
def mu3NativeHitSpecs (shape : Mu3AllTfShape) : List Mu3NativeCardSpec :=
  (List.range 48).flatMap fun u =>
    let cell := (mu3AllTfCells shape).getD u 0
    let xu := cell / 8
    let yu := cell % 8
    (List.range 8).map (fun x =>
      (mu3NativeRowVars shape u x,
        if mu3AllTfInternal shape x yu then 0 else 1)) ++
    (List.range 8).map (fun y =>
      (mu3NativeColumnVars shape u y,
        if mu3AllTfInternal shape xu y then 0 else 1))

def mu3NativeRunExactSpecs (specs : List Mu3NativeCardSpec)
    (st : Mu3NativeCnfState) : Mu3NativeCnfState :=
  specs.foldl (fun st spec => mu3NativeEquals spec.1 spec.2 st) st

set_option maxRecDepth 100000 in
theorem mu3NativeHitSpecs_generate_hitBlocks :
    ([Mu3AllTfShape.c16, .c10c6, .c8c8].all fun shape =>
      mu3NativeRunExactSpecs (mu3NativeHitSpecs shape) {} ==
        mu3NativeHitBlocks shape) = true := by
  native_decide

/-- The Boolean row denoted by a signed DIMACS literal array. -/
def mu3NativeVarsRow (val : DimacsValuation) (vars : Array Int) :
    Fin vars.size → Bool := fun i => dimacsLitValue val vars[i]

theorem mu3NativeVarsRow_reifies
    (val : DimacsValuation) (top : Nat) (vars : Array Int)
    (hnonzero : ∀ lit ∈ vars, lit ≠ 0)
    (hbounded : ∀ lit ∈ vars, lit.natAbs ≤ top) :
    SeqCounterInputReifies val top vars (mu3NativeVarsRow val vars) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro i hi
    apply hnonzero (vars.getD i 0)
    simp [Array.getD, hi]
  · intro i hi
    apply hbounded (vars.getD i 0)
    simp [Array.getD, hi]
  · intro i hi
    simp [mu3NativeVarsRow, Array.getD, hi]

/-- Run exact-cardinality blocks while constructing their canonical auxiliary
valuation.  The first projection is definitionally the executable CNF run. -/
def mu3NativeRunExactSpecsVal (baseVal : DimacsValuation) :
    List Mu3NativeCardSpec → Mu3NativeCnfState → DimacsValuation →
      Mu3NativeCnfState × DimacsValuation
  | [], st, val => (st, val)
  | spec :: rest, st, val =>
      let x := mu3NativeVarsRow baseVal spec.1
      let nextVal := seqCounterEqualsVal val st.top spec.1 x spec.2
      mu3NativeRunExactSpecsVal baseVal rest
        (mu3NativeEquals spec.1 spec.2 st) nextVal

theorem mu3NativeRunExactSpecsVal_state
    (baseVal : DimacsValuation) (specs : List Mu3NativeCardSpec)
    (st : Mu3NativeCnfState) (val : DimacsValuation) :
    (mu3NativeRunExactSpecsVal baseVal specs st val).1 =
      mu3NativeRunExactSpecs specs st := by
  induction specs generalizing st val with
  | nil => rfl
  | cons spec rest ih =>
      simp only [mu3NativeRunExactSpecsVal, mu3NativeRunExactSpecs,
        List.foldl_cons]
      exact ih _ _

/-- Semantic induction for a list of exact-cardinality blocks whose inputs
all lie in a fixed base-ID range. -/
theorem mu3NativeRunExactSpecsVal_formulaSatisfied
    (baseTop : Nat) (baseVal : DimacsValuation)
    (specs : List Mu3NativeCardSpec)
    (st : Mu3NativeCnfState) (inputVal : DimacsValuation)
    (htop : baseTop ≤ st.top)
    (hprefixSat : dimacsFormulaSatisfied inputVal st.clauses)
    (hprefixBound : dimacsFormulaBounded st.top st.clauses)
    (hagree : ∀ id, id ≤ baseTop → inputVal id = baseVal id)
    (hnonzero : ∀ spec ∈ specs, ∀ lit ∈ spec.1, lit ≠ 0)
    (hbaseBound : ∀ spec ∈ specs, ∀ lit ∈ spec.1,
      lit.natAbs ≤ baseTop)
    (hcounts : ∀ spec ∈ specs,
      seqPrefixTrue (mu3NativeVarsRow baseVal spec.1) spec.1.size = spec.2) :
    let out := mu3NativeRunExactSpecsVal baseVal specs st inputVal
    dimacsFormulaSatisfied out.2 out.1.clauses ∧
    dimacsFormulaBounded out.1.top out.1.clauses ∧
    baseTop ≤ out.1.top ∧
    ∀ id, id ≤ baseTop → out.2 id = baseVal id := by
  induction specs generalizing st inputVal with
  | nil =>
      exact ⟨hprefixSat, hprefixBound, htop, hagree⟩
  | cons spec rest ih =>
      let x := mu3NativeVarsRow baseVal spec.1
      let nextSt := mu3NativeEquals spec.1 spec.2 st
      let nextVal := seqCounterEqualsVal inputVal st.top spec.1 x spec.2
      have hspecNonzero : ∀ lit ∈ spec.1, lit ≠ 0 := by
        intro lit hlit
        exact hnonzero spec (by simp) lit hlit
      have hspecBaseBound : ∀ lit ∈ spec.1, lit.natAbs ≤ baseTop := by
        intro lit hlit
        exact hbaseBound spec (by simp) lit hlit
      have hinput : SeqCounterInputReifies inputVal st.top spec.1 x := by
        refine ⟨rfl, ?_, ?_, ?_⟩
        · intro i hi
          apply hspecNonzero (spec.1.getD i 0)
          simp [Array.getD, hi]
        · intro i hi
          exact (hspecBaseBound (spec.1.getD i 0)
            (by simp [Array.getD, hi])).trans htop
        · intro i hi
          change dimacsLitValue inputVal (spec.1.getD i 0) =
            dimacsLitValue baseVal spec.1[⟨i, hi⟩]
          have hlit := hspecBaseBound (spec.1.getD i 0)
            (by simp [Array.getD, hi])
          rw [dimacsLitValue_eq_of_agree inputVal baseVal
            (hagree _ hlit)]
          simp [Array.getD, hi]
      have hcount : seqPrefixTrue x spec.1.size = spec.2 := by
        exact hcounts spec (by simp)
      have hstep := mu3NativeEquals_formulaSatisfied_append st inputVal
        spec.1 x hprefixSat hprefixBound hinput spec.2 hcount
      have hstepSat : dimacsFormulaSatisfied nextVal nextSt.clauses := by
        simpa [nextVal, nextSt] using hstep.1
      have hstepBound : dimacsFormulaBounded nextSt.top nextSt.clauses := by
        simpa [nextSt] using hstep.2.1
      have hnextTop : baseTop ≤ nextSt.top := by
        exact htop.trans (by
          simpa [nextSt, mu3NativeEquals, mu3NativeAppendCounter] using
            seqCounterEquals_top_bound st.top spec.1 spec.2)
      have hnextAgree : ∀ id, id ≤ baseTop → nextVal id = baseVal id := by
        intro id hid
        rw [show nextVal id = inputVal id by
          exact hstep.2.2 id (hid.trans htop)]
        exact hagree id hid
      have hrestNonzero : ∀ s ∈ rest, ∀ lit ∈ s.1, lit ≠ 0 := by
        intro s hs
        exact hnonzero s (by simp [hs])
      have hrestBound : ∀ s ∈ rest, ∀ lit ∈ s.1,
          lit.natAbs ≤ baseTop := by
        intro s hs
        exact hbaseBound s (by simp [hs])
      have hrestCounts : ∀ s ∈ rest,
          seqPrefixTrue (mu3NativeVarsRow baseVal s.1) s.1.size = s.2 := by
        intro s hs
        exact hcounts s (by simp [hs])
      simpa [mu3NativeRunExactSpecsVal, x, nextSt, nextVal] using
        ih nextSt nextVal hnextTop hstepSat hstepBound hnextAgree
          hrestNonzero hrestBound hrestCounts

/-- The complete row/column hit prefix has a satisfying valuation as soon as
its base edge assignment has the specified exact counts.  The two elementary
ID-side hypotheses are separated so they can be discharged once for the
fixed native edge enumeration. -/
theorem mu3NativeHitSpecs_formulaSatisfiable
    (shape : Mu3AllTfShape) (edgeVal : DimacsValuation)
    (hnonzero : ∀ spec ∈ mu3NativeHitSpecs shape,
      ∀ lit ∈ spec.1, lit ≠ 0)
    (hbaseBound : ∀ spec ∈ mu3NativeHitSpecs shape,
      ∀ lit ∈ spec.1, lit.natAbs ≤ 1128)
    (hcounts : ∀ spec ∈ mu3NativeHitSpecs shape,
      seqPrefixTrue (mu3NativeVarsRow edgeVal spec.1) spec.1.size = spec.2) :
    ∃ val,
      dimacsFormulaSatisfied val
        (mu3NativeRunExactSpecs (mu3NativeHitSpecs shape) {}).clauses ∧
      dimacsFormulaBounded
        (mu3NativeRunExactSpecs (mu3NativeHitSpecs shape) {}).top
        (mu3NativeRunExactSpecs (mu3NativeHitSpecs shape) {}).clauses ∧
      ∀ id, id ≤ 1128 → val id = edgeVal id := by
  let out := mu3NativeRunExactSpecsVal edgeVal
    (mu3NativeHitSpecs shape) {} edgeVal
  have h := mu3NativeRunExactSpecsVal_formulaSatisfied
    1128 edgeVal (mu3NativeHitSpecs shape) {} edgeVal
    (by rfl) (dimacsFormulaSatisfied_empty edgeVal)
    (dimacsFormulaBounded_empty 1128) (by simp)
    hnonzero hbaseBound hcounts
  refine ⟨out.2, ?_, ?_, h.2.2.2⟩
  · rw [← mu3NativeRunExactSpecsVal_state edgeVal
      (mu3NativeHitSpecs shape) {} edgeVal]
    exact h.1
  · rw [← mu3NativeRunExactSpecsVal_state edgeVal
      (mu3NativeHitSpecs shape) {} edgeVal]
    exact h.2.1

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
