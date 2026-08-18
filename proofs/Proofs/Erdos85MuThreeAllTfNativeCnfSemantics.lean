import Proofs.Erdos85MuThreeAllTfNativeCnf
import Proofs.Erdos85MuThreeAllTfNativeCertificates
import Proofs.Erdos85SequentialCounterReification

/-! # Semantic building blocks for the native all-triangle-free CNF

The executable generator stores a DIMACS prefix as `Mu3NativeCnfState`, while
the sequential-counter soundness library is phrased for a bare incoming top
and clause array.  The theorems below are the state-level adapters used by the
row/column and common-neighbor folds.  In particular, each adapter returns a
valuation which still agrees with the incoming valuation on every old ID.
-/

namespace Erdos85

set_option maxRecDepth 100000

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
            dimacsLitValue baseVal spec.1[i]
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

/-! ## Common-neighbor conjunction folds -/

/-- The 46 pairs of base edge IDs whose conjunctions encode common neighbors
of `u` and `v`. -/
def mu3NativeCommonSpecs (u v : Nat) : List (Nat × Nat) :=
  (List.range 48).filterMap fun m =>
    if m = u || m = v then none
    else some (mu3NativeEdgeId u m, mu3NativeEdgeId v m)

def mu3NativeRunConjSpecs (specs : List (Nat × Nat))
    (acc : Array Int × Mu3NativeCnfState) :
    Array Int × Mu3NativeCnfState :=
  specs.foldl (fun acc spec =>
    let out := mu3NativeConjStep spec.1 spec.2 acc.2
    (acc.1.push (out.1 : Int), out.2)) acc

set_option maxRecDepth 100000 in
theorem mu3NativeCommonSpecs_generate_commonFold :
    (mu3NativePairs.all fun pair =>
      mu3NativeRunConjSpecs (mu3NativeCommonSpecs pair.1 pair.2)
        (#[], {}) ==
      (List.range 48).foldl
        (fun acc m => mu3NativeCommonStep pair.1 pair.2 m acc)
        (#[], {})) = true := by
  native_decide

/-- Semantic execution of the common-neighbor conjunction list. -/
def mu3NativeRunConjSpecsVal (baseVal : DimacsValuation) :
    List (Nat × Nat) → Array Int × Mu3NativeCnfState →
      DimacsValuation → (Array Int × Mu3NativeCnfState) × DimacsValuation
  | [], acc, val => (acc, val)
  | spec :: rest, acc, val =>
      let out := mu3NativeConjStep spec.1 spec.2 acc.2
      let nextAcc := (acc.1.push (out.1 : Int), out.2)
      let nextVal := mu3NativeConjVal acc.2 val spec.1 spec.2
      mu3NativeRunConjSpecsVal baseVal rest nextAcc nextVal

theorem mu3NativeRunConjSpecsVal_state
    (baseVal : DimacsValuation) (specs : List (Nat × Nat))
    (acc : Array Int × Mu3NativeCnfState) (val : DimacsValuation) :
    (mu3NativeRunConjSpecsVal baseVal specs acc val).1 =
      mu3NativeRunConjSpecs specs acc := by
  induction specs generalizing acc val with
  | nil => rfl
  | cons spec rest ih =>
      simp only [mu3NativeRunConjSpecsVal, mu3NativeRunConjSpecs,
        List.foldl_cons]
      exact ih _ _

/-- The truth row for a conjunction specification list, independent of the
fresh numeric IDs allocated to represent it. -/
def mu3NativeCommonTruthRow (baseVal : DimacsValuation)
    (specs : List (Nat × Nat)) : Fin specs.length → Bool := fun i =>
  baseVal specs[i].1 && baseVal specs[i].2

/-- Semantic induction through a list of freshly allocated conjunctions. -/
theorem mu3NativeRunConjSpecsVal_formulaSatisfied
    (baseTop : Nat) (baseVal : DimacsValuation)
    (specs : List (Nat × Nat))
    (acc : Array Int × Mu3NativeCnfState) (inputVal : DimacsValuation)
    (htop : baseTop ≤ acc.2.top)
    (hprefixSat : dimacsFormulaSatisfied inputVal acc.2.clauses)
    (hprefixBound : dimacsFormulaBounded acc.2.top acc.2.clauses)
    (hagree : ∀ id, id ≤ baseTop → inputVal id = baseVal id)
    (haccIds : ∀ lit ∈ acc.1,
      lit ≠ 0 ∧ lit.natAbs ≤ acc.2.top)
    (hspecIds : ∀ spec ∈ specs,
      0 < spec.1 ∧ spec.1 ≤ baseTop ∧
      0 < spec.2 ∧ spec.2 ≤ baseTop) :
    let out := mu3NativeRunConjSpecsVal baseVal specs acc inputVal
    dimacsFormulaSatisfied out.2 out.1.2.clauses ∧
    dimacsFormulaBounded out.1.2.top out.1.2.clauses ∧
    baseTop ≤ out.1.2.top ∧
    (∀ id, id ≤ baseTop → out.2 id = baseVal id) ∧
    ∀ lit ∈ out.1.1, lit ≠ 0 ∧ lit.natAbs ≤ out.1.2.top := by
  induction specs generalizing acc inputVal with
  | nil =>
      exact ⟨hprefixSat, hprefixBound, htop, hagree, haccIds⟩
  | cons spec rest ih =>
      let step := mu3NativeConjStep spec.1 spec.2 acc.2
      let nextAcc : Array Int × Mu3NativeCnfState :=
        (acc.1.push (step.1 : Int), step.2)
      let nextVal := mu3NativeConjVal acc.2 inputVal spec.1 spec.2
      have hspec := hspecIds spec (by simp)
      have hstep := mu3NativeConjStep_formulaSatisfied_append
        acc.2 inputVal spec.1 spec.2 hspec.1 (hspec.2.1.trans htop)
          hspec.2.2.1 (hspec.2.2.2.trans htop) hprefixSat hprefixBound
      have hstepSat : dimacsFormulaSatisfied nextVal nextAcc.2.clauses := by
        simpa [nextVal, nextAcc, step] using hstep.1
      have hstepBound : dimacsFormulaBounded nextAcc.2.top
          nextAcc.2.clauses := by
        simpa [nextAcc, step] using hstep.2.1
      have hnextTopEq : nextAcc.2.top = acc.2.top + 1 := by
        simp [nextAcc, step, mu3NativeConjStep, mu3NativeFresh,
          mu3NativeEmit]
      have hnextTop : baseTop ≤ nextAcc.2.top := by
        rw [hnextTopEq]
        omega
      have hnextAgree : ∀ id, id ≤ baseTop → nextVal id = baseVal id := by
        intro id hid
        rw [show nextVal id = inputVal id by
          simpa [nextVal] using hstep.2.2.2.2 id (hid.trans htop)]
        exact hagree id hid
      have hnextIds : ∀ lit ∈ nextAcc.1,
          lit ≠ 0 ∧ lit.natAbs ≤ nextAcc.2.top := by
        intro lit hlit
        simp only [nextAcc, Array.mem_push] at hlit
        rcases hlit with hold | rfl
        · obtain ⟨hne, hb⟩ := haccIds lit hold
          exact ⟨hne, hb.trans (by rw [hnextTopEq]; omega)⟩
        · have haux : step.1 = acc.2.top + 1 := by
            simpa [step] using hstep.2.2.1
          rw [haux]
          constructor
          · exact_mod_cast Nat.succ_ne_zero acc.2.top
          · change acc.2.top + 1 ≤ nextAcc.2.top
            rw [hnextTopEq]
      have hrestIds : ∀ s ∈ rest,
          0 < s.1 ∧ s.1 ≤ baseTop ∧ 0 < s.2 ∧ s.2 ≤ baseTop := by
        intro s hs
        exact hspecIds s (by simp [hs])
      simpa [mu3NativeRunConjSpecsVal, step, nextAcc, nextVal] using
        ih nextAcc nextVal hnextTop hstepSat hstepBound hnextAgree
          hnextIds hrestIds

/-! ## One complete C4-pair block -/

def mu3NativeC4PairSpecStep (pair : Nat × Nat)
    (st : Mu3NativeCnfState) : Mu3NativeCnfState :=
  let conj := mu3NativeRunConjSpecs
    (mu3NativeCommonSpecs pair.1 pair.2) (#[], st)
  mu3NativeAtMost conj.1 1 conj.2

def mu3NativeC4PairSpecStepVal (baseVal : DimacsValuation)
    (pair : Nat × Nat) (st : Mu3NativeCnfState)
    (inputVal : DimacsValuation) : Mu3NativeCnfState × DimacsValuation :=
  let conj := mu3NativeRunConjSpecsVal baseVal
    (mu3NativeCommonSpecs pair.1 pair.2) (#[], st) inputVal
  let x := mu3NativeVarsRow conj.2 conj.1.1
  (mu3NativeAtMost conj.1.1 1 conj.1.2,
    mu3NativeAtMostVal conj.1.2 conj.2 conj.1.1 x 1)

theorem mu3NativeC4PairSpecStepVal_state
    (baseVal : DimacsValuation) (pair : Nat × Nat)
    (st : Mu3NativeCnfState) (inputVal : DimacsValuation) :
    (mu3NativeC4PairSpecStepVal baseVal pair st inputVal).1 =
      mu3NativeC4PairSpecStep pair st := by
  simp only [mu3NativeC4PairSpecStepVal, mu3NativeC4PairSpecStep]
  rw [mu3NativeRunConjSpecsVal_state]

/-- Semantic soundness of one vertex-pair block.  `hcommon` is exactly the
C4-free condition on the freshly reified common-neighbor row. -/
theorem mu3NativeC4PairSpecStepVal_formulaSatisfied
    (baseTop : Nat) (baseVal : DimacsValuation)
    (pair : Nat × Nat) (st : Mu3NativeCnfState)
    (inputVal : DimacsValuation)
    (htop : baseTop ≤ st.top)
    (hprefixSat : dimacsFormulaSatisfied inputVal st.clauses)
    (hprefixBound : dimacsFormulaBounded st.top st.clauses)
    (hagree : ∀ id, id ≤ baseTop → inputVal id = baseVal id)
    (hspecIds : ∀ spec ∈ mu3NativeCommonSpecs pair.1 pair.2,
      0 < spec.1 ∧ spec.1 ≤ baseTop ∧
      0 < spec.2 ∧ spec.2 ≤ baseTop)
    (hcommon :
      let conj := mu3NativeRunConjSpecsVal baseVal
        (mu3NativeCommonSpecs pair.1 pair.2) (#[], st) inputVal
      seqPrefixTrue (mu3NativeVarsRow conj.2 conj.1.1) conj.1.1.size ≤ 1) :
    let out := mu3NativeC4PairSpecStepVal baseVal pair st inputVal
    dimacsFormulaSatisfied out.2 out.1.clauses ∧
    dimacsFormulaBounded out.1.top out.1.clauses ∧
    baseTop ≤ out.1.top ∧
    ∀ id, id ≤ baseTop → out.2 id = baseVal id := by
  let conj := mu3NativeRunConjSpecsVal baseVal
    (mu3NativeCommonSpecs pair.1 pair.2) (#[], st) inputVal
  let x := mu3NativeVarsRow conj.2 conj.1.1
  let out := mu3NativeC4PairSpecStepVal baseVal pair st inputVal
  have hconj := mu3NativeRunConjSpecsVal_formulaSatisfied
    baseTop baseVal (mu3NativeCommonSpecs pair.1 pair.2) (#[], st) inputVal
    htop hprefixSat hprefixBound hagree (by simp) hspecIds
  have hinput : SeqCounterInputReifies conj.2 conj.1.2.top conj.1.1 x := by
    apply mu3NativeVarsRow_reifies
    · intro lit hlit
      exact (hconj.2.2.2.2 lit hlit).1
    · intro lit hlit
      exact (hconj.2.2.2.2 lit hlit).2
  have hstep := mu3NativeAtMost_formulaSatisfied_append
    conj.1.2 conj.2 conj.1.1 x hconj.1 hconj.2.1 hinput 1 hcommon
  have houtState : out.1 = mu3NativeAtMost conj.1.1 1 conj.1.2 := by
    simp [out, mu3NativeC4PairSpecStepVal, conj]
  have houtVal : out.2 = mu3NativeAtMostVal conj.1.2 conj.2 conj.1.1 x 1 := by
    simp [out, mu3NativeC4PairSpecStepVal, conj, x]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [houtState, houtVal]
    exact hstep.1
  · rw [houtState]
    exact hstep.2.1
  · rw [houtState]
    exact hconj.2.2.1.trans
      (by simpa [mu3NativeAtMost, mu3NativeAppendCounter] using
        seqCounterAtMost_top_bound conj.1.2.top conj.1.1 1)
  · intro id hid
    rw [houtVal, show mu3NativeAtMostVal conj.1.2 conj.2 conj.1.1 x 1 id =
        conj.2 id by exact hstep.2.2 id (hid.trans hconj.2.2.1)]
    exact hconj.2.2.2.1 id hid

/-! ## The complete C4-pair fold -/

def mu3NativeRunC4PairSpecs (pairs : List (Nat × Nat))
    (st : Mu3NativeCnfState) : Mu3NativeCnfState :=
  pairs.foldl (fun st pair => mu3NativeC4PairSpecStep pair st) st

def mu3NativeRunC4PairSpecsVal (baseVal : DimacsValuation) :
    List (Nat × Nat) → Mu3NativeCnfState → DimacsValuation →
      Mu3NativeCnfState × DimacsValuation
  | [], st, val => (st, val)
  | pair :: rest, st, val =>
      let next := mu3NativeC4PairSpecStepVal baseVal pair st val
      mu3NativeRunC4PairSpecsVal baseVal rest next.1 next.2

theorem mu3NativeRunC4PairSpecsVal_state
    (baseVal : DimacsValuation) (pairs : List (Nat × Nat))
    (st : Mu3NativeCnfState) (val : DimacsValuation) :
    (mu3NativeRunC4PairSpecsVal baseVal pairs st val).1 =
      mu3NativeRunC4PairSpecs pairs st := by
  induction pairs generalizing st val with
  | nil => rfl
  | cons pair rest ih =>
      simp only [mu3NativeRunC4PairSpecsVal, mu3NativeRunC4PairSpecs,
        List.foldl_cons]
      rw [ih, mu3NativeC4PairSpecStepVal_state]
      rfl

/-- The stage-indexed hypotheses needed by the outer semantic fold.  This
form makes explicit that each at-most-one row is read after allocating its
own conjunction variables. -/
def Mu3NativeC4FoldConditions (baseTop : Nat)
    (baseVal : DimacsValuation) :
    List (Nat × Nat) → Mu3NativeCnfState → DimacsValuation → Prop
  | [], _, _ => True
  | pair :: rest, st, val =>
      (∀ spec ∈ mu3NativeCommonSpecs pair.1 pair.2,
        0 < spec.1 ∧ spec.1 ≤ baseTop ∧
        0 < spec.2 ∧ spec.2 ≤ baseTop) ∧
      (let conj := mu3NativeRunConjSpecsVal baseVal
          (mu3NativeCommonSpecs pair.1 pair.2) (#[], st) val;
        seqPrefixTrue (mu3NativeVarsRow conj.2 conj.1.1) conj.1.1.size ≤ 1) ∧
      let next := mu3NativeC4PairSpecStepVal baseVal pair st val
      Mu3NativeC4FoldConditions baseTop baseVal rest next.1 next.2

theorem mu3NativeRunC4PairSpecsVal_formulaSatisfied
    (baseTop : Nat) (baseVal : DimacsValuation)
    (pairs : List (Nat × Nat))
    (st : Mu3NativeCnfState) (inputVal : DimacsValuation)
    (htop : baseTop ≤ st.top)
    (hprefixSat : dimacsFormulaSatisfied inputVal st.clauses)
    (hprefixBound : dimacsFormulaBounded st.top st.clauses)
    (hagree : ∀ id, id ≤ baseTop → inputVal id = baseVal id)
    (hconditions : Mu3NativeC4FoldConditions
      baseTop baseVal pairs st inputVal) :
    let out := mu3NativeRunC4PairSpecsVal baseVal pairs st inputVal
    dimacsFormulaSatisfied out.2 out.1.clauses ∧
    dimacsFormulaBounded out.1.top out.1.clauses ∧
    baseTop ≤ out.1.top ∧
    ∀ id, id ≤ baseTop → out.2 id = baseVal id := by
  induction pairs generalizing st inputVal with
  | nil => exact ⟨hprefixSat, hprefixBound, htop, hagree⟩
  | cons pair rest ih =>
      let next := mu3NativeC4PairSpecStepVal baseVal pair st inputVal
      have hstep := mu3NativeC4PairSpecStepVal_formulaSatisfied
        baseTop baseVal pair st inputVal htop hprefixSat hprefixBound hagree
          hconditions.1 hconditions.2.1
      simpa [mu3NativeRunC4PairSpecsVal, next] using
        ih next.1 next.2 hstep.2.2.1 hstep.1 hstep.2.1 hstep.2.2.2
          hconditions.2.2

def mu3NativeFinalSpecState (shape : Mu3AllTfShape) : Mu3NativeCnfState :=
  mu3NativeRunC4PairSpecs mu3NativePairs
    (mu3NativeRunExactSpecs (mu3NativeHitSpecs shape) {})

set_option maxHeartbeats 0 in
theorem mu3NativeFinalSpecState_eq_finalState :
    ([Mu3AllTfShape.c16, .c10c6, .c8c8].all fun shape =>
      mu3NativeFinalSpecState shape == mu3NativeFinalState shape) = true := by
  native_decide

theorem mu3NativeFinalSpecState_eq_finalState_of_shape
    (shape : Mu3AllTfShape) :
    mu3NativeFinalSpecState shape = mu3NativeFinalState shape := by
  cases shape <;> native_decide

def mu3NativeHitSpecVal (shape : Mu3AllTfShape)
    (edgeVal : DimacsValuation) : Mu3NativeCnfState × DimacsValuation :=
  mu3NativeRunExactSpecsVal edgeVal (mu3NativeHitSpecs shape) {} edgeVal

def mu3NativeFinalSpecVal (shape : Mu3AllTfShape)
    (edgeVal : DimacsValuation) : Mu3NativeCnfState × DimacsValuation :=
  let hit := mu3NativeHitSpecVal shape edgeVal
  mu3NativeRunC4PairSpecsVal edgeVal mu3NativePairs hit.1 hit.2

/-- Generator-level semantic capstone: exact hit counts plus every C4
at-most-one condition construct a valuation satisfying the certificate CNF. -/
theorem mu3NativeFinalState_formulaSatisfiable
    (shape : Mu3AllTfShape) (edgeVal : DimacsValuation)
    (hhitNonzero : ∀ spec ∈ mu3NativeHitSpecs shape,
      ∀ lit ∈ spec.1, lit ≠ 0)
    (hhitBound : ∀ spec ∈ mu3NativeHitSpecs shape,
      ∀ lit ∈ spec.1, lit.natAbs ≤ 1128)
    (hhitCounts : ∀ spec ∈ mu3NativeHitSpecs shape,
      seqPrefixTrue (mu3NativeVarsRow edgeVal spec.1) spec.1.size = spec.2)
    (hc4 :
      let hit := mu3NativeHitSpecVal shape edgeVal
      Mu3NativeC4FoldConditions 1128 edgeVal mu3NativePairs hit.1 hit.2) :
    ∃ val, dimacsFormulaSatisfied val (mu3NativeFinalState shape).clauses := by
  let hit := mu3NativeHitSpecVal shape edgeVal
  have hhit := mu3NativeRunExactSpecsVal_formulaSatisfied
    1128 edgeVal (mu3NativeHitSpecs shape) {} edgeVal
    (by rfl) (dimacsFormulaSatisfied_empty edgeVal)
    (dimacsFormulaBounded_empty 1128) (by simp)
    hhitNonzero hhitBound hhitCounts
  have hfinal := mu3NativeRunC4PairSpecsVal_formulaSatisfied
    1128 edgeVal mu3NativePairs hit.1 hit.2 hhit.2.2.1
      hhit.1 hhit.2.1 hhit.2.2.2 hc4
  refine ⟨(mu3NativeFinalSpecVal shape edgeVal).2, ?_⟩
  rw [← mu3NativeFinalSpecState_eq_finalState_of_shape shape,
    show mu3NativeFinalSpecState shape =
      (mu3NativeFinalSpecVal shape edgeVal).1 by
        rw [mu3NativeFinalSpecVal, mu3NativeFinalSpecState,
          mu3NativeRunC4PairSpecsVal_state]
        apply congrArg (mu3NativeRunC4PairSpecs mu3NativePairs)
        exact (mu3NativeRunExactSpecsVal_state edgeVal
          (mu3NativeHitSpecs shape) {} edgeVal).symm]
  exact hfinal.1

theorem mu3AllTfNativeSatCnf_satisfiable
    (shape : Mu3AllTfShape) (edgeVal : DimacsValuation)
    (hnz : ∀ clause ∈ (mu3NativeFinalState shape).clauses,
      DimacsClauseNonzero clause)
    (hhitNonzero : ∀ spec ∈ mu3NativeHitSpecs shape,
      ∀ lit ∈ spec.1, lit ≠ 0)
    (hhitBound : ∀ spec ∈ mu3NativeHitSpecs shape,
      ∀ lit ∈ spec.1, lit.natAbs ≤ 1128)
    (hhitCounts : ∀ spec ∈ mu3NativeHitSpecs shape,
      seqPrefixTrue (mu3NativeVarsRow edgeVal spec.1) spec.1.size = spec.2)
    (hc4 :
      let hit := mu3NativeHitSpecVal shape edgeVal
      Mu3NativeC4FoldConditions 1128 edgeVal mu3NativePairs hit.1 hit.2) :
    ∃ assignment, (mu3AllTfNativeSatCnf shape).Sat assignment := by
  obtain ⟨val, hsat⟩ := mu3NativeFinalState_formulaSatisfiable
    shape edgeVal hhitNonzero hhitBound hhitCounts hc4
  refine ⟨satAssignmentOfDimacs val, ?_⟩
  exact satCnf_of_dimacsFormulaSatisfied
    hsat hnz

/-- Certificate-facing contradiction endpoint.  All generator semantics are
above this boundary; only the selected shape's checked LRAT theorem enters
here. -/
theorem false_of_mu3AllTfNativeConstraints
    (shape : Mu3AllTfShape) (edgeVal : DimacsValuation)
    (hnz : ∀ clause ∈ (mu3NativeFinalState shape).clauses,
      DimacsClauseNonzero clause)
    (hhitNonzero : ∀ spec ∈ mu3NativeHitSpecs shape,
      ∀ lit ∈ spec.1, lit ≠ 0)
    (hhitBound : ∀ spec ∈ mu3NativeHitSpecs shape,
      ∀ lit ∈ spec.1, lit.natAbs ≤ 1128)
    (hhitCounts : ∀ spec ∈ mu3NativeHitSpecs shape,
      seqPrefixTrue (mu3NativeVarsRow edgeVal spec.1) spec.1.size = spec.2)
    (hc4 :
      let hit := mu3NativeHitSpecVal shape edgeVal
      Mu3NativeC4FoldConditions 1128 edgeVal mu3NativePairs hit.1 hit.2) :
    False := by
  obtain ⟨assignment, hsat⟩ := mu3AllTfNativeSatCnf_satisfiable
    shape edgeVal hnz hhitNonzero hhitBound hhitCounts hc4
  have hunsat : (mu3AllTfNativeSatCnf shape).Unsat := by
    cases shape
    · exact mu3AllTfNativeC16_unsat
    · exact mu3AllTfNativeC10C6_unsat
    · exact mu3AllTfNativeC8C8_unsat
  have hfalse := hunsat assignment
  rw [Std.Sat.CNF.sat_def] at hsat
  rw [hsat] at hfalse
  contradiction

/-! ## Fixed base-ID facts -/

theorem mu3NativeHitSpecs_ids_valid (shape : Mu3AllTfShape) :
    (∀ spec ∈ mu3NativeHitSpecs shape, ∀ lit ∈ spec.1, lit ≠ 0) ∧
    (∀ spec ∈ mu3NativeHitSpecs shape, ∀ lit ∈ spec.1,
      lit.natAbs ≤ 1128) := by
  have hcheck : (mu3NativeHitSpecs shape).all fun spec =>
      spec.1.all fun lit => decide (lit ≠ 0 ∧ lit.natAbs ≤ 1128) := by
    cases shape <;> native_decide
  simp only [List.all_eq_true] at hcheck
  constructor
  · intro spec hspec lit hlit
    have hsarr := hcheck spec hspec
    simp only [Array.all_eq_true] at hsarr
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hlit
    have hs := hsarr i hi
    have hp : spec.1[i] ≠ 0 ∧ spec.1[i].natAbs ≤ 1128 := by
      simpa only [decide_eq_true_eq] using hs
    exact hp.1
  · intro spec hspec lit hlit
    have hsarr := hcheck spec hspec
    simp only [Array.all_eq_true] at hsarr
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hlit
    have hs := hsarr i hi
    have hp : spec.1[i] ≠ 0 ∧ spec.1[i].natAbs ≤ 1128 := by
      simpa only [decide_eq_true_eq] using hs
    exact hp.2

theorem mu3NativeCommonSpecs_ids_valid
    (pair : Nat × Nat) (hpair : pair ∈ mu3NativePairs) :
    ∀ spec ∈ mu3NativeCommonSpecs pair.1 pair.2,
      0 < spec.1 ∧ spec.1 ≤ 1128 ∧
      0 < spec.2 ∧ spec.2 ≤ 1128 := by
  have hcheck : mu3NativePairs.all fun p =>
      (mu3NativeCommonSpecs p.1 p.2).all fun spec =>
        decide (0 < spec.1 ∧ spec.1 ≤ 1128 ∧
          0 < spec.2 ∧ spec.2 ≤ 1128) := by
    native_decide
  simp only [List.all_eq_true] at hcheck
  intro spec hspec
  have hs := hcheck pair hpair spec hspec
  simpa only [decide_eq_true_eq] using hs

/-! ## Conjunction-row value agreement -/

def mu3NativeArrayLitValues (val : DimacsValuation) (xs : Array Int) :
    List Bool := xs.toList.map (dimacsLitValue val)

def mu3NativeCommonTruthValues (baseVal : DimacsValuation)
    (specs : List (Nat × Nat)) : List Bool :=
  specs.map fun spec => baseVal spec.1 && baseVal spec.2

/-- Semantic execution appends, in order, exactly the Boolean conjunction
values specified by the base edge assignment. -/
theorem mu3NativeRunConjSpecsVal_values
    (baseTop : Nat) (baseVal : DimacsValuation)
    (specs : List (Nat × Nat))
    (acc : Array Int × Mu3NativeCnfState) (inputVal : DimacsValuation)
    (htop : baseTop ≤ acc.2.top)
    (hprefixSat : dimacsFormulaSatisfied inputVal acc.2.clauses)
    (hprefixBound : dimacsFormulaBounded acc.2.top acc.2.clauses)
    (hagree : ∀ id, id ≤ baseTop → inputVal id = baseVal id)
    (haccIds : ∀ lit ∈ acc.1,
      lit ≠ 0 ∧ lit.natAbs ≤ acc.2.top)
    (hspecIds : ∀ spec ∈ specs,
      0 < spec.1 ∧ spec.1 ≤ baseTop ∧
      0 < spec.2 ∧ spec.2 ≤ baseTop) :
    let out := mu3NativeRunConjSpecsVal baseVal specs acc inputVal
    mu3NativeArrayLitValues out.2 out.1.1 =
      mu3NativeArrayLitValues inputVal acc.1 ++
        mu3NativeCommonTruthValues baseVal specs := by
  induction specs generalizing acc inputVal with
  | nil => simp [mu3NativeRunConjSpecsVal, mu3NativeCommonTruthValues]
  | cons spec rest ih =>
      let step := mu3NativeConjStep spec.1 spec.2 acc.2
      let nextAcc : Array Int × Mu3NativeCnfState :=
        (acc.1.push (step.1 : Int), step.2)
      let nextVal := mu3NativeConjVal acc.2 inputVal spec.1 spec.2
      have hspec := hspecIds spec (by simp)
      have hstep := mu3NativeConjStep_formulaSatisfied_append
        acc.2 inputVal spec.1 spec.2 hspec.1 (hspec.2.1.trans htop)
          hspec.2.2.1 (hspec.2.2.2.trans htop) hprefixSat hprefixBound
      have hstepSat : dimacsFormulaSatisfied nextVal nextAcc.2.clauses := by
        simpa [nextVal, nextAcc, step] using hstep.1
      have hstepBound : dimacsFormulaBounded nextAcc.2.top
          nextAcc.2.clauses := by
        simpa [nextAcc, step] using hstep.2.1
      have hnextTopEq : nextAcc.2.top = acc.2.top + 1 := by
        simp [nextAcc, step, mu3NativeConjStep, mu3NativeFresh,
          mu3NativeEmit]
      have hnextTop : baseTop ≤ nextAcc.2.top := by
        rw [hnextTopEq]
        omega
      have hnextAgree : ∀ id, id ≤ baseTop → nextVal id = baseVal id := by
        intro id hid
        rw [show nextVal id = inputVal id by
          simpa [nextVal] using hstep.2.2.2.2 id (hid.trans htop)]
        exact hagree id hid
      have hnextIds : ∀ lit ∈ nextAcc.1,
          lit ≠ 0 ∧ lit.natAbs ≤ nextAcc.2.top := by
        intro lit hlit
        simp only [nextAcc, Array.mem_push] at hlit
        rcases hlit with hold | rfl
        · obtain ⟨hne, hb⟩ := haccIds lit hold
          exact ⟨hne, hb.trans (by rw [hnextTopEq]; omega)⟩
        · have haux : step.1 = acc.2.top + 1 := by
            simpa [step] using hstep.2.2.1
          rw [haux]
          constructor
          · exact_mod_cast Nat.succ_ne_zero acc.2.top
          · change acc.2.top + 1 ≤ nextAcc.2.top
            rw [hnextTopEq]
      have hrestIds : ∀ s ∈ rest,
          0 < s.1 ∧ s.1 ≤ baseTop ∧ 0 < s.2 ∧ s.2 ≤ baseTop := by
        intro s hs
        exact hspecIds s (by simp [hs])
      have ihEq := ih nextAcc nextVal hnextTop hstepSat hstepBound
        hnextAgree hnextIds hrestIds
      simp only [mu3NativeRunConjSpecsVal]
      rw [ihEq]
      have holdValues : mu3NativeArrayLitValues nextVal acc.1 =
          mu3NativeArrayLitValues inputVal acc.1 := by
        unfold mu3NativeArrayLitValues
        apply List.map_congr_left
        intro lit hlit
        rw [dimacsLitValue_eq_of_agree nextVal inputVal]
        exact hstep.2.2.2.2 lit.natAbs
          (haccIds lit (by simpa using hlit)).2
      have hauxValue : dimacsLitValue nextVal (step.1 : Int) =
          (baseVal spec.1 && baseVal spec.2) := by
        have hstepPos : 0 < step.1 := by
          rw [hstep.2.2.1]
          omega
        rw [dimacsLitValue_natCast nextVal hstepPos]
        rw [show nextVal step.1 = (inputVal spec.1 && inputVal spec.2) by
          simpa [nextVal, step] using hstep.2.2.2.1]
        rw [hagree spec.1 hspec.2.1, hagree spec.2 hspec.2.2.2]
      have hnextValues : mu3NativeArrayLitValues nextVal nextAcc.1 =
          mu3NativeArrayLitValues inputVal acc.1 ++
            [baseVal spec.1 && baseVal spec.2] := by
        change mu3NativeArrayLitValues nextVal
            (acc.1.push (step.1 : Int)) = _
        rw [show mu3NativeArrayLitValues nextVal
            (acc.1.push (step.1 : Int)) =
              mu3NativeArrayLitValues nextVal acc.1 ++
                [dimacsLitValue nextVal (step.1 : Int)] by
          simp [mu3NativeArrayLitValues, Array.toList_push]]
        rw [holdValues, hauxValue]
      rw [hnextValues]
      simp [mu3NativeCommonTruthValues, List.append_assoc]

theorem mu3NativeVarsRow_ofFn_eq_arrayLitValues
    (val : DimacsValuation) (xs : Array Int) :
    List.ofFn (mu3NativeVarsRow val xs) =
      mu3NativeArrayLitValues val xs := by
  apply List.ext_get
  · simp [mu3NativeArrayLitValues]
  · intro n hleft hright
    simp [mu3NativeVarsRow, mu3NativeArrayLitValues]

theorem mu3Native_seqPrefixTrue_eq_count
    {n : Nat} (x : Fin n → Bool) :
    seqPrefixTrue x n = (List.ofFn x).count true := by
  rw [seqPrefixTrue_full_eq_filter_card]
  let v : List.Vector Bool n := ⟨List.ofFn x, by simp⟩
  have h := Fin.card_filter_univ_eq_vector_get_eq_count true v
  convert h using 1 <;> simp [v, List.Vector.get]

def Mu3NativeBaseC4 (edgeVal : DimacsValuation) : Prop :=
  ∀ pair ∈ mu3NativePairs,
    (mu3NativeCommonTruthValues edgeVal
      (mu3NativeCommonSpecs pair.1 pair.2)).count true ≤ 1

/-- A static base-edge common-neighbor bound supplies every stage-indexed
condition required by the executable C4 fold. -/
theorem mu3NativeC4FoldConditions_of_base
    (baseVal : DimacsValuation) (pairs : List (Nat × Nat))
    (st : Mu3NativeCnfState) (inputVal : DimacsValuation)
    (htop : 1128 ≤ st.top)
    (hprefixSat : dimacsFormulaSatisfied inputVal st.clauses)
    (hprefixBound : dimacsFormulaBounded st.top st.clauses)
    (hagree : ∀ id, id ≤ 1128 → inputVal id = baseVal id)
    (hpairs : ∀ pair ∈ pairs, pair ∈ mu3NativePairs)
    (hbaseC4 : Mu3NativeBaseC4 baseVal) :
    Mu3NativeC4FoldConditions 1128 baseVal pairs st inputVal := by
  induction pairs generalizing st inputVal with
  | nil => trivial
  | cons pair rest ih =>
      have hpair : pair ∈ mu3NativePairs := hpairs pair (by simp)
      have hspec := mu3NativeCommonSpecs_ids_valid pair hpair
      let conj := mu3NativeRunConjSpecsVal baseVal
        (mu3NativeCommonSpecs pair.1 pair.2) (#[], st) inputVal
      have hconjSem := mu3NativeRunConjSpecsVal_formulaSatisfied
        1128 baseVal (mu3NativeCommonSpecs pair.1 pair.2) (#[], st)
          inputVal htop hprefixSat hprefixBound hagree (by simp) hspec
      have hvalues := mu3NativeRunConjSpecsVal_values
        1128 baseVal (mu3NativeCommonSpecs pair.1 pair.2) (#[], st)
          inputVal htop hprefixSat hprefixBound hagree (by simp) hspec
      have hcommon : seqPrefixTrue
          (mu3NativeVarsRow conj.2 conj.1.1) conj.1.1.size ≤ 1 := by
        rw [mu3Native_seqPrefixTrue_eq_count]
        rw [mu3NativeVarsRow_ofFn_eq_arrayLitValues]
        have hv : mu3NativeArrayLitValues conj.2 conj.1.1 =
            mu3NativeCommonTruthValues baseVal
              (mu3NativeCommonSpecs pair.1 pair.2) := by
          simpa [conj, mu3NativeArrayLitValues] using hvalues
        rw [hv]
        exact hbaseC4 pair hpair
      let next := mu3NativeC4PairSpecStepVal baseVal pair st inputVal
      have hstep := mu3NativeC4PairSpecStepVal_formulaSatisfied
        1128 baseVal pair st inputVal htop hprefixSat hprefixBound hagree
          hspec hcommon
      have hrestPairs : ∀ p ∈ rest, p ∈ mu3NativePairs := by
        intro p hp
        exact hpairs p (by simp [hp])
      refine ⟨hspec, hcommon, ?_⟩
      exact ih next.1 next.2 hstep.2.2.1 hstep.1 hstep.2.1
        hstep.2.2.2 hrestPairs

end Erdos85
