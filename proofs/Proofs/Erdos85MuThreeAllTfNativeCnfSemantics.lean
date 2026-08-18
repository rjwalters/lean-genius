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

end Erdos85
