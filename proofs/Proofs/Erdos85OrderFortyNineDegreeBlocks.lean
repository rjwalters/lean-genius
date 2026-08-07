import Proofs.Erdos85OrderFortyNineDimacsRows

/-!
# Threaded degree-counter blocks for the order-49 DIMACS encoding

The production generator calls `CardEnc.equals` once for each vertex, in
ascending order, threading PySAT's global `top_id`.  This file defines that
exact fold and proves that any Boolean terminal assignment extends through
all 49 equality blocks while preserving the original 1176 edge variables.
-/

namespace Erdos85

/-- Append one vertex's exact-degree counter block and thread its final top. -/
def orderFortyNineDegreeBlockStep (h : Nat) (st : SeqCounterGenState)
    (i : Fin 49) : SeqCounterGenState :=
  let block := seqCounterEqualsCore st.top (orderFortyNineDimacsRow i)
    (orderFortyNineTargetDegree h i)
  { block with clauses := st.clauses ++ block.clauses }

/-- Thread degree blocks through a specified vertex order. -/
def orderFortyNineDegreeBlocksLoop (h : Nat) :
    List (Fin 49) → SeqCounterGenState → SeqCounterGenState
  | [], st => st
  | i :: rest, st =>
      orderFortyNineDegreeBlocksLoop h rest
        (orderFortyNineDegreeBlockStep h st i)

/-- The exact ascending 49-row degree-counter prefix of the production CNF. -/
def orderFortyNineDegreeBlocks (h : Nat) : SeqCounterGenState :=
  orderFortyNineDegreeBlocksLoop h (List.finRange 49) { top := 1176 }

/-- Reification of a graph row persists under any extension that agrees on
the original edge variables. -/
theorem orderFortyNineDimacsRow_reifies_of_extension
    (edges : BitVec 1176) (i : Fin 49) (val : DimacsValuation) (top : Nat)
    (htop : 1176 ≤ top)
    (hagree : ∀ id, id ≤ 1176 →
      val id = orderFortyNineDimacsEdgeVal edges id) :
    SeqCounterInputReifies val top (orderFortyNineDimacsRow i)
      (orderFortyNineDimacsSizedCounterRow edges i) := by
  have hbase := orderFortyNineDimacsRow_reifies_sized edges i
  constructor
  · exact hbase.size_eq
  · exact hbase.nonzero
  · intro k hk
    exact (hbase.bounded k hk).trans htop
  · intro k hk
    calc
      dimacsLitValue val ((orderFortyNineDimacsRow i).getD k 0) =
          dimacsLitValue (orderFortyNineDimacsEdgeVal edges)
            ((orderFortyNineDimacsRow i).getD k 0) :=
        dimacsLitValue_eq_of_agree val (orderFortyNineDimacsEdgeVal edges)
          (hagree _ (hbase.bounded k hk))
      _ = orderFortyNineDimacsSizedCounterRow edges i ⟨k, hk⟩ :=
        hbase.value k hk

/-- Semantic invariant carried while the 49 degree blocks are accumulated. -/
def OrderFortyNineDegreeBlocksInvariant
    (edges : BitVec 1176) (st : SeqCounterGenState) : Prop :=
  ∃ val : DimacsValuation,
    dimacsFormulaSatisfied val st.clauses ∧
    dimacsFormulaBounded st.top st.clauses ∧
    1176 ≤ st.top ∧
    ∀ id, id ≤ 1176 → val id = orderFortyNineDimacsEdgeVal edges id

theorem orderFortyNineDegreeBlockStep_invariant
    {h : Nat} {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints h masks edges)
    (st : SeqCounterGenState)
    (hinv : OrderFortyNineDegreeBlocksInvariant edges st) (i : Fin 49) :
    OrderFortyNineDegreeBlocksInvariant edges
      (orderFortyNineDegreeBlockStep h st i) := by
  obtain ⟨val, hsat, hbounded, htop, hagree⟩ := hinv
  let vars := orderFortyNineDimacsRow i
  let x := orderFortyNineDimacsSizedCounterRow edges i
  let t := orderFortyNineTargetDegree h i
  let block := seqCounterEqualsCore st.top vars t
  let nextVal := seqCounterEqualsCoreVal val st.top vars x t
  have hinput : SeqCounterInputReifies val st.top vars x := by
    exact orderFortyNineDimacsRow_reifies_of_extension edges i val st.top
      htop hagree
  have hblockSat : dimacsFormulaSatisfied nextVal block.clauses := by
    exact seqCounterEqualsCoreVal_formulaSatisfied val st.top vars x hinput t
      (orderFortyNineDimacsSizedCounterRow_count_of_constraints hc i)
  have htopStep : st.top ≤ block.top := by
    exact seqCounterEqualsCore_top_bound st.top vars t
  have hpreviousSat : dimacsFormulaSatisfied nextVal st.clauses := by
    apply dimacsFormulaSatisfied_of_bounded_agree hsat hbounded
    intro id hid
    exact (seqCounterEqualsCoreVal_input val st.top vars x t id hid).symm
  have hcombinedSat :
      dimacsFormulaSatisfied nextVal (st.clauses ++ block.clauses) :=
    dimacsFormulaSatisfied_append hpreviousSat hblockSat
  have hblockBounded : dimacsFormulaBounded block.top block.clauses := by
    exact seqCounterEqualsCore_formulaBounded val st.top vars x hinput t
  have hcombinedBounded :
      dimacsFormulaBounded block.top (st.clauses ++ block.clauses) :=
    dimacsFormulaBounded_append
      (dimacsFormulaBounded_mono htopStep hbounded) hblockBounded
  refine ⟨nextVal, ?_, ?_, htop.trans htopStep, ?_⟩
  · simpa [orderFortyNineDegreeBlockStep, block, vars, t] using hcombinedSat
  · simpa [orderFortyNineDegreeBlockStep, block, vars, t] using hcombinedBounded
  · intro id hid
    change seqCounterEqualsCoreVal val st.top vars x t id = _
    rw [seqCounterEqualsCoreVal_input val st.top vars x t id
      (hid.trans htop)]
    exact hagree id hid

theorem orderFortyNineDegreeBlocksLoop_invariant
    {h : Nat} {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints h masks edges)
    (rows : List (Fin 49)) (st : SeqCounterGenState)
    (hinv : OrderFortyNineDegreeBlocksInvariant edges st) :
    OrderFortyNineDegreeBlocksInvariant edges
      (orderFortyNineDegreeBlocksLoop h rows st) := by
  induction rows generalizing st with
  | nil => exact hinv
  | cons i rest ih =>
      exact ih (orderFortyNineDegreeBlockStep h st i)
        (orderFortyNineDegreeBlockStep_invariant hc st hinv i)

/-- All 49 production-order degree blocks are simultaneously satisfiable by
an extension of every Boolean terminal assignment. -/
theorem orderFortyNineDegreeBlocks_invariant
    {h : Nat} {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints h masks edges) :
    OrderFortyNineDegreeBlocksInvariant edges
      (orderFortyNineDegreeBlocks h) := by
  apply orderFortyNineDegreeBlocksLoop_invariant hc
  refine ⟨orderFortyNineDimacsEdgeVal edges, ?_, ?_, le_rfl, ?_⟩
  · exact dimacsFormulaSatisfied_empty _
  · exact dimacsFormulaBounded_empty _
  · intro id hid
    rfl

theorem orderFortyNineDegreeBlocks_formulaSatisfied
    {h : Nat} {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints h masks edges) :
    ∃ val : DimacsValuation,
      dimacsFormulaSatisfied val (orderFortyNineDegreeBlocks h).clauses := by
  obtain ⟨val, hsat, _⟩ := orderFortyNineDegreeBlocks_invariant hc
  exact ⟨val, hsat⟩

end Erdos85
