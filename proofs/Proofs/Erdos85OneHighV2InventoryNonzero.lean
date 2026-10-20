import Proofs.Erdos85OneHighV2Exclusion
import Proofs.Erdos85OneHighV2CapacityInventory

/-!
# Nonzero literals in every exact-v2 one-high CNF

`OneHighFamilyV2CheckedUnsat profile table` has two fields: `nonzero` (no
clause of the generated DIMACS formula contains the literal `0`, so that it
translates clausewise into a `Std.Sat.CNF`) and `unsat` (the translated CNF
has no satisfying assignment).  Previously `nonzero` was discharged only for
the calibration instance, by `native_decide`
(`oneHighV2Calibration_nonzero`).

This module proves `nonzero` structurally, for **every** profile and **every**
miss table (`oneHighFamilyV2Clauses_nonzero`), hence in particular for every
row of the 13,351-row one-high capacity inventory
(`oneHighCapacityInventory_nonzero`).  The argument mirrors the
`OneHighFamilyIdsSound` induction of the generator: every emitted literal is
`±id` for a named `IDPool` identifier (allocated as `top + 1 > 0`), a
sequential-counter auxiliary (likewise positive, see
`Erdos85OrderFortyNineDegreeBlocksNonzero`), or the negation of a previously
collected such literal.  No `native_decide` or `decide` is used; the theorems
depend only on the standard axioms `propext`, `Classical.choice`,
`Quot.sound` (see the `#print axioms` lines at the end).

Consequently only the `unsat` field remains an assumption:
`oneHighFamilyV2CheckedUnsat_of_unsat` builds the checked structure from the
unsatisfiability statement alone, and `oneHighCapacityInventory_checked_of_unsat`
converts the inventory-wide unsatisfiability hypothesis into the `hOne`
hypothesis of the order-49 capstones.

This file is new and changes no existing module.
-/

namespace Erdos85

/-! ## Generic fold invariants -/

theorem oneHighNZ_foldl {α β : Type} (P : β → Prop) (f : β → α → β) :
    ∀ (xs : List α) (init : β), P init →
      (∀ b x, x ∈ xs → P b → P (f b x)) → P (xs.foldl f init)
  | [], _, h, _ => h
  | x :: xs, init, h, hf =>
      oneHighNZ_foldl P f xs (f init x) (hf init x (by simp) h)
        (fun b y hy hb => hf b y (List.mem_cons_of_mem x hy) hb)

theorem oneHighNZ_arrayFoldl {α β : Type} (P : β → Prop) (f : β → α → β)
    (xs : Array α) (init : β) (h : P init)
    (hf : ∀ b x, x ∈ xs → P b → P (f b x)) : P (xs.foldl f init) := by
  rw [← Array.foldl_toList]
  exact oneHighNZ_foldl P f xs.toList init h
    (fun b x hx hb => hf b x (Array.mem_toList_iff.mp hx) hb)

/-! ## Sequential-counter wrappers -/

theorem seqCounter_getD_nonzero_of_mem {vars : Array Int}
    (hvars : ∀ lit ∈ vars, lit ≠ 0) :
    ∀ i, i < vars.size → vars.getD i 0 ≠ 0 := by
  intro i hi
  have hmem := hvars vars[i] (Array.getElem_mem hi)
  simpa [Array.getD, hi] using hmem

theorem seqCounterAtMost_nonzero (top : Nat) (vars : Array Int)
    (hvars : ∀ lit ∈ vars, lit ≠ 0) (t : Nat) :
    ∀ clause ∈ (seqCounterAtMost top vars t).clauses,
      ∀ lit ∈ clause, lit ≠ 0 := by
  intro clause hclause lit hlit
  unfold seqCounterAtMost at hclause
  split at hclause
  · simp only [Array.mem_map] at hclause
    obtain ⟨v, hv, rfl⟩ := hclause
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hlit
    have := hvars v hv
    omega
  · split at hclause
    · simp at hclause
      subst hclause
      simp at hlit
      obtain ⟨v, hv, rfl⟩ := hlit
      have := hvars v (by simpa using hv)
      omega
    · exact (seqCounterAtMostCore_nonzero top vars
        (seqCounter_getD_nonzero_of_mem hvars) t).1 clause hclause lit hlit

theorem seqCounterEquals_nonzero (top : Nat) (vars : Array Int)
    (hvars : ∀ lit ∈ vars, lit ≠ 0) (t : Nat) :
    ∀ clause ∈ (seqCounterEquals top vars t).clauses,
      ∀ lit ∈ clause, lit ≠ 0 := by
  intro clause hclause
  simp only [seqCounterEquals, Array.mem_append] at hclause
  rcases hclause with hlower | hupper
  · unfold seqCounterAtLeast at hlower
    refine seqCounterAtMost_nonzero top _ ?_ _ clause hlower
    intro lit hlit
    simp only [Array.mem_map] at hlit
    obtain ⟨v, hv, rfl⟩ := hlit
    have := hvars v hv
    omega
  · exact seqCounterAtMost_nonzero _ vars hvars t clause hupper

/-! ## The generator invariant -/

/-- Every named identifier is positive and every emitted clause is free of
the literal `0`. -/
structure OneHighFamilyNonzero (st : OneHighFamilyGenState) : Prop where
  ids_pos : ∀ entry ∈ st.ids, 0 < entry.2
  clauses : ∀ clause ∈ st.clauses, ∀ lit ∈ clause, lit ≠ 0

/-- The same invariant for a state paired with an accumulator of literals. -/
structure OneHighFamilyAccNonzero
    (p : Array Int × OneHighFamilyGenState) : Prop where
  acc : ∀ lit ∈ p.1, lit ≠ 0
  state : OneHighFamilyNonzero p.2

theorem oneHighFamilyNonzero_initial :
    OneHighFamilyNonzero ({} : OneHighFamilyGenState) := by
  constructor <;> simp

theorem oneHighFamilyAccNonzero_empty {st : OneHighFamilyGenState}
    (h : OneHighFamilyNonzero st) : OneHighFamilyAccNonzero (#[], st) :=
  ⟨by simp, h⟩

theorem oneHighFamilyAccNonzero_push {acc : Array Int}
    {st : OneHighFamilyGenState} (hacc : ∀ lit ∈ acc, lit ≠ 0)
    (hst : OneHighFamilyNonzero st) {id : Nat} (hid : 0 < id) :
    OneHighFamilyAccNonzero (acc.push (id : Int), st) := by
  refine ⟨?_, hst⟩
  intro lit hlit
  simp only [Array.mem_push] at hlit
  rcases hlit with hlit | rfl
  · exact hacc lit hlit
  · omega

theorem oneHighFamilyNonzero_atomId_raw {st : OneHighFamilyGenState}
    (h : OneHighFamilyNonzero st) (atom : OneHighFamilyAtom) :
    OneHighFamilyNonzero (oneHighFamilyAtomId atom st).2 ∧
      0 < (oneHighFamilyAtomId atom st).1 := by
  unfold oneHighFamilyAtomId
  rcases hlook : oneHighFamilyLookup atom st.ids with _ | id
  · refine ⟨⟨?_, h.clauses⟩, Nat.succ_pos _⟩
    intro entry hentry
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | hentry
    · exact Nat.succ_pos _
    · exact h.ids_pos entry hentry
  · exact ⟨h, h.ids_pos _ (oneHighFamilyLookup_eq_some_mem hlook)⟩

theorem oneHighFamilyNonzero_atomId {st st' : OneHighFamilyGenState}
    (h : OneHighFamilyNonzero st) {atom : OneHighFamilyAtom} {id : Nat}
    (heq : oneHighFamilyAtomId atom st = (id, st')) :
    OneHighFamilyNonzero st' ∧ 0 < id := by
  have := oneHighFamilyNonzero_atomId_raw h atom
  rw [heq] at this
  exact this

theorem oneHighFamilyNonzero_edgeId {st st' : OneHighFamilyGenState}
    (h : OneHighFamilyNonzero st) {i j id : Nat}
    (heq : oneHighFamilyEdgeId i j st = (id, st')) :
    OneHighFamilyNonzero st' ∧ 0 < id :=
  oneHighFamilyNonzero_atomId h heq

theorem oneHighFamilyNonzero_midpointAtomId {st st' : OneHighFamilyGenState}
    (h : OneHighFamilyNonzero st) {x w z id : Nat}
    (heq : oneHighFamilyMidpointAtomId x w z st = (id, st')) :
    OneHighFamilyNonzero st' ∧ 0 < id :=
  oneHighFamilyNonzero_atomId h heq

theorem oneHighFamilyNonzero_commonAtomId {st st' : OneHighFamilyGenState}
    (h : OneHighFamilyNonzero st) {x z id : Nat}
    (heq : oneHighFamilyCommonAtomId x z st = (id, st')) :
    OneHighFamilyNonzero st' ∧ 0 < id :=
  oneHighFamilyNonzero_atomId h heq

theorem oneHighFamilyNonzero_emit {st : OneHighFamilyGenState}
    (h : OneHighFamilyNonzero st) {clause : DimacsClause}
    (hclause : ∀ lit ∈ clause, lit ≠ 0) :
    OneHighFamilyNonzero (oneHighFamilyEmit clause st).2 := by
  change OneHighFamilyNonzero { st with clauses := st.clauses.push clause }
  refine ⟨h.ids_pos, ?_⟩
  intro c hc
  simp only [Array.mem_push] at hc
  rcases hc with hc | rfl
  · exact h.clauses c hc
  · exact hclause

theorem oneHighFamilyNonzero_equalsBlock {st : OneHighFamilyGenState}
    (h : OneHighFamilyNonzero st) (vars : Array Int)
    (hvars : ∀ lit ∈ vars, lit ≠ 0) (bound : Nat) :
    OneHighFamilyNonzero (oneHighFamilyEqualsBlock vars bound st) := by
  refine ⟨h.ids_pos, ?_⟩
  intro c hc
  simp only [oneHighFamilyEqualsBlock, Array.mem_append] at hc
  rcases hc with hc | hc
  · exact h.clauses c hc
  · exact seqCounterEquals_nonzero _ vars hvars bound c hc

theorem oneHighFamilyNonzero_runList {α : Type} (xs : List α)
    (step : α → OneHighFamilyGenState → OneHighFamilyGenState)
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st)
    (hstep : ∀ x st, OneHighFamilyNonzero st →
      OneHighFamilyNonzero (step x st)) :
    OneHighFamilyNonzero (oneHighFamilyRunList xs step st) := by
  unfold oneHighFamilyRunList
  exact oneHighNZ_foldl OneHighFamilyNonzero _ xs st h
    (fun st x _ hs => hstep x st hs)

/-- Literal side conditions of the small fixed clauses. -/
macro "nz_lits" : tactic =>
  `(tactic| (intro lit hlit;
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hlit; omega))

/-! ## Base, C4, at-most-one and far-degree segments -/

theorem oneHighFamilyNonzero_internalPairStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st)
    (a b i j : Nat) :
    OneHighFamilyNonzero (oneHighFamilyInternalPairStep a b i j st) := by
  simp only [oneHighFamilyInternalPairStep]
  generalize heq : oneHighFamilyEdgeId (5 * b + i) (5 * b + j) st = out
  rcases out with ⟨id, st'⟩
  obtain ⟨hs, hid⟩ := oneHighFamilyNonzero_edgeId h heq
  apply oneHighFamilyNonzero_emit hs
  intro lit hlit
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hlit
  subst hlit
  split <;> omega

theorem oneHighFamilyNonzero_internalBlockStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st) (a b : Nat) :
    OneHighFamilyNonzero (oneHighFamilyInternalBlockStep a b st) := by
  apply oneHighFamilyNonzero_runList _ _ h
  intro i st hi
  apply oneHighFamilyNonzero_runList _ _ hi
  intro j st hj
  split
  · exact oneHighFamilyNonzero_internalPairStep hj a b i j
  · exact hj

theorem oneHighFamilyNonzero_internalUnits (a : Nat) :
    OneHighFamilyNonzero (oneHighFamilyInternalUnits a) :=
  oneHighFamilyNonzero_runList _ _ oneHighFamilyNonzero_initial
    (fun b _ h => oneHighFamilyNonzero_internalBlockStep h a b)

theorem oneHighFamilyNonzero_matePairStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st)
    (b i j : Nat) :
    OneHighFamilyNonzero (oneHighFamilyMatePairStep b i j st) := by
  simp only [oneHighFamilyMatePairStep]
  generalize heq : oneHighFamilyEdgeId (5 * b + i) (5 * (b + 1) + j) st = out
  rcases out with ⟨id, st'⟩
  obtain ⟨hs, hid⟩ := oneHighFamilyNonzero_edgeId h heq
  exact oneHighFamilyNonzero_emit hs (by nz_lits)

theorem oneHighFamilyNonzero_mateBlockStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st) (b : Nat) :
    OneHighFamilyNonzero (oneHighFamilyMateBlockStep b st) := by
  apply oneHighFamilyNonzero_runList _ _ h
  intro i st hi
  exact oneHighFamilyNonzero_runList _ _ hi
    (fun j st hj => oneHighFamilyNonzero_matePairStep hj b i j)

theorem oneHighFamilyNonzero_baseUnits (a : Nat) :
    OneHighFamilyNonzero (oneHighFamilyBaseUnits a) :=
  oneHighFamilyNonzero_runList _ _ (oneHighFamilyNonzero_internalUnits a)
    (fun b _ h => oneHighFamilyNonzero_mateBlockStep h b)

theorem oneHighFamilyNonzero_c4SameMidpointStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st)
    (i j w : Nat) :
    OneHighFamilyNonzero (oneHighFamilyC4SameMidpointStep i j w st) := by
  simp only [oneHighFamilyC4SameMidpointStep]
  generalize h₁ : oneHighFamilyEdgeId i w st = out₁
  rcases out₁ with ⟨eiw, st₁⟩
  obtain ⟨hs₁, p₁⟩ := oneHighFamilyNonzero_edgeId h h₁
  generalize h₂ : oneHighFamilyEdgeId j w st₁ = out₂
  rcases out₂ with ⟨ejw, st₂⟩
  obtain ⟨hs₂, p₂⟩ := oneHighFamilyNonzero_edgeId hs₁ h₂
  simp only [h₂]
  exact oneHighFamilyNonzero_emit hs₂ (by nz_lits)

theorem oneHighFamilyNonzero_c4CrossMidpointsStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st)
    (i j w w' : Nat) :
    OneHighFamilyNonzero (oneHighFamilyC4CrossMidpointsStep i j w w' st) := by
  simp only [oneHighFamilyC4CrossMidpointsStep]
  generalize h₁ : oneHighFamilyEdgeId i w st = out₁
  rcases out₁ with ⟨eiw, st₁⟩
  obtain ⟨hs₁, p₁⟩ := oneHighFamilyNonzero_edgeId h h₁
  generalize h₂ : oneHighFamilyEdgeId j w st₁ = out₂
  rcases out₂ with ⟨ejw, st₂⟩
  obtain ⟨hs₂, p₂⟩ := oneHighFamilyNonzero_edgeId hs₁ h₂
  generalize h₃ : oneHighFamilyEdgeId i w' st₂ = out₃
  rcases out₃ with ⟨eiw', st₃⟩
  obtain ⟨hs₃, p₃⟩ := oneHighFamilyNonzero_edgeId hs₂ h₃
  generalize h₄ : oneHighFamilyEdgeId j w' st₃ = out₄
  rcases out₄ with ⟨ejw', st₄⟩
  obtain ⟨hs₄, p₄⟩ := oneHighFamilyNonzero_edgeId hs₃ h₄
  simp only [h₂, h₃, h₄]
  exact oneHighFamilyNonzero_emit hs₄ (by nz_lits)

theorem oneHighFamilyNonzero_c4PairStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st) (i j : Nat) :
    OneHighFamilyNonzero (oneHighFamilyC4PairStep i j st) := by
  simp only [oneHighFamilyC4PairStep]
  split
  · exact oneHighFamilyNonzero_runList _ _ h
      (fun w st hw => oneHighFamilyNonzero_c4SameMidpointStep hw i j w)
  · apply oneHighFamilyNonzero_runList _ _ h
    intro w st hw
    apply oneHighFamilyNonzero_runList _ _ hw
    intro w' st hw'
    split
    · exact oneHighFamilyNonzero_c4CrossMidpointsStep hw' i j w w'
    · exact hw'

theorem oneHighFamilyNonzero_c4OuterStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st) (i : Nat) :
    OneHighFamilyNonzero (oneHighFamilyC4OuterStep i st) := by
  apply oneHighFamilyNonzero_runList _ _ h
  intro j st hj
  split
  · exact oneHighFamilyNonzero_c4PairStep hj i j
  · exact hj

theorem oneHighFamilyNonzero_c4Clauses (a : Nat) :
    OneHighFamilyNonzero (oneHighFamilyC4Clauses a) :=
  oneHighFamilyNonzero_runList _ _ (oneHighFamilyNonzero_baseUnits a)
    (fun i _ h => oneHighFamilyNonzero_c4OuterStep h i)

theorem oneHighFamilyNonzero_atMostOnePairStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st)
    (y x x' : Nat) :
    OneHighFamilyNonzero (oneHighFamilyAtMostOnePairStep y x x' st) := by
  simp only [oneHighFamilyAtMostOnePairStep]
  generalize h₁ : oneHighFamilyEdgeId y x st = out₁
  rcases out₁ with ⟨eyx, st₁⟩
  obtain ⟨hs₁, p₁⟩ := oneHighFamilyNonzero_edgeId h h₁
  generalize h₂ : oneHighFamilyEdgeId y x' st₁ = out₂
  rcases out₂ with ⟨eyx', st₂⟩
  obtain ⟨hs₂, p₂⟩ := oneHighFamilyNonzero_edgeId hs₁ h₂
  simp only [h₂]
  exact oneHighFamilyNonzero_emit hs₂ (by nz_lits)

theorem oneHighFamilyNonzero_atMostOneVertexStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st) (b y : Nat) :
    OneHighFamilyNonzero (oneHighFamilyAtMostOneVertexStep b y st) := by
  simp only [oneHighFamilyAtMostOneVertexStep]
  split
  · exact h
  · apply oneHighFamilyNonzero_runList _ _ h
    intro x st hx
    apply oneHighFamilyNonzero_runList _ _ hx
    intro x' st hx'
    split
    · exact oneHighFamilyNonzero_atMostOnePairStep hx' y x x'
    · exact hx'

theorem oneHighFamilyNonzero_atMostOneBlockStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st) (b : Nat) :
    OneHighFamilyNonzero (oneHighFamilyAtMostOneBlockStep b st) :=
  oneHighFamilyNonzero_runList _ _ h
    (fun y _ hy => oneHighFamilyNonzero_atMostOneVertexStep hy b y)

theorem oneHighFamilyNonzero_atMostOneBlockClauses (a : Nat) :
    OneHighFamilyNonzero (oneHighFamilyAtMostOneBlockClauses a) :=
  oneHighFamilyNonzero_runList _ _ (oneHighFamilyNonzero_c4Clauses a)
    (fun b _ h => oneHighFamilyNonzero_atMostOneBlockStep h b)

/-- The edge-collecting fold shared by the far-degree and miss-definition
segments. -/
theorem oneHighFamilyNonzero_collectEdges (w : Nat) (zs : List Nat)
    {p : Array Int × OneHighFamilyGenState} (h : OneHighFamilyAccNonzero p) :
    OneHighFamilyAccNonzero (zs.foldl (fun (acc, st) z =>
      let (id, st) := oneHighFamilyEdgeId w z st
      (acc.push (id : Int), st)) p) := by
  apply oneHighNZ_foldl OneHighFamilyAccNonzero _ zs p h
  intro q z _ hq
  rcases q with ⟨acc, st₀⟩
  try dsimp only
  generalize he : oneHighFamilyEdgeId w z st₀ = e
  rcases e with ⟨id, st₁⟩
  obtain ⟨hs₁, hid⟩ := oneHighFamilyNonzero_edgeId hq.state he
  exact oneHighFamilyAccNonzero_push hq.acc hs₁ hid

theorem oneHighFamilyNonzero_farDegreeStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st) (a y : Nat) :
    OneHighFamilyNonzero (oneHighFamilyFarDegreeStep a y st) := by
  simp only [oneHighFamilyFarDegreeStep]
  generalize heq : (oneHighFamilyFarVertices y).foldl (fun (acc, st) x =>
    let (id, st) := oneHighFamilyEdgeId y x st
    (acc.push (id : Int), st)) (#[], st) = out
  rcases out with ⟨vars, st'⟩
  have hs : OneHighFamilyAccNonzero (vars, st') := by
    rw [← heq]
    exact oneHighFamilyNonzero_collectEdges y _
      (oneHighFamilyAccNonzero_empty h)
  exact oneHighFamilyNonzero_equalsBlock hs.state vars hs.acc _

theorem oneHighFamilyNonzero_farDegreeClauses (a : Nat) :
    OneHighFamilyNonzero (oneHighFamilyFarDegreeClauses a) :=
  oneHighFamilyNonzero_runList _ _
    (oneHighFamilyNonzero_atMostOneBlockClauses a)
    (fun y _ h => oneHighFamilyNonzero_farDegreeStep h a y)

/-! ## Miss definitions and lex -/

theorem oneHighFamilyNonzero_missDefinitionStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st) (w b : Nat) :
    OneHighFamilyNonzero (oneHighFamilyMissDefinitionStep w b st) := by
  simp only [oneHighFamilyMissDefinitionStep]
  split
  · exact h
  · generalize h₁ : oneHighFamilyAtomId (.miss w b) st = out₁
    rcases out₁ with ⟨xv, st₁⟩
    obtain ⟨hs₁, hxv⟩ := oneHighFamilyNonzero_atomId h h₁
    generalize h₂ : (oneHighFamilyBlockVertices b).foldl
      (fun (acc, st) z =>
        let (id, st) := oneHighFamilyEdgeId w z st
        (acc.push (id : Int), st)) (#[], st₁) = out₂
    rcases out₂ with ⟨lits, st₂⟩
    have hs₂ : OneHighFamilyAccNonzero (lits, st₂) := by
      rw [← h₂]
      exact oneHighFamilyNonzero_collectEdges w _
        (oneHighFamilyAccNonzero_empty hs₁)
    have hs₃ : OneHighFamilyNonzero (lits.foldl
        (fun st lit => (oneHighFamilyEmit [-(xv : Int), -lit] st).2) st₂) := by
      apply oneHighNZ_arrayFoldl OneHighFamilyNonzero _ lits st₂ hs₂.state
      intro s lit hlit hs
      have := hs₂.acc lit hlit
      exact oneHighFamilyNonzero_emit hs (by nz_lits)
    simp only [h₂]
    apply oneHighFamilyNonzero_emit hs₃
    intro l hl
    simp only [List.mem_cons] at hl
    rcases hl with rfl | hl
    · omega
    · exact hs₂.acc l (Array.mem_toList_iff.mp hl)

theorem oneHighFamilyNonzero_missVertexStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st) (a w : Nat) :
    OneHighFamilyNonzero (oneHighFamilyMissVertexStep a w st) := by
  simp only [oneHighFamilyMissVertexStep]
  split
  · exact oneHighFamilyNonzero_runList _ _ h
      (fun b st hb => oneHighFamilyNonzero_missDefinitionStep hb w b)
  · exact h

theorem oneHighFamilyNonzero_missDefinitionClauses (a : Nat) :
    OneHighFamilyNonzero (oneHighFamilyMissDefinitionClauses a) :=
  oneHighFamilyNonzero_runList _ _ (oneHighFamilyNonzero_farDegreeClauses a)
    (fun w _ h => oneHighFamilyNonzero_missVertexStep h a w)

theorem oneHighFamilyNonzero_lexPairStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st)
    (x y j k : Nat) :
    OneHighFamilyNonzero (oneHighFamilyLexPairStep x y j k st) := by
  simp only [oneHighFamilyLexPairStep]
  split
  · generalize h₁ : oneHighFamilyAtomId (.miss x j) st = out₁
    rcases out₁ with ⟨xj, st₁⟩
    obtain ⟨hs₁, p₁⟩ := oneHighFamilyNonzero_atomId h h₁
    generalize h₂ : oneHighFamilyAtomId (.miss y k) st₁ = out₂
    rcases out₂ with ⟨yk, st₂⟩
    obtain ⟨hs₂, p₂⟩ := oneHighFamilyNonzero_atomId hs₁ h₂
    simp only [h₂]
    exact oneHighFamilyNonzero_emit hs₂ (by nz_lits)
  · exact h

theorem oneHighFamilyNonzero_lexLeq
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st) (c x y : Nat) :
    OneHighFamilyNonzero (oneHighFamilyLexLeq c x y st) := by
  apply oneHighFamilyNonzero_runList _ _ h
  intro j st hj
  exact oneHighFamilyNonzero_runList _ _ hj
    (fun k st hk => oneHighFamilyNonzero_lexPairStep hk x y j k)

theorem oneHighFamilyNonzero_lexBlockStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st) (a c : Nat) :
    OneHighFamilyNonzero (oneHighFamilyLexBlockStep a c st) := by
  simp only [oneHighFamilyLexBlockStep]
  have hbase := oneHighFamilyNonzero_lexLeq h c (5 * c) (5 * c + 1)
  split
  · exact oneHighFamilyNonzero_lexLeq
      (oneHighFamilyNonzero_lexLeq hbase c (5 * c + 2) (5 * c + 3))
      c (5 * c) (5 * c + 2)
  · exact hbase

/-! ## Tseitin helpers -/

theorem oneHighFamilyNonzero_midpointTseitinStep
    {p : Array Int × OneHighFamilyGenState} (h : OneHighFamilyAccNonzero p)
    (x z w : Nat) :
    OneHighFamilyAccNonzero (oneHighFamilyMidpointTseitinStep x z w p) := by
  rcases p with ⟨ts, st⟩
  simp only [oneHighFamilyMidpointTseitinStep]
  generalize h₁ : oneHighFamilyMidpointAtomId x w z st = out₁
  rcases out₁ with ⟨t, st₁⟩
  obtain ⟨hs₁, pt⟩ := oneHighFamilyNonzero_midpointAtomId h.state h₁
  generalize h₂ : oneHighFamilyEdgeId x w st₁ = out₂
  rcases out₂ with ⟨exw, st₂⟩
  obtain ⟨hs₂, p₂⟩ := oneHighFamilyNonzero_edgeId hs₁ h₂
  generalize h₃ : oneHighFamilyEdgeId w z st₂ = out₃
  rcases out₃ with ⟨ewz, st₃⟩
  obtain ⟨hs₃, p₃⟩ := oneHighFamilyNonzero_edgeId hs₂ h₃
  simp only [h₂, h₃]
  exact oneHighFamilyAccNonzero_push h.acc
    (oneHighFamilyNonzero_emit
      (oneHighFamilyNonzero_emit
        (oneHighFamilyNonzero_emit hs₃ (by nz_lits)) (by nz_lits))
      (by nz_lits)) pt

theorem oneHighFamilyNonzero_commonTseitinStep
    {p : Array Int × OneHighFamilyGenState} (h : OneHighFamilyAccNonzero p)
    (bi bj x z : Nat) :
    OneHighFamilyAccNonzero (oneHighFamilyCommonTseitinStep bi bj x z p) := by
  rcases p with ⟨cs, st⟩
  simp only [oneHighFamilyCommonTseitinStep]
  generalize h₁ : (oneHighFamilyPairedMidpoints bi bj).foldl
    (fun accst w => oneHighFamilyMidpointTseitinStep x z w accst)
    (#[], st) = out₁
  rcases out₁ with ⟨ts, st₁⟩
  have hs₁ : OneHighFamilyAccNonzero (ts, st₁) := by
    rw [← h₁]
    apply oneHighNZ_foldl OneHighFamilyAccNonzero _ _ _
      (oneHighFamilyAccNonzero_empty h.state)
    intro q w _ hq
    exact oneHighFamilyNonzero_midpointTseitinStep hq x z w
  generalize h₂ : oneHighFamilyCommonAtomId x z st₁ = out₂
  rcases out₂ with ⟨c, st₂⟩
  obtain ⟨hs₂, hc⟩ := oneHighFamilyNonzero_commonAtomId hs₁.state h₂
  have hs₃ : OneHighFamilyNonzero
      (oneHighFamilyEmit (-(c : Int) :: ts.toList) st₂).2 := by
    apply oneHighFamilyNonzero_emit hs₂
    intro l hl
    simp only [List.mem_cons] at hl
    rcases hl with rfl | hl
    · omega
    · exact hs₁.acc l (Array.mem_toList_iff.mp hl)
  have hs₄ : OneHighFamilyNonzero (ts.foldl
      (fun st t => (oneHighFamilyEmit [-t, (c : Int)] st).2)
      (oneHighFamilyEmit (-(c : Int) :: ts.toList) st₂).2) := by
    apply oneHighNZ_arrayFoldl OneHighFamilyNonzero _ ts _ hs₃
    intro s t ht hs
    have := hs₁.acc t ht
    exact oneHighFamilyNonzero_emit hs (by nz_lits)
  try simp only [h₁, h₂]
  exact oneHighFamilyAccNonzero_push h.acc hs₄ hc

/-! ## Table pins (shared with the PURE+table generator) -/

theorem oneHighFamilyNonzero_tableMissVars
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st)
    (a c j : Nat) :
    OneHighFamilyAccNonzero (oneHighFamilyTableMissVars a c j st) := by
  unfold oneHighFamilyTableMissVars
  apply oneHighNZ_foldl OneHighFamilyAccNonzero _ _ _
    (oneHighFamilyAccNonzero_empty h)
  intro q atom _ hq
  rcases q with ⟨vars, s⟩
  try dsimp only
  generalize he : oneHighFamilyAtomId atom s = e
  rcases e with ⟨id, s'⟩
  obtain ⟨hs, hid⟩ := oneHighFamilyNonzero_atomId hq.state he
  exact oneHighFamilyAccNonzero_push hq.acc hs hid

theorem oneHighFamilyNonzero_tablePairStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st)
    (a : Nat) (table : OneHighMissTable) (pair : Nat × Nat) :
    OneHighFamilyNonzero (oneHighFamilyTablePairStep a table pair st) := by
  have hv := oneHighFamilyNonzero_tableMissVars h a pair.1 pair.2
  simp only [oneHighFamilyTablePairStep]
  generalize hm : oneHighFamilyTableMissVars a pair.1 pair.2 st = m at hv ⊢
  rcases m with ⟨vars, s⟩
  exact oneHighFamilyNonzero_equalsBlock hv.state vars hv.acc _

/-! ## The exact v2 generator -/

theorem oneHighFamilyNonzero_v2UpperTableClauses
    (a : Nat) (table : OneHighMissTable) :
    OneHighFamilyNonzero (oneHighFamilyV2UpperTableClauses a table) :=
  oneHighFamilyNonzero_runList _ _
    (oneHighFamilyNonzero_missDefinitionClauses a)
    (fun pair _ h => oneHighFamilyNonzero_tablePairStep h a table pair)

theorem oneHighFamilyNonzero_v2LexClauses
    (a : Nat) (table : OneHighMissTable) :
    OneHighFamilyNonzero (oneHighFamilyV2LexClauses a table) :=
  oneHighFamilyNonzero_runList _ _
    (oneHighFamilyNonzero_v2UpperTableClauses a table)
    (fun c _ h => oneHighFamilyNonzero_lexBlockStep h a c)

theorem oneHighFamilyNonzero_v2LowerTablePairStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st)
    (a : Nat) (table : OneHighMissTable) (pair : Nat × Nat) :
    OneHighFamilyNonzero
      (oneHighFamilyV2LowerTablePairStep a table pair st) := by
  have hv := oneHighFamilyNonzero_tableMissVars h a pair.1 pair.2
  simp only [oneHighFamilyV2LowerTablePairStep]
  generalize hm : oneHighFamilyTableMissVars a pair.1 pair.2 st = m at hv ⊢
  rcases m with ⟨vars, s⟩
  exact oneHighFamilyNonzero_equalsBlock hv.state vars hv.acc _

theorem oneHighFamilyNonzero_v2F1Clauses
    (a : Nat) (table : OneHighMissTable) :
    OneHighFamilyNonzero (oneHighFamilyV2F1Clauses a table) :=
  oneHighFamilyNonzero_runList _ _
    (oneHighFamilyNonzero_v2LexClauses a table)
    (fun pair _ h => oneHighFamilyNonzero_v2LowerTablePairStep h a table pair)

theorem oneHighFamilyNonzero_v2PairedCommonBlockStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st) (pair : Nat) :
    OneHighFamilyNonzero (oneHighFamilyV2PairedCommonBlockStep pair st) := by
  simp only [oneHighFamilyV2PairedCommonBlockStep]
  have hacc := oneHighNZ_foldl OneHighFamilyAccNonzero
    (fun accst x => (oneHighFamilyBlockVertices (2 * pair + 1)).foldl
      (fun accst z => oneHighFamilyCommonTseitinStep
        (2 * pair) (2 * pair + 1) x z accst) accst)
    (oneHighFamilyBlockVertices (2 * pair)) (#[], st)
    (oneHighFamilyAccNonzero_empty h) (by
      intro q x _ hq
      apply oneHighNZ_foldl OneHighFamilyAccNonzero _ _ _ hq
      intro r z _ hr
      exact oneHighFamilyNonzero_commonTseitinStep hr _ _ x z)
  exact hacc.state

theorem oneHighFamilyNonzero_v2PairedCommonClauses
    (a : Nat) (table : OneHighMissTable) :
    OneHighFamilyNonzero (oneHighFamilyV2PairedCommonClauses a table) :=
  oneHighFamilyNonzero_runList _ _
    (oneHighFamilyNonzero_v2F1Clauses a table)
    (fun pair _ h => oneHighFamilyNonzero_v2PairedCommonBlockStep h pair)

theorem oneHighFamilyNonzero_v2SaverStep
    {p : Array Int × OneHighFamilyGenState} (h : OneHighFamilyAccNonzero p)
    (x w : Nat) :
    OneHighFamilyAccNonzero (oneHighFamilyV2SaverStep x w p) := by
  rcases p with ⟨ss, st⟩
  simp only [oneHighFamilyV2SaverStep]
  generalize h₁ : oneHighFamilyAtomId (.saver x w) st = out₁
  rcases out₁ with ⟨s, st₁⟩
  obtain ⟨hs₁, ps⟩ := oneHighFamilyNonzero_atomId h.state h₁
  generalize h₂ : oneHighFamilyEdgeId x w st₁ = out₂
  rcases out₂ with ⟨exw, st₂⟩
  obtain ⟨hs₂, p₂⟩ := oneHighFamilyNonzero_edgeId hs₁ h₂
  generalize h₃ : oneHighFamilyAtomId (.miss w (x / 5 ^^^ 1)) st₂ = out₃
  rcases out₃ with ⟨mw, st₃⟩
  obtain ⟨hs₃, p₃⟩ := oneHighFamilyNonzero_atomId hs₂ h₃
  simp only [h₂, h₃]
  exact oneHighFamilyAccNonzero_push h.acc
    (oneHighFamilyNonzero_emit
      (oneHighFamilyNonzero_emit
        (oneHighFamilyNonzero_emit hs₃ (by nz_lits)) (by nz_lits))
      (by nz_lits)) ps

theorem oneHighFamilyNonzero_v2CollectPairedCommonStep
    {p : Array Int × OneHighFamilyGenState} (h : OneHighFamilyAccNonzero p)
    (x z : Nat) :
    OneHighFamilyAccNonzero
      (oneHighFamilyV2CollectPairedCommonStep x z p) := by
  rcases p with ⟨cs, st⟩
  simp only [oneHighFamilyV2CollectPairedCommonStep]
  generalize h₁ : oneHighFamilyCommonAtomId x z st = out₁
  rcases out₁ with ⟨c, st₁⟩
  obtain ⟨hs₁, pc⟩ := oneHighFamilyNonzero_commonAtomId h.state h₁
  exact oneHighFamilyAccNonzero_push h.acc hs₁ pc

theorem oneHighFamilyNonzero_v2F2VertexStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st) (a x : Nat) :
    OneHighFamilyNonzero (oneHighFamilyV2F2VertexStep a x st) := by
  simp only [oneHighFamilyV2F2VertexStep]
  generalize hsavers : (oneHighFamilyV2SaverVertices a x).foldl
    (fun accst w => oneHighFamilyV2SaverStep x w accst) (#[], st) = outS
  rcases outS with ⟨ss, stS⟩
  have hs : OneHighFamilyAccNonzero (ss, stS) := by
    rw [← hsavers]
    apply oneHighNZ_foldl OneHighFamilyAccNonzero _ _ _
      (oneHighFamilyAccNonzero_empty h)
    intro q w _ hq
    exact oneHighFamilyNonzero_v2SaverStep hq x w
  generalize hcommons : (oneHighFamilyBlockVertices (x / 5 ^^^ 1)).foldl
    (fun accst z => oneHighFamilyV2CollectPairedCommonStep x z accst)
    (#[], stS) = outC
  rcases outC with ⟨cs, stC⟩
  have hc : OneHighFamilyAccNonzero (cs, stC) := by
    rw [← hcommons]
    apply oneHighNZ_foldl OneHighFamilyAccNonzero _ _ _
      (oneHighFamilyAccNonzero_empty hs.state)
    intro q z _ hq
    exact oneHighFamilyNonzero_v2CollectPairedCommonStep hq x z
  apply oneHighFamilyNonzero_equalsBlock hc.state (cs ++ ss)
  intro l hl
  simp only [Array.mem_append] at hl
  rcases hl with hl | hl
  · exact hc.acc l hl
  · exact hs.acc l hl

theorem oneHighFamilyNonzero_v2F2Clauses
    (a : Nat) (table : OneHighMissTable) :
    OneHighFamilyNonzero (oneHighFamilyV2F2Clauses a table) :=
  oneHighFamilyNonzero_runList _ _
    (oneHighFamilyNonzero_v2PairedCommonClauses a table)
    (fun x _ h => oneHighFamilyNonzero_v2F2VertexStep h a x)

theorem oneHighFamilyNonzero_v2F3aCollect
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st) (pair : Nat) :
    OneHighFamilyAccNonzero (oneHighFamilyV2F3aCollect pair st) := by
  simp only [oneHighFamilyV2F3aCollect]
  apply oneHighNZ_foldl OneHighFamilyAccNonzero _ _ _
    (oneHighFamilyAccNonzero_empty h)
  intro q x _ hq
  apply oneHighNZ_foldl OneHighFamilyAccNonzero _ _ _ hq
  intro r z _ hr
  exact oneHighFamilyNonzero_v2CollectPairedCommonStep hr x z

theorem oneHighFamilyNonzero_v2F3aBlockStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st) (a pair : Nat) :
    OneHighFamilyNonzero (oneHighFamilyV2F3aBlockStep a pair st) := by
  have hc := oneHighFamilyNonzero_v2F3aCollect h pair
  simp only [oneHighFamilyV2F3aBlockStep, oneHighFamilyV2F3aFinish]
  exact oneHighFamilyNonzero_equalsBlock hc.state _ hc.acc _

theorem oneHighFamilyNonzero_v2F3aClauses
    (a : Nat) (table : OneHighMissTable) :
    OneHighFamilyNonzero (oneHighFamilyV2F3aClauses a table) :=
  oneHighFamilyNonzero_runList _ _
    (oneHighFamilyNonzero_v2F2Clauses a table)
    (fun pair _ h => oneHighFamilyNonzero_v2F3aBlockStep h a pair)

theorem oneHighFamilyNonzero_v2AppendEdge
    {p : Array Int × OneHighFamilyGenState} (h : OneHighFamilyAccNonzero p)
    (i j : Nat) :
    OneHighFamilyAccNonzero (oneHighFamilyV2AppendEdge i j p) := by
  rcases p with ⟨lits, st⟩
  simp only [oneHighFamilyV2AppendEdge]
  generalize h₁ : oneHighFamilyEdgeId i j st = out₁
  rcases out₁ with ⟨e, st₁⟩
  obtain ⟨hs₁, pe⟩ := oneHighFamilyNonzero_edgeId h.state h₁
  exact oneHighFamilyAccNonzero_push h.acc hs₁ pe

theorem oneHighFamilyNonzero_v2MaybeAppendEdge
    {p : Array Int × OneHighFamilyGenState} (h : OneHighFamilyAccNonzero p)
    (enabled : Bool) (i j : Nat) :
    OneHighFamilyAccNonzero (oneHighFamilyV2MaybeAppendEdge enabled i j p) := by
  simp only [oneHighFamilyV2MaybeAppendEdge]
  split
  · exact oneHighFamilyNonzero_v2AppendEdge h i j
  · exact h

theorem oneHighFamilyNonzero_v2FinishCommon
    {cs ors : Array Int} {st : OneHighFamilyGenState}
    (hcs : ∀ lit ∈ cs, lit ≠ 0) (hors : ∀ lit ∈ ors, lit ≠ 0)
    (h : OneHighFamilyNonzero st) (x z : Nat) :
    OneHighFamilyAccNonzero (oneHighFamilyV2FinishCommon cs ors x z st) := by
  simp only [oneHighFamilyV2FinishCommon]
  generalize hc : oneHighFamilyCommonAtomId x z st = outC
  rcases outC with ⟨c, stC⟩
  obtain ⟨hsC, pc⟩ := oneHighFamilyNonzero_commonAtomId h hc
  have hs₁ : OneHighFamilyNonzero
      (oneHighFamilyEmit (-(c : Int) :: ors.toList) stC).2 := by
    apply oneHighFamilyNonzero_emit hsC
    intro l hl
    simp only [List.mem_cons] at hl
    rcases hl with rfl | hl
    · omega
    · exact hors l (Array.mem_toList_iff.mp hl)
  have hs₂ : OneHighFamilyNonzero (ors.foldl
      (fun st lit => (oneHighFamilyEmit [-lit, (c : Int)] st).2)
      (oneHighFamilyEmit (-(c : Int) :: ors.toList) stC).2) := by
    apply oneHighNZ_arrayFoldl OneHighFamilyNonzero _ ors _ hs₁
    intro s lit hlit hs
    have := hors lit hlit
    exact oneHighFamilyNonzero_emit hs (by nz_lits)
  exact oneHighFamilyAccNonzero_push hcs hs₂ pc

theorem oneHighFamilyNonzero_v2UnpairedCommonStep
    {p : Array Int × OneHighFamilyGenState} (h : OneHighFamilyAccNonzero p)
    (profile a b x z : Nat) :
    OneHighFamilyAccNonzero
      (oneHighFamilyV2UnpairedCommonStep profile a b x z p) := by
  rcases p with ⟨cs, st⟩
  simp only [oneHighFamilyV2UnpairedCommonStep]
  generalize hmids : (oneHighFamilyV2UnpairedMidpoints a b).foldl
    (fun accst w => oneHighFamilyMidpointTseitinStep x z w accst)
    (#[], st) = outM
  rcases outM with ⟨ors, stM⟩
  have hsM : OneHighFamilyAccNonzero (ors, stM) := by
    rw [← hmids]
    apply oneHighNZ_foldl OneHighFamilyAccNonzero _ _ _
      (oneHighFamilyAccNonzero_empty h.state)
    intro q w _ hq
    exact oneHighFamilyNonzero_midpointTseitinStep hq x z w
  generalize hxedge : oneHighFamilyV2MaybeAppendEdge
    (oneHighFamilyVertexMatched profile x)
    (oneHighFamilyV2PartnerVertex x) z (ors, stM) = outX
  rcases outX with ⟨orsX, stX⟩
  have hsX : OneHighFamilyAccNonzero (orsX, stX) := by
    rw [← hxedge]
    exact oneHighFamilyNonzero_v2MaybeAppendEdge hsM _ _ _
  generalize hzedge : oneHighFamilyV2MaybeAppendEdge
    (oneHighFamilyVertexMatched profile z)
    x (oneHighFamilyV2PartnerVertex z) (orsX, stX) = outZ
  rcases outZ with ⟨orsZ, stZ⟩
  have hsZ : OneHighFamilyAccNonzero (orsZ, stZ) := by
    rw [← hzedge]
    exact oneHighFamilyNonzero_v2MaybeAppendEdge hsX _ _ _
  exact oneHighFamilyNonzero_v2FinishCommon h.acc hsZ.acc hsZ.state x z

theorem oneHighFamilyNonzero_v2F3bCollect
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st)
    (profile : Nat) (pair : Nat × Nat) :
    OneHighFamilyAccNonzero (oneHighFamilyV2F3bCollect profile pair st) := by
  simp only [oneHighFamilyV2F3bCollect]
  apply oneHighNZ_foldl OneHighFamilyAccNonzero _ _ _
    (oneHighFamilyAccNonzero_empty h)
  intro q x _ hq
  apply oneHighNZ_foldl OneHighFamilyAccNonzero _ _ _ hq
  intro r z _ hr
  exact oneHighFamilyNonzero_v2UnpairedCommonStep hr profile pair.1 pair.2 x z

theorem oneHighFamilyNonzero_v2F3bBlockStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyNonzero st)
    (profile : Nat) (table : OneHighMissTable) (pair : Nat × Nat) :
    OneHighFamilyNonzero
      (oneHighFamilyV2F3bBlockStep profile table pair st) := by
  have hc := oneHighFamilyNonzero_v2F3bCollect h profile pair
  simp only [oneHighFamilyV2F3bBlockStep, oneHighFamilyV2F3bFinish]
  split
  · exact oneHighFamilyNonzero_equalsBlock hc.state _ hc.acc _
  · exact hc.state

theorem oneHighFamilyNonzero_v2Clauses
    (profile : Nat) (table : OneHighMissTable) :
    OneHighFamilyNonzero (oneHighFamilyV2Clauses profile table) :=
  oneHighFamilyNonzero_runList _ _
    (oneHighFamilyNonzero_v2F3aClauses profile table)
    (fun pair _ h =>
      oneHighFamilyNonzero_v2F3bBlockStep h profile table pair)

/-! ## Certificate-facing consequences -/

/-- **Structural `nonzero`.** For every profile and every miss table, no
clause of the exact v2 one-high DIMACS formula contains the literal `0`.
Axioms: standard only (no `native_decide`). -/
theorem oneHighFamilyV2Clauses_nonzero
    (profile : Nat) (table : OneHighMissTable) :
    ∀ clause ∈ (oneHighFamilyV2Clauses profile table).clauses,
      DimacsClauseNonzero clause :=
  (oneHighFamilyNonzero_v2Clauses profile table).clauses

/-- The `nonzero` field of `OneHighFamilyV2CheckedUnsat`, discharged for every
row of the 13,351-row one-high capacity inventory (indeed for every table). -/
theorem oneHighCapacityInventory_nonzero :
    ∀ (profile : Fin 5) table,
      table ∈ oneHighCapacityInventoryTables profile →
        ∀ clause ∈ (oneHighFamilyV2Clauses profile.val table).clauses,
          DimacsClauseNonzero clause :=
  fun profile table _ => oneHighFamilyV2Clauses_nonzero profile.val table

/-- Only the unsatisfiability field of `OneHighFamilyV2CheckedUnsat` is a
genuine assumption. -/
theorem oneHighFamilyV2CheckedUnsat_of_unsat
    {profile : Nat} {table : OneHighMissTable}
    (hunsat : ∀ assignment : Nat → Bool,
      ¬(oneHighFamilyV2SatCnf profile table).Sat assignment) :
    OneHighFamilyV2CheckedUnsat profile table :=
  ⟨oneHighFamilyV2Clauses_nonzero profile table, hunsat⟩

/-- Inventory-wide form: the unsatisfiability statements alone supply the
`hOne` hypothesis of the order-49 capstones
(`not_c4FreeMinDegreeWitness_fortyNine_seven_of_h1_h7Evidence` and its
corollaries). -/
theorem oneHighCapacityInventory_checked_of_unsat
    (hUnsat : ∀ (profile : Fin 5) table,
      table ∈ oneHighCapacityInventoryTables profile →
        ∀ assignment : Nat → Bool,
          ¬(oneHighFamilyV2SatCnf profile.val table).Sat assignment) :
    ∀ (profile : Fin 5) table,
      table ∈ oneHighCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table :=
  fun profile table htable =>
    oneHighFamilyV2CheckedUnsat_of_unsat (hUnsat profile table htable)

end Erdos85

#print axioms Erdos85.oneHighFamilyV2Clauses_nonzero
#print axioms Erdos85.oneHighCapacityInventory_nonzero
#print axioms Erdos85.oneHighFamilyV2CheckedUnsat_of_unsat
#print axioms Erdos85.oneHighCapacityInventory_checked_of_unsat
