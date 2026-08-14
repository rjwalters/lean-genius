import Proofs.Erdos85OneHighOrbitCnf

/-!
# Exact fleet-v2 one-high generator

The durable orbit certificates were produced by `sweep_worker.py` with
`arm:v2`.  Its clause order is not the PURE-family order: upper table pins
precede lex, and the reverse-direction F1 pins follow lex.  This file starts
a separate byte-exact transcription rather than attempting to reuse proofs
against a merely equisatisfiable formula.
-/

namespace Erdos85

/-- Worker-v2 through its first table pass:
base through miss definitions, then `c < j` exact miss-count blocks. -/
def oneHighFamilyV2UpperTableClauses
    (a : Nat) (table : OneHighMissTable) : OneHighFamilyGenState :=
  oneHighFamilyRunList oneHighFamilyTablePairs
    (oneHighFamilyTablePairStep a table)
    (oneHighFamilyMissDefinitionClauses a)

theorem oneHighFamilyIdsSound_v2UpperTableClauses
    (a : Nat) (table : OneHighMissTable) :
    OneHighFamilyIdsSound (oneHighFamilyV2UpperTableClauses a table) := by
  exact oneHighFamilyIdsSound_runList _ _
    (oneHighFamilyIdsSound_missDefinitionClauses a)
    (fun pair st h => oneHighFamilyIdsSound_tablePairStep h a table pair)

/-- The worker's lex segment, now applied after upper table counters. -/
def oneHighFamilyV2LexClauses
    (a : Nat) (table : OneHighMissTable) : OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range 8) (oneHighFamilyLexBlockStep a)
    (oneHighFamilyV2UpperTableClauses a table)

theorem oneHighFamilyIdsSound_v2LexClauses
    (a : Nat) (table : OneHighMissTable) :
    OneHighFamilyIdsSound (oneHighFamilyV2LexClauses a table) := by
  exact oneHighFamilyIdsSound_runList _ _
    (oneHighFamilyIdsSound_v2UpperTableClauses a table)
    (fun c st h => oneHighFamilyIdsSound_lexBlockStep h a c)

/-- Reverse-direction non-mate branch pairs in worker nested-loop order. -/
def oneHighFamilyV2LowerTablePairs : List (Nat × Nat) :=
  (List.range 8).flatMap fun c =>
    (List.range 8).filterMap fun j =>
      if j < c ∧ j != (c ^^^ 1) then some (c, j) else none

theorem oneHighFamilyV2LowerTablePairs_size :
    oneHighFamilyV2LowerTablePairs.length = 24 := by
  native_decide

/-- F1 reverse pin.  The table is stored on unordered coordinates, hence the
worker's `m_of(c,j)` at `j<c` reads `table j c`. -/
def oneHighFamilyV2LowerTablePairStep
    (a : Nat) (table : OneHighMissTable) (pair : Nat × Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  let (vars, st) := oneHighFamilyTableMissVars a pair.1 pair.2 st
  oneHighFamilyEqualsBlock vars (table pair.2 pair.1) st

theorem oneHighFamilyIdsSound_v2LowerTablePairStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (a : Nat) (table : OneHighMissTable) (pair : Nat × Nat) :
    OneHighFamilyIdsSound
      (oneHighFamilyV2LowerTablePairStep a table pair st) := by
  simp only [oneHighFamilyV2LowerTablePairStep]
  exact oneHighFamilyIdsSound_equalsBlock
    (oneHighFamilyIdsSound_tableMissVars h a pair.1 pair.2) _ _

/-- Exact worker-v2 prefix through F1 (both directed table pin families). -/
def oneHighFamilyV2F1Clauses
    (a : Nat) (table : OneHighMissTable) : OneHighFamilyGenState :=
  oneHighFamilyRunList oneHighFamilyV2LowerTablePairs
    (oneHighFamilyV2LowerTablePairStep a table)
    (oneHighFamilyV2LexClauses a table)

theorem oneHighFamilyIdsSound_v2F1Clauses
    (a : Nat) (table : OneHighMissTable) :
    OneHighFamilyIdsSound (oneHighFamilyV2F1Clauses a table) := by
  exact oneHighFamilyIdsSound_runList _ _
    (oneHighFamilyIdsSound_v2LexClauses a table)
    (fun pair st h =>
      oneHighFamilyIdsSound_v2LowerTablePairStep h a table pair)

/-! ## F2 paired-fan equalities -/

/-- Emit the paired-product common Tseitin definitions, but defer their
cardinality block until after all F2 vertex equalities, matching v2 order. -/
def oneHighFamilyV2PairedCommonBlockStep (pair : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  let bi := 2 * pair
  let bj := bi + 1
  ((oneHighFamilyBlockVertices bi).foldl (fun accst x =>
    (oneHighFamilyBlockVertices bj).foldl
      (fun accst z => oneHighFamilyCommonTseitinStep bi bj x z accst)
      accst) (#[], st)).2

theorem oneHighFamilyIdsSound_v2PairedCommonBlockStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (pair : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyV2PairedCommonBlockStep pair st) := by
  simp only [oneHighFamilyV2PairedCommonBlockStep]
  exact oneHighFamilyIdsSound_foldlAccum
    (oneHighFamilyBlockVertices (2 * pair))
    (fun x accst => (oneHighFamilyBlockVertices (2 * pair + 1)).foldl
      (fun accst z => oneHighFamilyCommonTseitinStep
        (2 * pair) (2 * pair + 1) x z accst) accst)
    #[] h (by
      intro x cs st hx
      exact oneHighFamilyIdsSound_foldlAccum
        (oneHighFamilyBlockVertices (2 * pair + 1))
        (fun z accst => oneHighFamilyCommonTseitinStep
          (2 * pair) (2 * pair + 1) x z accst)
        cs hx (by
          intro z cs st hz
          exact oneHighFamilyIdsSound_commonTseitinStep hz cs _ _ x z))

def oneHighFamilyV2PairedCommonClauses
    (a : Nat) (table : OneHighMissTable) : OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range 4)
    oneHighFamilyV2PairedCommonBlockStep
    (oneHighFamilyV2F1Clauses a table)

theorem oneHighFamilyIdsSound_v2PairedCommonClauses
    (a : Nat) (table : OneHighMissTable) :
    OneHighFamilyIdsSound
      (oneHighFamilyV2PairedCommonClauses a table) := by
  exact oneHighFamilyIdsSound_runList _ _
    (oneHighFamilyIdsSound_v2F1Clauses a table)
    (fun pair st h => oneHighFamilyIdsSound_v2PairedCommonBlockStep h pair)

def oneHighFamilyV2SaverVertices (a x : Nat) : List Nat :=
  (List.range 40).filter fun w =>
    oneHighFamilyVertexMatched a w &&
      decide (w / 5 ≠ x / 5 ∧ w / 5 ≠ (x / 5 ^^^ 1))

def oneHighFamilyV2SaverStep (x w : Nat)
    (accst : Array Int × OneHighFamilyGenState) :
    Array Int × OneHighFamilyGenState :=
  let (ss, st) := accst
  let (s, st) := oneHighFamilyAtomId (.saver x w) st
  let (exw, st) := oneHighFamilyEdgeId x w st
  let (mw, st) := oneHighFamilyAtomId (.miss w (x / 5 ^^^ 1)) st
  let st := (oneHighFamilyEmit [-(s : Int), (exw : Int)] st).2
  let st := (oneHighFamilyEmit [-(s : Int), (mw : Int)] st).2
  let st := (oneHighFamilyEmit
    [(s : Int), -(exw : Int), -(mw : Int)] st).2
  (ss.push (s : Int), st)

theorem oneHighFamilyIdsSound_v2SaverStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (ss : Array Int) (x w : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyV2SaverStep x w (ss, st)).2 := by
  simp only [oneHighFamilyV2SaverStep]
  generalize h₁ : oneHighFamilyAtomId (.saver x w) st = out₁
  rcases out₁ with ⟨s, st₁⟩
  have hs₁ := oneHighFamilyIdsSound_atomId h (.saver x w)
  rw [h₁] at hs₁
  generalize h₂ : oneHighFamilyEdgeId x w st₁ = out₂
  rcases out₂ with ⟨exw, st₂⟩
  have hs₂ := oneHighFamilyIdsSound_edgeId hs₁ x w
  rw [h₂] at hs₂
  generalize h₃ : oneHighFamilyAtomId (.miss w (x / 5 ^^^ 1)) st₂ = out₃
  rcases out₃ with ⟨mw, st₃⟩
  have hs₃ := oneHighFamilyIdsSound_atomId hs₂
    (.miss w (x / 5 ^^^ 1))
  rw [h₃] at hs₃
  simp only [h₂, h₃]
  exact oneHighFamilyIdsSound_emit
    (oneHighFamilyIdsSound_emit
      (oneHighFamilyIdsSound_emit hs₃ _) _) _

def oneHighFamilyV2CollectPairedCommonStep (x z : Nat)
    (accst : Array Int × OneHighFamilyGenState) :
    Array Int × OneHighFamilyGenState :=
  let (cs, st) := accst
  let (c, st) := oneHighFamilyCommonAtomId x z st
  (cs.push (c : Int), st)

theorem oneHighFamilyIdsSound_v2CollectPairedCommonStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (cs : Array Int) (x z : Nat) :
    OneHighFamilyIdsSound
      (oneHighFamilyV2CollectPairedCommonStep x z (cs, st)).2 := by
  exact oneHighFamilyIdsSound_commonAtomId h x z

def oneHighFamilyV2F2VertexStep (a x : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  let (ss, st) := (oneHighFamilyV2SaverVertices a x).foldl
    (fun accst w => oneHighFamilyV2SaverStep x w accst) (#[], st)
  let mateBlock := x / 5 ^^^ 1
  let (cs, st) := (oneHighFamilyBlockVertices mateBlock).foldl
    (fun accst z => oneHighFamilyV2CollectPairedCommonStep x z accst)
    (#[], st)
  oneHighFamilyEqualsBlock (cs ++ ss)
    (oneHighFamilyFarDegreeBound a x) st

theorem oneHighFamilyIdsSound_v2F2VertexStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (a x : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyV2F2VertexStep a x st) := by
  simp only [oneHighFamilyV2F2VertexStep]
  generalize hsavers : (oneHighFamilyV2SaverVertices a x).foldl
    (fun accst w => oneHighFamilyV2SaverStep x w accst) (#[], st) = outS
  rcases outS with ⟨ss, stS⟩
  have hs := oneHighFamilyIdsSound_foldlAccum
    (oneHighFamilyV2SaverVertices a x)
    (fun w accst => oneHighFamilyV2SaverStep x w accst)
    #[] h (by
      intro w ss st hw
      exact oneHighFamilyIdsSound_v2SaverStep hw ss x w)
  rw [hsavers] at hs
  generalize hcommons : (oneHighFamilyBlockVertices (x / 5 ^^^ 1)).foldl
    (fun accst z => oneHighFamilyV2CollectPairedCommonStep x z accst)
    (#[], stS) = outC
  rcases outC with ⟨cs, stC⟩
  have hc := oneHighFamilyIdsSound_foldlAccum
    (oneHighFamilyBlockVertices (x / 5 ^^^ 1))
    (fun z accst => oneHighFamilyV2CollectPairedCommonStep x z accst)
    #[] hs (by
      intro z cs st hz
      exact oneHighFamilyIdsSound_v2CollectPairedCommonStep hz cs x z)
  rw [hcommons] at hc
  exact oneHighFamilyIdsSound_equalsBlock hc (cs ++ ss) _

def oneHighFamilyV2F2Clauses
    (a : Nat) (table : OneHighMissTable) : OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range 40) (oneHighFamilyV2F2VertexStep a)
    (oneHighFamilyV2PairedCommonClauses a table)

theorem oneHighFamilyIdsSound_v2F2Clauses
    (a : Nat) (table : OneHighMissTable) :
    OneHighFamilyIdsSound (oneHighFamilyV2F2Clauses a table) := by
  exact oneHighFamilyIdsSound_runList _ _
    (oneHighFamilyIdsSound_v2PairedCommonClauses a table)
    (fun x st h => oneHighFamilyIdsSound_v2F2VertexStep h a x)

/-! ## F3a paired-product totals -/

def oneHighFamilyV2F3aCollect (pair : Nat)
    (st : OneHighFamilyGenState) : Array Int × OneHighFamilyGenState :=
  let bi := 2 * pair
  let bj := bi + 1
  (oneHighFamilyBlockVertices bi).foldl (fun accst x =>
    (oneHighFamilyBlockVertices bj).foldl
      (fun accst z => oneHighFamilyV2CollectPairedCommonStep x z accst)
      accst) (#[], st)

def oneHighFamilyV2F3aFinish (a pair : Nat)
    (input : Array Int × OneHighFamilyGenState) : OneHighFamilyGenState :=
  let bi := 2 * pair
  let bj := bi + 1
  let bound := 30 - 2 * oneHighFamilyInternalEdgesNat a bi -
    2 * oneHighFamilyInternalEdgesNat a bj
  oneHighFamilyEqualsBlock input.1 bound input.2

def oneHighFamilyV2F3aBlockStep (a pair : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  oneHighFamilyV2F3aFinish a pair
    (oneHighFamilyV2F3aCollect pair st)

theorem oneHighFamilyIdsSound_v2F3aBlockStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (a pair : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyV2F3aBlockStep a pair st) := by
  simp only [oneHighFamilyV2F3aBlockStep, oneHighFamilyV2F3aFinish,
    oneHighFamilyV2F3aCollect]
  generalize hcommons : (oneHighFamilyBlockVertices (2 * pair)).foldl
    (fun accst x => (oneHighFamilyBlockVertices (2 * pair + 1)).foldl
      (fun accst z => oneHighFamilyV2CollectPairedCommonStep x z accst)
      accst) (#[], st) = out
  rcases out with ⟨cs, stC⟩
  apply oneHighFamilyIdsSound_equalsBlock _ cs _
  have hc := oneHighFamilyIdsSound_foldlAccum
    (oneHighFamilyBlockVertices (2 * pair))
    (fun x accst => (oneHighFamilyBlockVertices (2 * pair + 1)).foldl
      (fun accst z => oneHighFamilyV2CollectPairedCommonStep x z accst)
      accst) #[] h (by
        intro x cs st hx
        exact oneHighFamilyIdsSound_foldlAccum
          (oneHighFamilyBlockVertices (2 * pair + 1))
          (fun z accst => oneHighFamilyV2CollectPairedCommonStep x z accst)
          cs hx (by
            intro z cs st hz
            exact oneHighFamilyIdsSound_v2CollectPairedCommonStep hz cs x z))
  rw [hcommons] at hc
  exact hc

def oneHighFamilyV2F3aClauses
    (a : Nat) (table : OneHighMissTable) : OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range 4)
    (oneHighFamilyV2F3aBlockStep a) (oneHighFamilyV2F2Clauses a table)

theorem oneHighFamilyIdsSound_v2F3aClauses
    (a : Nat) (table : OneHighMissTable) :
    OneHighFamilyIdsSound (oneHighFamilyV2F3aClauses a table) := by
  exact oneHighFamilyIdsSound_runList _ _
    (oneHighFamilyIdsSound_v2F2Clauses a table)
    (fun pair st h => oneHighFamilyIdsSound_v2F3aBlockStep h a pair)

/-! ## F3b unpaired-product totals -/

def oneHighFamilyTableGet (table : OneHighMissTable) (c j : Nat) : Nat :=
  table (min c j) (max c j)

def oneHighFamilyV2UnpairedMidpoints (a b : Nat) : List Nat :=
  (List.range 40).filter fun w =>
    w / 5 ≠ a ∧ w / 5 ≠ b ∧
      w / 5 ≠ (a ^^^ 1) ∧ w / 5 ≠ (b ^^^ 1)

def oneHighFamilyV2PartnerVertex (x : Nat) : Nat :=
  if x % 5 = 0 ∨ x % 5 = 2 then x + 1 else x - 1

def oneHighFamilyV2AppendEdge (i j : Nat)
    (accst : Array Int × OneHighFamilyGenState) :
    Array Int × OneHighFamilyGenState :=
  let (lits, st) := accst
  let (e, st) := oneHighFamilyEdgeId i j st
  (lits.push (e : Int), st)

theorem oneHighFamilyIdsSound_v2AppendEdge
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (lits : Array Int) (i j : Nat) :
    OneHighFamilyIdsSound (oneHighFamilyV2AppendEdge i j (lits, st)).2 := by
  exact oneHighFamilyIdsSound_edgeId h i j

def oneHighFamilyV2MaybeAppendEdge (enabled : Bool) (i j : Nat)
    (accst : Array Int × OneHighFamilyGenState) :
    Array Int × OneHighFamilyGenState :=
  if enabled then oneHighFamilyV2AppendEdge i j accst else accst

theorem oneHighFamilyIdsSound_v2MaybeAppendEdge
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (lits : Array Int) (enabled : Bool) (i j : Nat) :
    OneHighFamilyIdsSound
      (oneHighFamilyV2MaybeAppendEdge enabled i j (lits, st)).2 := by
  simp only [oneHighFamilyV2MaybeAppendEdge]
  split
  · exact oneHighFamilyIdsSound_v2AppendEdge h lits i j
  · exact h

def oneHighFamilyV2FinishCommon (cs ors : Array Int) (x z : Nat)
    (st : OneHighFamilyGenState) : Array Int × OneHighFamilyGenState :=
  let (c, st) := oneHighFamilyCommonAtomId x z st
  let st := (oneHighFamilyEmit (-(c : Int) :: ors.toList) st).2
  let st := ors.foldl
    (fun st lit => (oneHighFamilyEmit [-lit, (c : Int)] st).2) st
  (cs.push (c : Int), st)

theorem oneHighFamilyIdsSound_v2FinishCommon
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (cs ors : Array Int) (x z : Nat) :
    OneHighFamilyIdsSound
      (oneHighFamilyV2FinishCommon cs ors x z st).2 := by
  simp only [oneHighFamilyV2FinishCommon]
  generalize hc : oneHighFamilyCommonAtomId x z st = outC
  rcases outC with ⟨c, stC⟩
  have hsC := oneHighFamilyIdsSound_commonAtomId h x z
  rw [hc] at hsC
  exact oneHighFamilyIdsSound_arrayFoldl ors
    (fun st lit => (oneHighFamilyEmit [-lit, (c : Int)] st).2)
    (oneHighFamilyIdsSound_emit hsC _) (by
      intro st lit hs
      exact oneHighFamilyIdsSound_emit hs _)

def oneHighFamilyV2UnpairedCommonStep
    (profile a b x z : Nat)
    (accst : Array Int × OneHighFamilyGenState) :
    Array Int × OneHighFamilyGenState :=
  let (cs, st) := accst
  let (ors, st) := (oneHighFamilyV2UnpairedMidpoints a b).foldl
    (fun accst w => oneHighFamilyMidpointTseitinStep x z w accst)
    (#[], st)
  let (ors, st) := oneHighFamilyV2MaybeAppendEdge
    (oneHighFamilyVertexMatched profile x)
    (oneHighFamilyV2PartnerVertex x) z (ors, st)
  let (ors, st) := oneHighFamilyV2MaybeAppendEdge
    (oneHighFamilyVertexMatched profile z)
    x (oneHighFamilyV2PartnerVertex z) (ors, st)
  oneHighFamilyV2FinishCommon cs ors x z st

theorem oneHighFamilyIdsSound_v2UnpairedCommonStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (cs : Array Int) (profile a b x z : Nat) :
    OneHighFamilyIdsSound
      (oneHighFamilyV2UnpairedCommonStep profile a b x z (cs, st)).2 := by
  simp only [oneHighFamilyV2UnpairedCommonStep]
  generalize hmids : (oneHighFamilyV2UnpairedMidpoints a b).foldl
    (fun accst w => oneHighFamilyMidpointTseitinStep x z w accst)
    (#[], st) = outM
  rcases outM with ⟨ors, stM⟩
  have hsM := oneHighFamilyIdsSound_foldlAccum
    (oneHighFamilyV2UnpairedMidpoints a b)
    (fun w accst => oneHighFamilyMidpointTseitinStep x z w accst)
    #[] h (by
      intro w ors st hw
      exact oneHighFamilyIdsSound_midpointTseitinStep hw ors x z w)
  rw [hmids] at hsM
  generalize hxedge : oneHighFamilyV2MaybeAppendEdge
    (oneHighFamilyVertexMatched profile x)
    (oneHighFamilyV2PartnerVertex x) z (ors, stM) = outX
  rcases outX with ⟨orsX, stX⟩
  have hsX := oneHighFamilyIdsSound_v2MaybeAppendEdge hsM ors
    (oneHighFamilyVertexMatched profile x)
    (oneHighFamilyV2PartnerVertex x) z
  rw [hxedge] at hsX
  generalize hzedge : oneHighFamilyV2MaybeAppendEdge
    (oneHighFamilyVertexMatched profile z)
    x (oneHighFamilyV2PartnerVertex z) (orsX, stX) = outZ
  rcases outZ with ⟨orsZ, stZ⟩
  have hsZ := oneHighFamilyIdsSound_v2MaybeAppendEdge hsX orsX
    (oneHighFamilyVertexMatched profile z)
    x (oneHighFamilyV2PartnerVertex z)
  rw [hzedge] at hsZ
  exact oneHighFamilyIdsSound_v2FinishCommon hsZ cs orsZ x z

def oneHighFamilyV2F3bCollect
  (profile : Nat) (pair : Nat × Nat)
    (st : OneHighFamilyGenState) : Array Int × OneHighFamilyGenState :=
  (oneHighFamilyBlockVertices pair.1).foldl (fun accst x =>
    (oneHighFamilyBlockVertices pair.2).foldl (fun accst z =>
      oneHighFamilyV2UnpairedCommonStep
        profile pair.1 pair.2 x z accst) accst)
    (#[], st)

def oneHighFamilyV2F3bFinish
    (table : OneHighMissTable) (pair : Nat × Nat)
    (input : Array Int × OneHighFamilyGenState) : OneHighFamilyGenState :=
  let bound := 20 + oneHighFamilyTableGet table pair.1 (pair.2 ^^^ 1) +
    oneHighFamilyTableGet table pair.2 (pair.1 ^^^ 1)
  if bound ≤ input.1.size then
    oneHighFamilyEqualsBlock input.1 bound input.2 else input.2

def oneHighFamilyV2F3bBlockStep
    (profile : Nat) (table : OneHighMissTable) (pair : Nat × Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  oneHighFamilyV2F3bFinish table pair
    (oneHighFamilyV2F3bCollect profile pair st)

theorem oneHighFamilyIdsSound_v2F3bBlockStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (profile : Nat) (table : OneHighMissTable) (pair : Nat × Nat) :
    OneHighFamilyIdsSound
      (oneHighFamilyV2F3bBlockStep profile table pair st) := by
  simp only [oneHighFamilyV2F3bBlockStep, oneHighFamilyV2F3bFinish,
    oneHighFamilyV2F3bCollect]
  generalize hcommons : (oneHighFamilyBlockVertices pair.1).foldl
    (fun accst x => (oneHighFamilyBlockVertices pair.2).foldl
      (fun accst z => oneHighFamilyV2UnpairedCommonStep
        profile pair.1 pair.2 x z accst) accst) (#[], st) = out
  rcases out with ⟨cs, stC⟩
  have hc := oneHighFamilyIdsSound_foldlAccum
    (oneHighFamilyBlockVertices pair.1)
    (fun x accst => (oneHighFamilyBlockVertices pair.2).foldl
      (fun accst z => oneHighFamilyV2UnpairedCommonStep
        profile pair.1 pair.2 x z accst) accst) #[] h (by
      intro x cs st hx
      exact oneHighFamilyIdsSound_foldlAccum
        (oneHighFamilyBlockVertices pair.2)
        (fun z accst => oneHighFamilyV2UnpairedCommonStep
          profile pair.1 pair.2 x z accst)
        cs hx (by
          intro z cs st hz
          exact oneHighFamilyIdsSound_v2UnpairedCommonStep
            hz cs profile pair.1 pair.2 x z))
  rw [hcommons] at hc
  split
  · exact oneHighFamilyIdsSound_equalsBlock hc cs _
  · exact hc

/-- Complete exact generator for `sweep_worker.py` with `arm:v2`. -/
def oneHighFamilyV2Clauses
    (profile : Nat) (table : OneHighMissTable) : OneHighFamilyGenState :=
  oneHighFamilyRunList oneHighFamilyTablePairs
    (oneHighFamilyV2F3bBlockStep profile table)
    (oneHighFamilyV2F3aClauses profile table)

theorem oneHighFamilyIdsSound_v2Clauses
    (profile : Nat) (table : OneHighMissTable) :
    OneHighFamilyIdsSound (oneHighFamilyV2Clauses profile table) := by
  exact oneHighFamilyIdsSound_runList _ _
    (oneHighFamilyIdsSound_v2F3aClauses profile table)
    (fun pair st h =>
      oneHighFamilyIdsSound_v2F3bBlockStep h profile table pair)

def oneHighFamilyV2SatCnf
    (profile : Nat) (table : OneHighMissTable) : Std.Sat.CNF Nat where
  clauses := dimacsFormulaToSatClauses
    (oneHighFamilyV2Clauses profile table).clauses

end Erdos85
