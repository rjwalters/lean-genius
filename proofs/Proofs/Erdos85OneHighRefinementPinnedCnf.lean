import Proofs.Erdos85OneHighFamilyCnfSatisfaction
import Proofs.Erdos85OneHighPairingRefinement

/-! # Pairing-refinement pinned one-high CNF

The existing family generator has assigned canonical coordinates to every
internal matching edge by the end of `oneHighFamilyLexClauses`.  This module
extends that checked prefix with positive units fixing the two miss labels of
each canonical edge to an explicit pairing refinement.  It deliberately
stops before the F2 paired-product blocks.
-/

namespace Erdos85

/-- Add the two positive miss-variable units belonging to canonical edge
`edge` of source block `source`.  Out-of-range coordinates use a harmless
default; the outer generator only calls this at actual row indices. -/
def oneHighFamilyRefinementPinEdgeStep
    (refinement : List (List OneHighLabelPair)) (source edge : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  let pair := (refinement.getD source []).getD edge (0, 0)
  let leftVertex := 5 * source + 2 * edge
  let rightVertex := leftVertex + 1
  let (leftId, st) := oneHighFamilyAtomId
    (.miss leftVertex pair.1.val) st
  let st := (oneHighFamilyEmit [(leftId : Int)] st).2
  let (rightId, st) := oneHighFamilyAtomId
    (.miss rightVertex pair.2.val) st
  (oneHighFamilyEmit [(rightId : Int)] st).2

theorem oneHighFamilyIdsSound_refinementPinEdgeStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (refinement : List (List OneHighLabelPair)) (source edge : Nat) :
    OneHighFamilyIdsSound
      (oneHighFamilyRefinementPinEdgeStep refinement source edge st) := by
  simp only [oneHighFamilyRefinementPinEdgeStep]
  generalize hleft : oneHighFamilyAtomId
    (.miss (5 * source + 2 * edge)
      ((refinement.getD source []).getD edge (0, 0)).1.val) st = left
  rcases left with ⟨leftId, st₁⟩
  dsimp only
  have hs₁ := oneHighFamilyIdsSound_atomId h
    (.miss (5 * source + 2 * edge)
      ((refinement.getD source []).getD edge (0, 0)).1.val)
  rw [hleft] at hs₁
  have hs₂ := oneHighFamilyIdsSound_emit hs₁ [(leftId : Int)]
  generalize hright : oneHighFamilyAtomId
    (.miss (5 * source + 2 * edge + 1)
      ((refinement.getD source []).getD edge (0, 0)).2.val)
      (oneHighFamilyEmit [(leftId : Int)] st₁).2 = right
  rcases right with ⟨rightId, st₂⟩
  dsimp only
  have hs₃ := oneHighFamilyIdsSound_atomId hs₂
    (.miss (5 * source + 2 * edge + 1)
      ((refinement.getD source []).getD edge (0, 0)).2.val)
  rw [hright] at hs₃
  exact oneHighFamilyIdsSound_emit hs₃ [(rightId : Int)]

/-- Pin every canonical internal edge in one source row. -/
def oneHighFamilyRefinementPinRowStep
    (refinement : List (List OneHighLabelPair)) (source : Nat)
    (st : OneHighFamilyGenState) : OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range (refinement.getD source []).length)
    (oneHighFamilyRefinementPinEdgeStep refinement source) st

theorem oneHighFamilyIdsSound_refinementPinRowStep
    {st : OneHighFamilyGenState} (h : OneHighFamilyIdsSound st)
    (refinement : List (List OneHighLabelPair)) (source : Nat) :
    OneHighFamilyIdsSound
      (oneHighFamilyRefinementPinRowStep refinement source st) := by
  exact oneHighFamilyIdsSound_runList _ _ h
    (fun edge st hs =>
      oneHighFamilyIdsSound_refinementPinEdgeStep hs refinement source edge)

/-- The lex-prefix family CNF with all eight refinement rows pinned. -/
def oneHighFamilyRefinementClauses
    (profile : Nat) (refinement : List (List OneHighLabelPair)) :
    OneHighFamilyGenState :=
  oneHighFamilyRunList (List.range 8)
    (oneHighFamilyRefinementPinRowStep refinement)
    (oneHighFamilyLexClauses profile)

theorem oneHighFamilyIdsSound_refinementClauses
    (profile : Nat) (refinement : List (List OneHighLabelPair)) :
    OneHighFamilyIdsSound
      (oneHighFamilyRefinementClauses profile refinement) := by
  exact oneHighFamilyIdsSound_runList _ _
    (oneHighFamilyIdsSound_lexClauses profile)
    (fun source st hs =>
      oneHighFamilyIdsSound_refinementPinRowStep hs refinement source)

def oneHighFamilyRefinementSatCnf
    (profile : Nat) (refinement : List (List OneHighLabelPair)) :
    Std.Sat.CNF Nat where
  clauses := dimacsFormulaToSatClauses
    (oneHighFamilyRefinementClauses profile refinement).clauses

end Erdos85

#print axioms Erdos85.oneHighFamilyIdsSound_refinementClauses
