import Proofs.Erdos85MuNegThreeZeroFiveOwnerCnf
import Proofs.Erdos85MuNegOneOneFourOwnerCnfSemantics

/-!
# Semantic socket for the mu=-3 `(0,5)` owner-grid CNFs

This is the graph-facing half of the h305 certificate interface.  The five
non-cross clause families are shared verbatim with the mature h114 owner
model.  The cross family differs only in its exact counts: two same-sign
defect entries and three opposite-sign defect entries in every row and
column.
-/

namespace Erdos85

open Std Sat

structure MuNegThreeZeroFiveOwnerConstraintSemantics
    (uTri vTri sigma : Bool) (val : DimacsValuation) : Prop where
  cross_rows : ∀ clause ∈ muNegThreeZeroFiveCrossRowClauses sigma,
    dimacsClauseSatisfied val clause
  cross_columns : ∀ clause ∈ muNegThreeZeroFiveCrossColClauses sigma,
    dimacsClauseSatisfied val clause
  intertwining : ∀ clause ∈ muNegOneIntertwineClauses,
    dimacsClauseSatisfied val clause
  hit_activity : ∀ clause ∈
    muNegOneHitActivityClauses uTri vTri (muNegOneHitPairs uTri vTri),
    dimacsClauseSatisfied val clause
  service : ∀ clause ∈
    muNegOneServiceClauses uTri vTri (muNegOneHitPairs uTri vTri),
    dimacsClauseSatisfied val clause
  exterior_c4 : ∀ clause ∈
    muNegOneC4Clauses uTri vTri (muNegOneHitPairs uTri vTri),
    dimacsClauseSatisfied val clause

/-- Semantic content of one h305 exact-three block.  The graph adapter proves
this field from the exact opposite-sign cardinality; keeping the clause
family bundled makes that adapter independent of the generator's list
normal form. -/
structure MuNegThreeExactlyThreeSemantics
    (val : DimacsValuation) (lits : List Int) : Prop where
  clauses : ∀ clause ∈ muNegThreeExactlyThree lits,
    dimacsClauseSatisfied val clause

theorem muNegThreeExactlyThree_satisfied
    {val : DimacsValuation} {lits : List Int}
    (h : MuNegThreeExactlyThreeSemantics val lits) :
    ∀ clause ∈ muNegThreeExactlyThree lits,
      dimacsClauseSatisfied val clause := by
  exact h.clauses

theorem muNegThreeZeroFiveCrossRowClauses_satisfied
    {sigma : Bool} {val : DimacsValuation}
    (hsame : ∀ i, i < 8 -> MuNegOneExactlyTwoSemantics val
      (((List.range 8).filter fun j =>
        muNegOneSign sigma i == muNegOneSign sigma (8 + j)).map fun j =>
          Int.ofNat (muNegOneDVar i j)))
    (hopp : ∀ i, i < 8 -> MuNegThreeExactlyThreeSemantics val
      (((List.range 8).filter fun j =>
        !(muNegOneSign sigma i == muNegOneSign sigma (8 + j))).map fun j =>
          Int.ofNat (muNegOneDVar i j))) :
    ∀ clause ∈ muNegThreeZeroFiveCrossRowClauses sigma,
      dimacsClauseSatisfied val clause := by
  intro clause hclause
  simp only [muNegThreeZeroFiveCrossRowClauses, List.mem_flatMap,
    List.mem_range, List.mem_append] at hclause
  obtain ⟨i, hi, hclause | hclause⟩ := hclause
  · exact muNegOneExactlyTwo_satisfied (hsame i hi) clause hclause
  · exact muNegThreeExactlyThree_satisfied (hopp i hi) clause hclause

theorem muNegThreeZeroFiveCrossColClauses_satisfied
    {sigma : Bool} {val : DimacsValuation}
    (hsame : ∀ j, j < 8 -> MuNegOneExactlyTwoSemantics val
      (((List.range 8).filter fun i =>
        muNegOneSign sigma i == muNegOneSign sigma (8 + j)).map fun i =>
          Int.ofNat (muNegOneDVar i j)))
    (hopp : ∀ j, j < 8 -> MuNegThreeExactlyThreeSemantics val
      (((List.range 8).filter fun i =>
        !(muNegOneSign sigma i == muNegOneSign sigma (8 + j))).map fun i =>
          Int.ofNat (muNegOneDVar i j))) :
    ∀ clause ∈ muNegThreeZeroFiveCrossColClauses sigma,
      dimacsClauseSatisfied val clause := by
  intro clause hclause
  simp only [muNegThreeZeroFiveCrossColClauses, List.mem_flatMap,
    List.mem_range, List.mem_append] at hclause
  obtain ⟨j, hj, hclause | hclause⟩ := hclause
  · exact muNegOneExactlyTwo_satisfied (hsame j hj) clause hclause
  · exact muNegThreeExactlyThree_satisfied (hopp j hj) clause hclause

theorem muNegThreeZeroFiveOwnerConstraintSemantics_formulaSatisfied
    {uTri vTri sigma : Bool} {val : DimacsValuation}
    (h : MuNegThreeZeroFiveOwnerConstraintSemantics uTri vTri sigma val) :
    dimacsFormulaSatisfied val
      (muNegThreeZeroFiveOwnerDimacsClauses uTri vTri sigma) := by
  intro clause hclause
  simp only [muNegThreeZeroFiveOwnerDimacsClauses, List.mem_toArray]
    at hclause
  rcases List.mem_append.mp hclause with hclause | hclause
  · rcases List.mem_append.mp hclause with hclause | hclause
    · rcases List.mem_append.mp hclause with hclause | hclause
      · rcases List.mem_append.mp hclause with hclause | hclause
        · rcases List.mem_append.mp hclause with hrows | hcols
          · exact h.cross_rows clause hrows
          · exact h.cross_columns clause hcols
        · exact h.intertwining clause hclause
      · exact h.hit_activity clause hclause
    · exact h.service clause hclause
  · exact h.exterior_c4 clause hclause

theorem muNegThreeZeroFiveOwnerSatCnf_sat_of_constraints
    {uTri vTri sigma : Bool} {val : DimacsValuation}
    (hnz : ∀ clause ∈
      muNegThreeZeroFiveOwnerDimacsClauses uTri vTri sigma,
      DimacsClauseNonzero clause)
    (h : MuNegThreeZeroFiveOwnerConstraintSemantics uTri vTri sigma val) :
    (muNegThreeZeroFiveOwnerSatCnf uTri vTri sigma).Sat
      (satAssignmentOfDimacs val) := by
  simpa only [muNegThreeZeroFiveOwnerSatCnf] using
    satCnf_of_dimacsFormulaSatisfied hnz
      (muNegThreeZeroFiveOwnerConstraintSemantics_formulaSatisfied h)

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveOwnerConstraintSemantics_formulaSatisfied
