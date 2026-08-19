import Proofs.Erdos85MuNegThreeOneTwoOwnerCertificates

/-!
# Semantic socket for the μ=-3 `(1,2)` owner-grid CNFs

The seven fields mirror the seven clause families in the checked generator.
Graph-to-CNF embeddings can establish the families independently and use the
single contradiction theorem below.
-/

namespace Erdos85

open Std Sat

structure MuNegThreeOneTwoOwnerConstraintSemantics
    (fwd : Bool) (c : Nat) (val : DimacsValuation) : Prop where
  fixed : ∀ clause ∈ muNegThreeFixClauses fwd c,
    dimacsClauseSatisfied val clause
  opposite_rows : ∀ clause ∈ muNegThreeOppRowClauses,
    dimacsClauseSatisfied val clause
  opposite_columns : ∀ clause ∈ muNegThreeOppColClauses,
    dimacsClauseSatisfied val clause
  intertwining : ∀ clause ∈ muNegThreeIntertwineClauses,
    dimacsClauseSatisfied val clause
  hit_activity : ∀ clause ∈ muNegThreeHitActivityClauses,
    dimacsClauseSatisfied val clause
  service : ∀ clause ∈ muNegThreeServiceClauses,
    dimacsClauseSatisfied val clause
  exterior_c4 : ∀ clause ∈ muNegThreeC4Clauses,
    dimacsClauseSatisfied val clause

/-- The unit-clause family is satisfied exactly by a valuation whose cross
cell variables realize the selected orientation and phase. -/
theorem muNegThreeFixClauses_satisfied
    {fwd : Bool} {c : Nat} {val : DimacsValuation}
    (hval : ∀ i j, i < 8 → j < 8 → i % 2 == j % 2 →
      val (muNegThreeDVar (i * 8 + j)) =
        (j == muNegThreePhi fwd c i)) :
    ∀ clause ∈ muNegThreeFixClauses fwd c,
      dimacsClauseSatisfied val clause := by
  intro clause hclause
  simp only [muNegThreeFixClauses, List.mem_flatMap, List.mem_range,
    List.mem_map, List.mem_filter] at hclause
  obtain ⟨i, hi, j, ⟨hj, hparity⟩, rfl⟩ := hclause
  split
  · next hphase =>
    let d := muNegThreeDVar (i * 8 + j)
    have hd : 0 < d := by simp [d, muNegThreeDVar]
    have hv := hval i j hi hj hparity
    simp [hphase] at hv
    change val d = true at hv
    refine ⟨Int.ofNat d, by simp [d], ?_⟩
    simp [dimacsLitValue, hd, hv]
  · next hphase =>
    let d := muNegThreeDVar (i * 8 + j)
    have hv := hval i j hi hj hparity
    simp [hphase] at hv
    change val d = false at hv
    refine ⟨-Int.ofNat d, by simp [d], ?_⟩
    simp [dimacsLitValue, hv]

/-- Semantic content of an exactly-one block, separated from its quadratic
DIMACS expansion. -/
structure MuNegThreeExactlyOneSemantics
    (val : DimacsValuation) (lits : List Int) : Prop where
  exists_true : dimacsClauseSatisfied val lits
  pairwise : ∀ x ∈ lits, ∀ y ∈ lits, x < y →
    dimacsClauseSatisfied val [-x, -y]

theorem muNegThreeExactlyOne_satisfied
    {val : DimacsValuation} {lits : List Int}
    (h : MuNegThreeExactlyOneSemantics val lits) :
    ∀ clause ∈ muNegThreeExactlyOne lits,
      dimacsClauseSatisfied val clause := by
  intro clause hclause
  simp only [muNegThreeExactlyOne, List.mem_append, List.mem_singleton,
    List.mem_flatMap, List.mem_map, List.mem_filter] at hclause
  rcases hclause with rfl | ⟨x, hx, y, ⟨hy, hxy⟩, rfl⟩
  · exact h.exists_true
  · exact h.pairwise x hx y hy (of_decide_eq_true hxy)

theorem muNegThreeOppRowClauses_satisfied
    {val : DimacsValuation}
    (hrow : ∀ i, i < 8 → MuNegThreeExactlyOneSemantics val
      (((List.range 8).filter fun j => !(i % 2 == j % 2)).map
        fun j => Int.ofNat (muNegThreeDVar (i * 8 + j)))) :
    ∀ clause ∈ muNegThreeOppRowClauses,
      dimacsClauseSatisfied val clause := by
  intro clause hclause
  simp only [muNegThreeOppRowClauses, List.mem_flatMap,
    List.mem_range] at hclause
  obtain ⟨i, hi, hclause⟩ := hclause
  exact muNegThreeExactlyOne_satisfied (hrow i hi) clause hclause

theorem muNegThreeOppColClauses_satisfied
    {val : DimacsValuation}
    (hcol : ∀ j, j < 8 → MuNegThreeExactlyOneSemantics val
      (((List.range 8).filter fun i => !(i % 2 == j % 2)).map
        fun i => Int.ofNat (muNegThreeDVar (i * 8 + j)))) :
    ∀ clause ∈ muNegThreeOppColClauses,
      dimacsClauseSatisfied val clause := by
  intro clause hclause
  simp only [muNegThreeOppColClauses, List.mem_flatMap,
    List.mem_range] at hclause
  obtain ⟨j, hj, hclause⟩ := hclause
  exact muNegThreeExactlyOne_satisfied (hcol j hj) clause hclause

/-- Entrywise satisfaction of the four-neighbor sum encoding lifts to the
complete `8 × 8` intertwining family. -/
theorem muNegThreeIntertwineClauses_satisfied
    {val : DimacsValuation}
    (hcell : ∀ i j, i < 8 → j < 8 →
      ∀ clause ∈ muNegThreeSumEq
        (Int.ofNat (muNegThreeDVar (((i + 7) % 8) * 8 + j)))
        (Int.ofNat (muNegThreeDVar (((i + 1) % 8) * 8 + j)))
        (Int.ofNat (muNegThreeDVar (i * 8 + (j + 1) % 8)))
        (Int.ofNat (muNegThreeDVar (i * 8 + (j + 7) % 8))),
        dimacsClauseSatisfied val clause) :
    ∀ clause ∈ muNegThreeIntertwineClauses,
      dimacsClauseSatisfied val clause := by
  intro clause hclause
  simp only [muNegThreeIntertwineClauses, List.mem_flatMap,
    List.mem_range] at hclause
  obtain ⟨i, hi, j, hj, hclause⟩ := hclause
  exact hcell i j hi hj clause hclause

theorem muNegThreeOneTwoOwnerConstraintSemantics_formulaSatisfied
    {fwd : Bool} {c : Nat} {val : DimacsValuation}
    (h : MuNegThreeOneTwoOwnerConstraintSemantics fwd c val) :
    dimacsFormulaSatisfied val
      (muNegThreeOneTwoOwnerDimacsClauses fwd c) := by
  intro clause hclause
  simp only [muNegThreeOneTwoOwnerDimacsClauses, List.mem_toArray] at hclause
  rcases List.mem_append.mp hclause with hclause | hclause
  · rcases List.mem_append.mp hclause with hclause | hclause
    · rcases List.mem_append.mp hclause with hclause | hclause
      · rcases List.mem_append.mp hclause with hclause | hclause
        · rcases List.mem_append.mp hclause with hclause | hclause
          · rcases List.mem_append.mp hclause with hfixed | hrows
            · exact h.fixed clause hfixed
            · exact h.opposite_rows clause hrows
          · exact h.opposite_columns clause hclause
        · exact h.intertwining clause hclause
      · exact h.hit_activity clause hclause
    · exact h.service clause hclause
  · exact h.exterior_c4 clause hclause

theorem muNegThreeOneTwoOwnerSatCnf_sat_of_constraints
    {fwd : Bool} {c : Nat} {val : DimacsValuation}
    (hnz : ∀ clause ∈ muNegThreeOneTwoOwnerDimacsClauses fwd c,
      DimacsClauseNonzero clause)
    (h : MuNegThreeOneTwoOwnerConstraintSemantics fwd c val) :
    (muNegThreeOneTwoOwnerSatCnf fwd c).Sat (satAssignmentOfDimacs val) := by
  simpa only [muNegThreeOneTwoOwnerSatCnf] using
    satCnf_of_dimacsFormulaSatisfied hnz
      (muNegThreeOneTwoOwnerConstraintSemantics_formulaSatisfied h)

theorem muNegThreeOneTwoOwnerConstraintSemantics_false
    {fwd : Bool} {c : Nat} {val : DimacsValuation}
    (hc : c = 0 ∨ c = 2 ∨ c = 4 ∨ c = 6)
    (hnz : ∀ clause ∈ muNegThreeOneTwoOwnerDimacsClauses fwd c,
      DimacsClauseNonzero clause)
    (h : MuNegThreeOneTwoOwnerConstraintSemantics fwd c val) : False := by
  have hsat := muNegThreeOneTwoOwnerSatCnf_sat_of_constraints hnz h
  rw [CNF.sat_def] at hsat
  have hfalse := muNegThreeOneTwoOwnerSatCnf_unsat fwd c hc
    (satAssignmentOfDimacs val)
  rw [hsat] at hfalse
  contradiction

end Erdos85

#print axioms Erdos85.muNegThreeOneTwoOwnerConstraintSemantics_false
