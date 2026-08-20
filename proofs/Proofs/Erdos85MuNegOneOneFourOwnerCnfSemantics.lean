import Proofs.Erdos85MuNegOneOneFourOwnerCertificateTFTFS0
import Proofs.Erdos85MuNegOneOneFourOwnerCertificateTFTFS1
import Proofs.Erdos85MuNegOneOneFourOwnerCertificateTFtriS0
import Proofs.Erdos85MuNegOneOneFourOwnerCertificateTFtriS1
import Proofs.Erdos85MuNegOneOneFourOwnerCertificatetritriS0
import Proofs.Erdos85MuNegOneOneFourOwnerCertificatetritriS1
import Proofs.Erdos85EightEightLowOwnerCnfSemantics

/-!
# Semantic socket for the μ=-1 `(1,4)` owner-grid CNFs

The six fields mirror the six clause families of the checked generator
(cross rows, cross columns, intertwining, hit activity, guarded
service, exterior C4).  Graph-to-CNF embeddings establish the families
independently and use the single contradiction theorem below, which
covers the three canonical shore-mode pairs (TF/TF, TF/tri, tri/tri)
and both sign phases — the reverse mixed orientation is normalized by
the banked swap adapter before reaching this socket.
-/

namespace Erdos85

open Std Sat Std.Tactic.BVDecide

structure MuNegOneOneFourOwnerConstraintSemantics
    (uTri vTri σ : Bool) (val : DimacsValuation) : Prop where
  cross_rows : ∀ clause ∈ muNegOneCrossRowClauses σ,
    dimacsClauseSatisfied val clause
  cross_columns : ∀ clause ∈ muNegOneCrossColClauses σ,
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

/-- Semantic content of an exactly-two block: every drop-one subclause
holds and no three literals are simultaneously true. -/
structure MuNegOneExactlyTwoSemantics
    (val : DimacsValuation) (lits : List Int) : Prop where
  drop_one : ∀ x ∈ lits,
    dimacsClauseSatisfied val (lits.filter fun l => l != x)
  no_three : ∀ i j k, i < lits.length → j < lits.length →
    k < lits.length → i < j → j < k →
    dimacsClauseSatisfied val [-lits[i]!, -lits[j]!, -lits[k]!]

theorem muNegOneExactlyTwo_satisfied
    {val : DimacsValuation} {lits : List Int}
    (h : MuNegOneExactlyTwoSemantics val lits) :
    ∀ clause ∈ muNegOneExactlyTwo lits,
      dimacsClauseSatisfied val clause := by
  intro clause hclause
  simp only [muNegOneExactlyTwo, List.mem_append, List.mem_map,
    List.mem_flatMap, List.mem_range, List.mem_filter] at hclause
  rcases hclause with ⟨x, hx, rfl⟩ | ⟨i, hi, j, ⟨hj, hij⟩, k, ⟨hk, hjk⟩, rfl⟩
  · exact h.drop_one x hx
  · exact h.no_three i j k hi hj hk
      (of_decide_eq_true hij) (of_decide_eq_true hjk)

theorem muNegOneCrossRowClauses_satisfied
    {σ : Bool} {val : DimacsValuation}
    (hsame : ∀ i, i < 8 → MuNegOneExactlyTwoSemantics val
      (((List.range 8).filter fun j =>
        muNegOneSign σ i == muNegOneSign σ (8 + j)).map fun j =>
          Int.ofNat (muNegOneDVar i j)))
    (hopp : ∀ i, i < 8 → MuNegOneExactlyTwoSemantics val
      (((List.range 8).filter fun j =>
        !(muNegOneSign σ i == muNegOneSign σ (8 + j))).map fun j =>
          Int.ofNat (muNegOneDVar i j))) :
    ∀ clause ∈ muNegOneCrossRowClauses σ,
      dimacsClauseSatisfied val clause := by
  intro clause hclause
  simp only [muNegOneCrossRowClauses, List.mem_flatMap,
    List.mem_range, List.mem_append] at hclause
  obtain ⟨i, hi, hclause | hclause⟩ := hclause
  · exact muNegOneExactlyTwo_satisfied (hsame i hi) clause hclause
  · exact muNegOneExactlyTwo_satisfied (hopp i hi) clause hclause

theorem muNegOneCrossColClauses_satisfied
    {σ : Bool} {val : DimacsValuation}
    (hsame : ∀ j, j < 8 → MuNegOneExactlyTwoSemantics val
      (((List.range 8).filter fun i =>
        muNegOneSign σ i == muNegOneSign σ (8 + j)).map fun i =>
          Int.ofNat (muNegOneDVar i j)))
    (hopp : ∀ j, j < 8 → MuNegOneExactlyTwoSemantics val
      (((List.range 8).filter fun i =>
        !(muNegOneSign σ i == muNegOneSign σ (8 + j))).map fun i =>
          Int.ofNat (muNegOneDVar i j))) :
    ∀ clause ∈ muNegOneCrossColClauses σ,
      dimacsClauseSatisfied val clause := by
  intro clause hclause
  simp only [muNegOneCrossColClauses, List.mem_flatMap,
    List.mem_range, List.mem_append] at hclause
  obtain ⟨j, hj, hclause | hclause⟩ := hclause
  · exact muNegOneExactlyTwo_satisfied (hsame j hj) clause hclause
  · exact muNegOneExactlyTwo_satisfied (hopp j hj) clause hclause

/-- Entrywise satisfaction of the four-neighbor sum encoding lifts to the
complete `8 × 8` intertwining family. -/
theorem muNegOneIntertwineClauses_satisfied
    {val : DimacsValuation}
    (hcell : ∀ i j, i < 8 → j < 8 →
      ∀ clause ∈ muNegOneSumEq
        (Int.ofNat (muNegOneDVar ((i + 7) % 8) j))
        (Int.ofNat (muNegOneDVar ((i + 1) % 8) j))
        (Int.ofNat (muNegOneDVar i ((j + 1) % 8)))
        (Int.ofNat (muNegOneDVar i ((j + 7) % 8))),
        dimacsClauseSatisfied val clause) :
    ∀ clause ∈ muNegOneIntertwineClauses,
      dimacsClauseSatisfied val clause := by
  intro clause hclause
  simp only [muNegOneIntertwineClauses, List.mem_flatMap,
    List.mem_range] at hclause
  obtain ⟨i, hi, j, hj, hclause⟩ := hclause
  exact hcell i j hi hj clause hclause

theorem muNegOneOneFourOwnerConstraintSemantics_formulaSatisfied
    {uTri vTri σ : Bool} {val : DimacsValuation}
    (h : MuNegOneOneFourOwnerConstraintSemantics uTri vTri σ val) :
    dimacsFormulaSatisfied val
      (muNegOneOneFourOwnerDimacsClauses uTri vTri σ) := by
  intro clause hclause
  simp only [muNegOneOneFourOwnerDimacsClauses, List.mem_toArray]
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

theorem muNegOneOneFourOwnerSatCnf_sat_of_constraints
    {uTri vTri σ : Bool} {val : DimacsValuation}
    (hnz : ∀ clause ∈ muNegOneOneFourOwnerDimacsClauses uTri vTri σ,
      DimacsClauseNonzero clause)
    (h : MuNegOneOneFourOwnerConstraintSemantics uTri vTri σ val) :
    (muNegOneOneFourOwnerSatCnf uTri vTri σ).Sat
      (satAssignmentOfDimacs val) := by
  simpa only [muNegOneOneFourOwnerSatCnf] using
    satCnf_of_dimacsFormulaSatisfied hnz
      (muNegOneOneFourOwnerConstraintSemantics_formulaSatisfied h)

theorem muNegOneOneFourOwnerConstraintSemantics_false
    {uTri vTri σ : Bool} {val : DimacsValuation}
    (hcanon : (uTri = false ∧ vTri = false) ∨
      (uTri = false ∧ vTri = true) ∨ (uTri = true ∧ vTri = true))
    (hnz : ∀ clause ∈ muNegOneOneFourOwnerDimacsClauses uTri vTri σ,
      DimacsClauseNonzero clause)
    (h : MuNegOneOneFourOwnerConstraintSemantics uTri vTri σ val) :
    False := by
  have hsat := muNegOneOneFourOwnerSatCnf_sat_of_constraints hnz h
  rw [CNF.sat_def] at hsat
  rcases hcanon with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases σ
  · have hu := LRAT.check_sound _ _ muNegOneOneFourOwner_check_TFTF_s0
      (satAssignmentOfDimacs val)
    rw [hsat] at hu
    contradiction
  · have hu := LRAT.check_sound _ _ muNegOneOneFourOwner_check_TFTF_s1
      (satAssignmentOfDimacs val)
    rw [hsat] at hu
    contradiction
  · have hu := LRAT.check_sound _ _ muNegOneOneFourOwner_check_TFtri_s0
      (satAssignmentOfDimacs val)
    rw [hsat] at hu
    contradiction
  · have hu := LRAT.check_sound _ _ muNegOneOneFourOwner_check_TFtri_s1
      (satAssignmentOfDimacs val)
    rw [hsat] at hu
    contradiction
  · have hu := LRAT.check_sound _ _ muNegOneOneFourOwner_check_tritri_s0
      (satAssignmentOfDimacs val)
    rw [hsat] at hu
    contradiction
  · have hu := LRAT.check_sound _ _ muNegOneOneFourOwner_check_tritri_s1
      (satAssignmentOfDimacs val)
    rw [hsat] at hu
    contradiction

end Erdos85

#print axioms Erdos85.muNegOneOneFourOwnerConstraintSemantics_false
