import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalCnfDegreeWitness
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalCnfC4Fold

/-!
# Completing the canonical H7/T0 C4-clause valuation

The degree-counter valuation already agrees with graph adjacency on IDs
`1..861`.  This module uses that invariant and semantic C4-freeness to satisfy
the generator's remaining negative four-cross-edge clauses.
-/

namespace Erdos85

set_option maxRecDepth 100000 in
theorem sevenHighT0CanonicalEdgeStatus_variable_le
    (a b : Fin 49) (id : Nat)
    (hstatus : sevenHighT0CanonicalEdgeStatus a.1 b.1 = .variable id) :
    id ≤ 861 := by
  have hab : a ≠ b := by
    intro h
    subst b
    simp [sevenHighT0CanonicalEdgeStatus] at hstatus
  have ha : 7 ≤ a.1 := by
    by_contra h
    have hahigh : a.1 < 7 := by omega
    unfold sevenHighT0CanonicalEdgeStatus at hstatus
    rw [if_neg (fun hv => hab (Fin.ext hv)), if_neg (by omega),
      if_pos hahigh] at hstatus
    split at hstatus <;> contradiction
  have hb : 7 ≤ b.1 := by
    by_contra h
    have hbhigh : b.1 < 7 := by omega
    unfold sevenHighT0CanonicalEdgeStatus at hstatus
    rw [if_neg (fun hv => hab (Fin.ext hv)), if_neg (by omega)] at hstatus
    by_cases hahigh : a.1 < 7
    · rw [if_pos hahigh] at hstatus
      split at hstatus <;> contradiction
    · rw [if_neg hahigh, if_pos hbhigh] at hstatus
      split at hstatus <;> contradiction
  have hid : id = sevenHighT0CanonicalLowEdgeId a.1 b.1 := by
    unfold sevenHighT0CanonicalEdgeStatus at hstatus
    rw [if_neg (fun h => hab (Fin.ext h)), if_pos ⟨ha, hb⟩] at hstatus
    simpa using congrArg (fun status => match status with
      | .variable value => value
      | _ => 0) hstatus.symm
  have hlookup := sevenHighT0CanonicalLowEdge_lookup a b ha hb hab
  rw [← hid] at hlookup
  obtain ⟨hindex, _⟩ := List.getElem?_eq_some_iff.mp hlookup
  have hlength : sevenHighT0CanonicalLowEdgePairs.length = 861 := by
    decide
  rw [hlength] at hindex
  have hpos := sevenHighT0CanonicalEdgeStatus_variable_pos a.1 b.1 id hstatus
  omega

theorem sevenHighT0CanonicalEdgeStatusValue_of_edge_agree
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (val : DimacsValuation)
    (hagree : ∀ id, id ≤ 861 → val id = sevenHighT0CanonicalEdgeVal H id)
    (a b : Fin 49) :
    sevenHighT0CanonicalEdgeStatusValue val
        (sevenHighT0CanonicalEdgeStatus a.1 b.1) =
      sevenHighT0CanonicalEdgeStatusValue (sevenHighT0CanonicalEdgeVal H)
        (sevenHighT0CanonicalEdgeStatus a.1 b.1) := by
  generalize hstatus : sevenHighT0CanonicalEdgeStatus a.1 b.1 = status
  cases status with
  | fixedFalse => rfl
  | fixedTrue => rfl
  | «variable» id =>
      simp only [sevenHighT0CanonicalEdgeStatusValue]
      exact hagree id (sevenHighT0CanonicalEdgeStatus_variable_le a b id hstatus)

theorem dimacsFormulaSatisfied_push
    {val : DimacsValuation} {clauses : Array DimacsClause}
    {clause : DimacsClause}
    (hprevious : dimacsFormulaSatisfied val clauses)
    (hclause : dimacsClauseSatisfied val clause) :
    dimacsFormulaSatisfied val (clauses.push clause) := by
  intro candidate hcandidate
  simp only [Array.mem_push] at hcandidate
  rcases hcandidate with hcandidate | rfl
  · exact hprevious candidate hcandidate
  · exact hclause

theorem sevenHighT0CanonicalC4Step_satisfied
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H)
    (val : DimacsValuation)
    (hagree : ∀ id, id ≤ 861 → val id = sevenHighT0CanonicalEdgeVal H id)
    (endpoints witnesses : Fin 49 × Fin 49)
    (hendpoints : endpoints.1 ≠ endpoints.2)
    (hwitnesses : witnesses.1 ≠ witnesses.2)
    (st : SevenHighT0CanonicalCnfState)
    (hsat : dimacsFormulaSatisfied val st.clauses) :
    dimacsFormulaSatisfied val
      (sevenHighT0CanonicalC4Step
        (endpoints.1.1, endpoints.2.1)
        (witnesses.1.1, witnesses.2.1) st).clauses := by
  let s0 := sevenHighT0CanonicalEdgeStatus endpoints.1.1 witnesses.1.1
  let s1 := sevenHighT0CanonicalEdgeStatus endpoints.2.1 witnesses.1.1
  let s2 := sevenHighT0CanonicalEdgeStatus endpoints.1.1 witnesses.2.1
  let s3 := sevenHighT0CanonicalEdgeStatus endpoints.2.1 witnesses.2.1
  let statuses : List SevenHighT0CanonicalEdgeStatus :=
    [s0, s1, s2, s3]
  by_cases hfalse : statuses.contains .fixedFalse
  · simpa only [sevenHighT0CanonicalC4Step, s0, s1, s2, s3,
      statuses, hfalse, ↓reduceIte] using hsat
  · have hmissing := semantics.exists_missing_cross_edge
        (fun h => hendpoints (sevenHighT0CanonicalIndexOfFin_injective h))
        (fun h => hwitnesses (sevenHighT0CanonicalIndexOfFin_injective h))
    have missingValue (a b : Fin 49) (hnot :
        ¬ H.Adj (sevenHighT0CanonicalIndexOfFin a)
          (sevenHighT0CanonicalIndexOfFin b)) :
        sevenHighT0CanonicalEdgeStatusValue val
          (sevenHighT0CanonicalEdgeStatus a.1 b.1) = false := by
      rw [sevenHighT0CanonicalEdgeStatusValue_of_edge_agree H val hagree,
        sevenHighT0CanonicalEdgeStatusValue_eq_adj H semantics]
      simp [sevenHighT0CanonicalAdjBool, hnot]
    have hvalues :
        sevenHighT0CanonicalEdgeStatusValue val s0 = false ∨
        sevenHighT0CanonicalEdgeStatusValue val s1 = false ∨
        sevenHighT0CanonicalEdgeStatusValue val s2 = false ∨
        sevenHighT0CanonicalEdgeStatusValue val s3 = false := by
      rcases hmissing with h | h | h | h
      · exact Or.inl (missingValue _ _ h)
      · exact Or.inr (Or.inl (missingValue _ _ h))
      · exact Or.inr (Or.inr (Or.inl (missingValue _ _ h)))
      · exact Or.inr (Or.inr (Or.inr (missingValue _ _ h)))
    have hclause : dimacsClauseSatisfied val
        (statuses.filterMap sevenHighT0CanonicalC4Literal) := by
      rcases hvalues with hvalue | hvalue | hvalue | hvalue
      · apply sevenHighT0CanonicalC4Clause_satisfied_of_false_status
          val statuses s0 (by simp [statuses])
        · intro hs
          apply hfalse
          simp [statuses, hs]
        · exact hvalue
        · intro id hstatus
          exact sevenHighT0CanonicalEdgeStatus_variable_pos _ _ id (by
            simpa [s0] using hstatus)
      · apply sevenHighT0CanonicalC4Clause_satisfied_of_false_status
          val statuses s1 (by simp [statuses])
        · intro hs
          apply hfalse
          simp [statuses, hs]
        · exact hvalue
        · intro id hstatus
          exact sevenHighT0CanonicalEdgeStatus_variable_pos _ _ id (by
            simpa [s1] using hstatus)
      · apply sevenHighT0CanonicalC4Clause_satisfied_of_false_status
          val statuses s2 (by simp [statuses])
        · intro hs
          apply hfalse
          simp [statuses, hs]
        · exact hvalue
        · intro id hstatus
          exact sevenHighT0CanonicalEdgeStatus_variable_pos _ _ id (by
            simpa [s2] using hstatus)
      · apply sevenHighT0CanonicalC4Clause_satisfied_of_false_status
          val statuses s3 (by simp [statuses])
        · intro hs
          apply hfalse
          simp [statuses, hs]
        · exact hvalue
        · intro id hstatus
          exact sevenHighT0CanonicalEdgeStatus_variable_pos _ _ id (by
            simpa [s3] using hstatus)
    simp only [sevenHighT0CanonicalC4Step, s0, s1, s2, s3,
      statuses, hfalse, Bool.false_eq_true, ↓reduceIte]
    exact dimacsFormulaSatisfied_push hsat hclause

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalEdgeStatus_variable_le
#print axioms Erdos85.sevenHighT0CanonicalC4Step_satisfied
