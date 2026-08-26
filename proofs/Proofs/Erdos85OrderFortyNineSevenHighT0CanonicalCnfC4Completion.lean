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

theorem sevenHighT0CanonicalNatPairs_mem
    {xs : List Nat} {pair : Nat × Nat}
    (hpair : pair ∈ sevenHighT0CanonicalNatPairs xs) :
    pair.1 ∈ xs ∧ pair.2 ∈ xs ∧ pair.1 < pair.2 := by
  unfold sevenHighT0CanonicalNatPairs at hpair
  obtain ⟨left, hleft, hpair⟩ := List.mem_flatMap.mp hpair
  obtain ⟨right, hright, rfl⟩ := List.mem_map.mp hpair
  simp only [List.mem_filter] at hright
  exact ⟨hleft, hright.1, of_decide_eq_true hright.2⟩

theorem sevenHighT0CanonicalC4Step_satisfied_nat
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H)
    (val : DimacsValuation)
    (hagree : ∀ id, id ≤ 861 → val id = sevenHighT0CanonicalEdgeVal H id)
    (endpoints witnesses : Nat × Nat)
    (he0 : endpoints.1 < 49) (he1 : endpoints.2 < 49)
    (hw0 : witnesses.1 < 49) (hw1 : witnesses.2 < 49)
    (hendpoints : endpoints.1 ≠ endpoints.2)
    (hwitnesses : witnesses.1 ≠ witnesses.2)
    (st : SevenHighT0CanonicalCnfState)
    (hsat : dimacsFormulaSatisfied val st.clauses) :
    dimacsFormulaSatisfied val
      (sevenHighT0CanonicalC4Step endpoints witnesses st).clauses := by
  exact sevenHighT0CanonicalC4Step_satisfied H semantics val hagree
    (⟨⟨endpoints.1, he0⟩, ⟨endpoints.2, he1⟩⟩)
    (⟨⟨witnesses.1, hw0⟩, ⟨witnesses.2, hw1⟩⟩)
    (fun h => hendpoints (congrArg Fin.val h))
    (fun h => hwitnesses (congrArg Fin.val h)) st hsat

theorem sevenHighT0CanonicalC4WitnessFold_satisfied
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H)
    (val : DimacsValuation)
    (hagree : ∀ id, id ≤ 861 → val id = sevenHighT0CanonicalEdgeVal H id)
    (endpoints : Nat × Nat)
    (he0 : endpoints.1 < 49) (he1 : endpoints.2 < 49)
    (hendpoints : endpoints.1 ≠ endpoints.2)
    (witnessPairs : List (Nat × Nat))
    (hwitnesses : ∀ pair ∈ witnessPairs,
      pair.1 < 49 ∧ pair.2 < 49 ∧ pair.1 ≠ pair.2)
    (st : SevenHighT0CanonicalCnfState)
    (hsat : dimacsFormulaSatisfied val st.clauses) :
    dimacsFormulaSatisfied val
      (witnessPairs.foldl
        (fun st witnesses => sevenHighT0CanonicalC4Step endpoints witnesses st)
        st).clauses := by
  induction witnessPairs generalizing st with
  | nil => exact hsat
  | cons witnesses rest ih =>
      simp only [List.foldl_cons]
      have hw := hwitnesses witnesses (by simp)
      apply ih
      · intro pair hpair
        exact hwitnesses pair (List.mem_cons_of_mem _ hpair)
      · exact sevenHighT0CanonicalC4Step_satisfied_nat H semantics val hagree
          endpoints witnesses he0 he1 hw.1 hw.2.1 hendpoints hw.2.2 st hsat

theorem sevenHighT0CanonicalC4EndpointStep_satisfied
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H)
    (val : DimacsValuation)
    (hagree : ∀ id, id ≤ 861 → val id = sevenHighT0CanonicalEdgeVal H id)
    (endpoints : Nat × Nat)
    (hendpointMem : endpoints ∈
      sevenHighT0CanonicalNatPairs sevenHighT0CanonicalVertices)
    (st : SevenHighT0CanonicalCnfState)
    (hsat : dimacsFormulaSatisfied val st.clauses) :
    dimacsFormulaSatisfied val
      (sevenHighT0CanonicalC4EndpointStep endpoints st).clauses := by
  have he := sevenHighT0CanonicalNatPairs_mem hendpointMem
  have he0 : endpoints.1 < 49 := by
    simpa [sevenHighT0CanonicalVertices] using he.1
  have he1 : endpoints.2 < 49 := by
    simpa [sevenHighT0CanonicalVertices] using he.2.1
  let candidates := sevenHighT0CanonicalVertices.filter fun vertex =>
    vertex ≠ endpoints.1 && vertex ≠ endpoints.2
  apply sevenHighT0CanonicalC4WitnessFold_satisfied H semantics val hagree
    endpoints he0 he1 (by omega) (sevenHighT0CanonicalNatPairs candidates)
  · intro pair hpair
    have hw := sevenHighT0CanonicalNatPairs_mem hpair
    have hw0mem : pair.1 ∈ sevenHighT0CanonicalVertices :=
      (List.mem_filter.mp hw.1).1
    have hw1mem : pair.2 ∈ sevenHighT0CanonicalVertices :=
      (List.mem_filter.mp hw.2.1).1
    exact ⟨by simpa [sevenHighT0CanonicalVertices] using hw0mem,
      by simpa [sevenHighT0CanonicalVertices] using hw1mem, by omega⟩
  · exact hsat

theorem sevenHighT0CanonicalC4EndpointFold_satisfied
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H)
    (val : DimacsValuation)
    (hagree : ∀ id, id ≤ 861 → val id = sevenHighT0CanonicalEdgeVal H id)
    (endpointPairs : List (Nat × Nat))
    (hendpoints : ∀ pair ∈ endpointPairs,
      pair ∈ sevenHighT0CanonicalNatPairs sevenHighT0CanonicalVertices)
    (st : SevenHighT0CanonicalCnfState)
    (hsat : dimacsFormulaSatisfied val st.clauses) :
    dimacsFormulaSatisfied val
      (endpointPairs.foldl
        (fun st endpoints => sevenHighT0CanonicalC4EndpointStep endpoints st)
        st).clauses := by
  induction endpointPairs generalizing st with
  | nil => exact hsat
  | cons endpoints rest ih =>
      simp only [List.foldl_cons]
      apply ih
      · intro pair hpair
        exact hendpoints pair (List.mem_cons_of_mem _ hpair)
      · exact sevenHighT0CanonicalC4EndpointStep_satisfied H semantics val hagree
          endpoints (hendpoints endpoints (by simp)) st hsat

theorem sevenHighT0CanonicalFinalState_satisfied
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H) :
    dimacsFormulaSatisfied (sevenHighT0CanonicalDegreeStateVal H).2
      sevenHighT0CanonicalFinalState.clauses := by
  let degreeSound := sevenHighT0CanonicalDegreeStateVal_semanticSound H semantics
  rw [sevenHighT0CanonicalFinalState]
  rw [← sevenHighT0CanonicalDegreeStateVal_state H]
  apply sevenHighT0CanonicalC4EndpointFold_satisfied H semantics
    (sevenHighT0CanonicalDegreeStateVal H).2 degreeSound.edge_agree
  · intro pair hpair
    exact hpair
  · exact degreeSound.satisfied

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalEdgeStatus_variable_le
#print axioms Erdos85.sevenHighT0CanonicalC4Step_satisfied
#print axioms Erdos85.sevenHighT0CanonicalFinalState_satisfied
