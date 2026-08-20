import Proofs.Erdos85MuNegFiveZeroThreeOwnerCrossBridge

/-!
# Relation-level hit, service, and C4 bridge for h503

This file transports clean owner-activity and owner-adjacency laws into the
three non-structural DIMACS families.  The first increment closes hit
activity.
-/

namespace Erdos85

open Std Sat

set_option maxHeartbeats 0

theorem muNegFiveZeroThreeHitVariable?_some_of_mem
    {e f : Nat} (hmem : (e, f) ∈ muNegFiveZeroThreeHitVariables) :
    e < 72 ∧ f < 72 ∧
      ∃ id, muNegFiveZeroThreeHitVariable? e f = some id := by
  have hbounds : e < 72 ∧ f < 72 := by
    simp only [muNegFiveZeroThreeHitVariables, List.mem_flatMap,
      List.mem_range, List.mem_map, List.mem_filter] at hmem
    obtain ⟨e', he', f', ⟨hf', hcond⟩, hp⟩ := hmem
    have heq : e' = e := congrArg Prod.fst hp
    have hfeq : f' = f := congrArg Prod.snd hp
    omega
  have hef : e < f := by
    simp only [muNegFiveZeroThreeHitVariables, List.mem_flatMap,
      List.mem_range, List.mem_map, List.mem_filter] at hmem
    obtain ⟨e', _, f', ⟨_, hcond⟩, hp⟩ := hmem
    have hef' : e' < f' := by
      simp at hcond
      exact hcond.1
    have heq : e' = e := congrArg Prod.fst hp
    have hfeq : f' = f := congrArg Prod.snd hp
    omega
  have hsome :
      (muNegFiveZeroThreeHitVariables.idxOf? (e, f)).isSome := by
    simpa using hmem
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨hbounds.1, hbounds.2, i + 65, ?_⟩
  simp [muNegFiveZeroThreeHitVariable?, hef, hi]

/-- Every encoded hit joins enabled owners, so each emitted negative-hit
activity guard is satisfied. -/
theorem muNegFiveZeroThreeHitActivityClauses_satisfied
    (active : Fin 72 → Prop) (X : Fin 72 → Fin 72 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsymm : ∀ e f, X e f → X f e)
    (hends : ∀ e f, X e f → active e ∧ active f) :
    ∀ clause ∈ muNegFiveZeroThreeHitActivityClauses,
      dimacsClauseSatisfied
        (muNegFiveZeroThreeOwnerValOfRelations active X) clause := by
  intro clause hclause
  simp only [muNegFiveZeroThreeHitActivityClauses, List.mem_flatMap]
    at hclause
  obtain ⟨p, hp, hclause⟩ := hclause
  rcases p with ⟨e, f⟩
  obtain ⟨he, hf, hitId, hhit⟩ :=
    muNegFiveZeroThreeHitVariable?_some_of_mem hp
  let ef : Fin 72 := ⟨e, he⟩
  let ff : Fin 72 := ⟨f, hf⟩
  have hhitFin : muNegFiveZeroThreeHitVariable? ef ff = some hitId := by
    simpa [ef, ff] using hhit
  simp only [hhit, Option.getD_some] at hclause
  have hsatisfy (q : Fin 72) (activeId : Nat)
      (hactiveVar : muNegFiveZeroThreeActiveVariable? q = some activeId)
      (hendpoint : ∀ hX : X ef ff, active q) :
      dimacsClauseSatisfied
        (muNegFiveZeroThreeOwnerValOfRelations active X)
        [-Int.ofNat hitId, Int.ofNat activeId] := by
    by_cases hval :
        muNegFiveZeroThreeOwnerValOfRelations active X hitId = true
    · have hX := muNegFiveZeroThreeOwnerRelation_of_val_true active X hsymm
          hhitFin hval
      refine ⟨Int.ofNat activeId, by simp, ?_⟩
      have haval := muNegFiveZeroThreeOwnerVal_active_true_of active X
        hactiveVar (hendpoint hX)
      simp [dimacsLitValue,
        (muNegFiveZeroThreeActiveVariable?_bounds hactiveVar).1, haval]
    · refine ⟨-Int.ofNat hitId, by simp, ?_⟩
      have hfalse :
          muNegFiveZeroThreeOwnerValOfRelations active X hitId = false :=
        Bool.eq_false_of_not_eq_true hval
      simp [dimacsLitValue, hfalse]
  generalize hea : muNegFiveZeroThreeActiveVariable? e = oe at hclause
  generalize hfa : muNegFiveZeroThreeActiveVariable? f = of_ at hclause
  cases oe with
  | none =>
      cases of_ with
      | none => simp at hclause
      | some b =>
          simp at hclause
          subst clause
          exact hsatisfy ff b (by simpa [ff] using hfa)
            (fun hX => (hends ef ff hX).2)
  | some a =>
      cases of_ with
      | none =>
          simp at hclause
          subst clause
          exact hsatisfy ef a (by simpa [ef] using hea)
            (fun hX => (hends ef ff hX).1)
      | some b =>
          simp at hclause
          rcases hclause with rfl | rfl
          · exact hsatisfy ef a (by simpa [ef] using hea)
              (fun hX => (hends ef ff hX).1)
          · exact hsatisfy ff b (by simpa [ff] using hfa)
              (fun hX => (hends ef ff hX).2)

end Erdos85

#print axioms Erdos85.muNegFiveZeroThreeHitActivityClauses_satisfied
