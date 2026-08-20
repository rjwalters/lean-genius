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

def muNegFiveZeroThreeOwnerEnabled
    (active : Fin 72 → Prop) (e : Fin 72) : Prop :=
  match muNegFiveZeroThreeActiveVariable? e with
  | some _ => active e
  | none => True

structure MuNegFiveZeroThreeOwnerServiceSemantics
    (active : Fin 72 → Prop) (X : Fin 72 → Fin 72 → Prop) : Prop where
  service_exists : ∀ (e : Fin 72) (v : Fin 16),
    muNegFiveZeroThreeOwnerEnabled active e →
    muNegFiveZeroThreeOwnerTargetContains e v = true →
      ∃ f, X e f ∧ muNegFiveZeroThreeOwnerContains f v = true
  service_unique : ∀ (e : Fin 72) (v : Fin 16) (f g : Fin 72),
    X e f → muNegFiveZeroThreeOwnerContains f v = true →
    X e g → muNegFiveZeroThreeOwnerContains g v = true → f = g
  internal_zero : ∀ (e : Fin 72) (v : Fin 16) (f : Fin 72),
    muNegFiveZeroThreeOwnerTargetContains e v = false →
    muNegFiveZeroThreeOwnerContains f v = true → ¬ X e f
  intersecting_no_common : ∀ (e f : Fin 72),
    e ≠ f → muNegFiveZeroThreeOwnersIntersect e f = true →
      ∀ k, X e k → X f k → False
  no_two_common : ∀ (e f : Fin 72),
    e ≠ f → ∀ (k l : Fin 72), k ≠ l →
      X e k → X f k → X e l → X f l → False

theorem mem_muNegFiveZeroThreeServiceVariables_iff
    (e : Fin 72) (v : Fin 16) (lit : Int) :
    lit ∈ muNegFiveZeroThreeServiceVariables e v ↔
      ∃ f : Fin 72, f ≠ e ∧
        muNegFiveZeroThreeOwnerContains f v = true ∧
        muNegFiveZeroThreeHitLiteral? e f = some lit := by
  simp only [muNegFiveZeroThreeServiceVariables, List.mem_filterMap,
    List.mem_range]
  constructor
  · rintro ⟨f, hf72, hflit⟩
    split at hflit
    · next hcond =>
      have hc : f ≠ e.val ∧
          muNegFiveZeroThreeOwnerContains f v = true := by
        simpa using hcond
      refine ⟨⟨f, hf72⟩, ?_, ?_, ?_⟩
      · intro h
        exact hc.1 (congrArg Fin.val h)
      · simpa using hc.2
      · simpa using hflit
    · simp at hflit
  · rintro ⟨f, hfe, hcontains, hlit⟩
    refine ⟨f, f.2, ?_⟩
    rw [if_pos]
    · exact hlit
    · have hne : f.val ≠ e.val := fun h => hfe (Fin.ext h)
      simp [hne, hcontains]

theorem muNegFiveZeroThreeHitVariable?_positive
    {e f : Fin 72} {id : Nat}
    (hvar : muNegFiveZeroThreeHitVariable? e f = some id) : 0 < id := by
  exact Nat.lt_trans (by omega : 0 < 64)
    (muNegFiveZeroThreeHitVariable?_above_active hvar)

theorem muNegFiveZeroThreeHitLiteral?_eq_some
    {e f : Fin 72} {lit : Int}
    (hlit : muNegFiveZeroThreeHitLiteral? e f = some lit) :
    ∃ id : Nat, muNegFiveZeroThreeHitVariable? e f = some id ∧
      lit = Int.ofNat id := by
  unfold muNegFiveZeroThreeHitLiteral? at hlit
  cases hvar : muNegFiveZeroThreeHitVariable? e f with
  | none => simp [hvar] at hlit
  | some id =>
      simp [hvar] at hlit
      exact ⟨id, rfl, hlit.symm⟩

theorem muNegFiveZeroThreeHitVariable?_exists
    (e f : Fin 72) (hef : e ≠ f)
    (hcompat : muNegFiveZeroThreeOwnerCompatible e f = true) :
    ∃ id, muNegFiveZeroThreeHitVariable? e f = some id := by
  have hs : (muNegFiveZeroThreeHitVariable? e f).isSome = true := by
    revert e f
    native_decide
  cases hvar : muNegFiveZeroThreeHitVariable? e f with
  | none => simp [hvar] at hs
  | some id => exact ⟨id, rfl⟩

theorem muNegFiveZeroThreeActiveGuard_satisfied_of_not_enabled
    (active : Fin 72 → Prop) (X : Fin 72 → Fin 72 → Prop)
    [DecidablePred active] [DecidableRel X]
    (e : Fin 72) (hdisabled : ¬ muNegFiveZeroThreeOwnerEnabled active e) :
    dimacsClauseSatisfied
      (muNegFiveZeroThreeOwnerValOfRelations active X)
      (muNegFiveZeroThreeActiveGuard e) := by
  unfold muNegFiveZeroThreeOwnerEnabled at hdisabled
  unfold muNegFiveZeroThreeActiveGuard
  cases hvar : muNegFiveZeroThreeActiveVariable? e with
  | none => simp [hvar] at hdisabled
  | some id =>
      have hnotactive : ¬ active e := by simpa [hvar] using hdisabled
      have hvalfalse :
          muNegFiveZeroThreeOwnerValOfRelations active X id = false := by
        apply Bool.eq_false_of_not_eq_true
        intro hval
        exact hnotactive
          (muNegFiveZeroThreeOwnerActive_of_val_true active X hvar hval)
      refine ⟨-Int.ofNat id, by simp, ?_⟩
      simp [dimacsLitValue, hvalfalse]

theorem muNegFiveZeroThreeServiceExistsClauseSatisfied_of_relation
    (active : Fin 72 → Prop) (X : Fin 72 → Fin 72 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsem : MuNegFiveZeroThreeOwnerServiceSemantics active X)
    (hirr : ∀ e, ¬ X e e)
    (hcompat : ∀ e f, X e f →
      muNegFiveZeroThreeOwnerCompatible e f = true)
    (e v : Nat) (he : e < 72) (hv : v < 16)
    (htarget : muNegFiveZeroThreeOwnerTargetContains e v = true) :
    dimacsClauseSatisfied
      (muNegFiveZeroThreeOwnerValOfRelations active X)
      (muNegFiveZeroThreeActiveGuard e ++
        muNegFiveZeroThreeServiceVariables e v) := by
  let ef : Fin 72 := ⟨e, he⟩
  let vf : Fin 16 := ⟨v, hv⟩
  by_cases henabled : muNegFiveZeroThreeOwnerEnabled active ef
  · obtain ⟨f, hX, hcontains⟩ :=
      hsem.service_exists ef vf henabled (by simpa using htarget)
    have hfe : f ≠ ef := by
      intro h
      subst f
      exact hirr ef hX
    obtain ⟨id, hvar⟩ :=
      muNegFiveZeroThreeHitVariable?_exists ef f hfe.symm
        (hcompat ef f hX)
    have hlit : muNegFiveZeroThreeHitLiteral? ef f =
        some (Int.ofNat id) := by
      simp [muNegFiveZeroThreeHitLiteral?, hvar]
    have hmem : Int.ofNat id ∈
        muNegFiveZeroThreeServiceVariables e v :=
      (mem_muNegFiveZeroThreeServiceVariables_iff ef vf
        (Int.ofNat id)).mpr ⟨f, hfe, hcontains, hlit⟩
    refine ⟨Int.ofNat id, List.mem_append.mpr (Or.inr hmem), ?_⟩
    have hval := muNegFiveZeroThreeOwnerVal_hit_true_of active X hvar hX
    have hid := muNegFiveZeroThreeHitVariable?_positive hvar
    simp [dimacsLitValue, hid, hval]
  · obtain ⟨lit, hmem, hsat⟩ :=
      muNegFiveZeroThreeActiveGuard_satisfied_of_not_enabled
        active X ef henabled
    exact ⟨lit, List.mem_append.mpr (Or.inl hmem), hsat⟩

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

/-- Certificate-facing relation terminal.  Cross degree, intertwining, and
hit activity are discharged here; the graph adapter's exact residual is the
service and exterior-C4 clause families. -/
theorem muNegFiveZeroThreeOwnerRelations_false
    (sigma : Bool)
    (active : Fin 72 → Prop) (X : Fin 72 → Fin 72 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsymm : ∀ e f, X e f → X f e)
    (hends : ∀ e f, X e f → active e ∧ active f)
    (hfiber : ∀ left z, z < 8 →
      muNegFiveZeroThreeFiberBitsAllowed sigma left z
        (muNegFiveZeroThreeFiberBit
          (muNegFiveZeroThreeOwnerValOfRelations active X) left z) = true)
    (hbalance : ∀ x y a b c d,
      muNegFiveZeroThreeCrossIndex? ((x + 7) % 8) y = some a →
      muNegFiveZeroThreeCrossIndex? ((x + 1) % 8) y = some b →
      muNegFiveZeroThreeCrossIndex? x ((y + 1) % 8) = some c →
      muNegFiveZeroThreeCrossIndex? x ((y + 7) % 8) = some d →
      (muNegFiveZeroThreeOwnerValOfRelations active X a).toNat +
          (muNegFiveZeroThreeOwnerValOfRelations active X b).toNat =
        (muNegFiveZeroThreeOwnerValOfRelations active X c).toNat +
          (muNegFiveZeroThreeOwnerValOfRelations active X d).toNat)
    (hservice : ∀ clause ∈ muNegFiveZeroThreeServiceClauses,
      dimacsClauseSatisfied
        (muNegFiveZeroThreeOwnerValOfRelations active X) clause)
    (hc4 : ∀ clause ∈ muNegFiveZeroThreeC4Clauses,
      dimacsClauseSatisfied
        (muNegFiveZeroThreeOwnerValOfRelations active X) clause) : False := by
  apply muNegFiveZeroThreeOwnerConstraintSemantics_false
  exact
    { cross_degree :=
        muNegFiveZeroThreeCrossDegreeClauses_satisfied sigma
          (muNegFiveZeroThreeOwnerValOfRelations active X) hfiber
      intertwining :=
        muNegFiveZeroThreeIntertwiningClauses_satisfied
          (muNegFiveZeroThreeOwnerValOfRelations active X) hbalance
      hit_activity :=
        muNegFiveZeroThreeHitActivityClauses_satisfied active X hsymm hends
      service := hservice
      exterior_c4 := hc4 }

end Erdos85

#print axioms Erdos85.muNegFiveZeroThreeHitActivityClauses_satisfied
#print axioms Erdos85.muNegFiveZeroThreeServiceExistsClauseSatisfied_of_relation
#print axioms Erdos85.muNegFiveZeroThreeOwnerRelations_false
