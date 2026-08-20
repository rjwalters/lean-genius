import Proofs.Erdos85MuNegFiveOneTwoCrossOnlyOwnerBridge
import Proofs.Erdos85MuNegFiveCanonicalOwnerCrossBridge

/-!
# Relation-level hit, service, and C4 bridge for cross-only h512

This file transports clean owner-activity and owner-adjacency laws into the
three non-structural DIMACS families.  The first increment closes hit
activity.
-/

namespace Erdos85

open Std Sat

set_option maxHeartbeats 0

def muNegFiveOneTwoCrossOnlyOwnerEnabled
    (active : Fin 64 → Prop) (e : Fin 64) : Prop :=
  match muNegFiveOneTwoCrossOnlyActiveVariable? e with
  | some _ => active e
  | none => True

structure MuNegFiveOneTwoCrossOnlyOwnerServiceSemantics
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop) : Prop where
  service_exists : ∀ (e : Fin 64) (v : Fin 16),
    muNegFiveOneTwoCrossOnlyOwnerEnabled active e →
    muNegFiveOneTwoCrossOnlyOwnerTargetContains e v = true →
      ∃ f, X e f ∧ muNegFiveOneTwoCrossOnlyOwnerContains f v = true
  service_unique : ∀ (e : Fin 64) (v : Fin 16) (f g : Fin 64),
    X e f → muNegFiveOneTwoCrossOnlyOwnerContains f v = true →
    X e g → muNegFiveOneTwoCrossOnlyOwnerContains g v = true → f = g
  internal_zero : ∀ (e : Fin 64) (v : Fin 16) (f : Fin 64),
    muNegFiveOneTwoCrossOnlyOwnerTargetContains e v = false →
    muNegFiveOneTwoCrossOnlyOwnerContains f v = true → ¬ X e f
  intersecting_no_common : ∀ (e f : Fin 64),
    e ≠ f → muNegFiveOneTwoCrossOnlyOwnersIntersect e f = true →
      ∀ k, X e k → X f k → False
  no_two_common : ∀ (e f : Fin 64),
    e ≠ f → ∀ (k l : Fin 64), k ≠ l →
      X e k → X f k → X e l → X f l → False

theorem mem_muNegFiveOneTwoCrossOnlyServiceVariables_iff
    (e : Fin 64) (v : Fin 16) (lit : Int) :
    lit ∈ muNegFiveOneTwoCrossOnlyServiceVariables e v ↔
      ∃ f : Fin 64, f ≠ e ∧
        muNegFiveOneTwoCrossOnlyOwnerContains f v = true ∧
        muNegFiveOneTwoCrossOnlyHitLiteral? e f = some lit := by
  simp only [muNegFiveOneTwoCrossOnlyServiceVariables, List.mem_filterMap,
    List.mem_range]
  constructor
  · rintro ⟨f, hf72, hflit⟩
    split at hflit
    · next hcond =>
      have hc : f ≠ e.val ∧
          muNegFiveOneTwoCrossOnlyOwnerContains f v = true := by
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

theorem muNegFiveOneTwoCrossOnlyHitVariable?_positive
    {e f : Fin 64} {id : Nat}
    (hvar : muNegFiveOneTwoCrossOnlyHitVariable? e f = some id) : 0 < id := by
  exact Nat.lt_trans (by omega : 0 < 64)
    (muNegFiveOneTwoCrossOnlyHitVariable?_above_active hvar)

theorem muNegFiveOneTwoCrossOnlyHitLiteral?_eq_some
    {e f : Fin 64} {lit : Int}
    (hlit : muNegFiveOneTwoCrossOnlyHitLiteral? e f = some lit) :
    ∃ id : Nat, muNegFiveOneTwoCrossOnlyHitVariable? e f = some id ∧
      lit = Int.ofNat id := by
  unfold muNegFiveOneTwoCrossOnlyHitLiteral? at hlit
  cases hvar : muNegFiveOneTwoCrossOnlyHitVariable? e f with
  | none => simp [hvar] at hlit
  | some id =>
      simp [hvar] at hlit
      exact ⟨id, rfl, hlit.symm⟩

theorem muNegFiveOneTwoCrossOnlyHitVariable?_exists
    (e f : Fin 64) (hef : e ≠ f)
    (hcompat : muNegFiveOneTwoCrossOnlyOwnerCompatible e f = true) :
    ∃ id, muNegFiveOneTwoCrossOnlyHitVariable? e f = some id := by
  have hs : (muNegFiveOneTwoCrossOnlyHitVariable? e f).isSome = true := by
    revert e f
    native_decide
  cases hvar : muNegFiveOneTwoCrossOnlyHitVariable? e f with
  | none => simp [hvar] at hs
  | some id => exact ⟨id, rfl⟩

theorem muNegFiveOneTwoCrossOnlyActiveGuard_satisfied_of_not_enabled
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    (e : Fin 64) (hdisabled : ¬ muNegFiveOneTwoCrossOnlyOwnerEnabled active e) :
    dimacsClauseSatisfied
      (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X)
      (muNegFiveOneTwoCrossOnlyActiveGuard e) := by
  unfold muNegFiveOneTwoCrossOnlyOwnerEnabled at hdisabled
  unfold muNegFiveOneTwoCrossOnlyActiveGuard
  cases hvar : muNegFiveOneTwoCrossOnlyActiveVariable? e with
  | none => simp [hvar] at hdisabled
  | some id =>
      have hnotactive : ¬ active e := by simpa [hvar] using hdisabled
      have hvalfalse :
          muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X id = false := by
        apply Bool.eq_false_of_not_eq_true
        intro hval
        exact hnotactive
          (muNegFiveOneTwoCrossOnlyOwnerActive_of_val_true active X hvar hval)
      refine ⟨-Int.ofNat id, by simp, ?_⟩
      simp [dimacsLitValue, hvalfalse]

theorem muNegFiveOneTwoCrossOnlyServiceExistsClauseSatisfied_of_relation
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsem : MuNegFiveOneTwoCrossOnlyOwnerServiceSemantics active X)
    (hirr : ∀ e, ¬ X e e)
    (hcompat : ∀ e f, X e f →
      muNegFiveOneTwoCrossOnlyOwnerCompatible e f = true)
    (e v : Nat) (he : e < 64) (hv : v < 16)
    (htarget : muNegFiveOneTwoCrossOnlyOwnerTargetContains e v = true) :
    dimacsClauseSatisfied
      (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X)
      (muNegFiveOneTwoCrossOnlyActiveGuard e ++
        muNegFiveOneTwoCrossOnlyServiceVariables e v) := by
  let ef : Fin 64 := ⟨e, he⟩
  let vf : Fin 16 := ⟨v, hv⟩
  by_cases henabled : muNegFiveOneTwoCrossOnlyOwnerEnabled active ef
  · obtain ⟨f, hX, hcontains⟩ :=
      hsem.service_exists ef vf henabled (by simpa using htarget)
    have hfe : f ≠ ef := by
      intro h
      subst f
      exact hirr ef hX
    obtain ⟨id, hvar⟩ :=
      muNegFiveOneTwoCrossOnlyHitVariable?_exists ef f hfe.symm
        (hcompat ef f hX)
    have hlit : muNegFiveOneTwoCrossOnlyHitLiteral? ef f =
        some (Int.ofNat id) := by
      simp [muNegFiveOneTwoCrossOnlyHitLiteral?, hvar]
    have hmem : Int.ofNat id ∈
        muNegFiveOneTwoCrossOnlyServiceVariables e v :=
      (mem_muNegFiveOneTwoCrossOnlyServiceVariables_iff ef vf
        (Int.ofNat id)).mpr ⟨f, hfe, hcontains, hlit⟩
    refine ⟨Int.ofNat id, List.mem_append.mpr (Or.inr hmem), ?_⟩
    have hval := muNegFiveOneTwoCrossOnlyOwnerVal_hit_true_of active X hvar hX
    have hid := muNegFiveOneTwoCrossOnlyHitVariable?_positive hvar
    simp [dimacsLitValue, hid, hval]
  · obtain ⟨lit, hmem, hsat⟩ :=
      muNegFiveOneTwoCrossOnlyActiveGuard_satisfied_of_not_enabled
        active X ef henabled
    exact ⟨lit, List.mem_append.mpr (Or.inl hmem), hsat⟩

theorem muNegFiveOneTwoCrossOnlyServiceUniqueClauseSatisfied_of_relation
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsem : MuNegFiveOneTwoCrossOnlyOwnerServiceSemantics active X)
    (hsymm : ∀ e f, X e f → X f e)
    (e v : Nat) (he : e < 64) (hv : v < 16)
    (_htarget : muNegFiveOneTwoCrossOnlyOwnerTargetContains e v = true)
    (clause : DimacsClause)
    (hclause : clause ∈ eightEightPairwiseNegativeClauses
      (muNegFiveOneTwoCrossOnlyServiceVariables e v)) :
    dimacsClauseSatisfied
      (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X) clause := by
  simp only [eightEightPairwiseNegativeClauses, List.mem_flatMap,
    List.mem_map, List.mem_filter] at hclause
  obtain ⟨x, hxrow, y, ⟨hyrow, hxy⟩, rfl⟩ := hclause
  let ef : Fin 64 := ⟨e, he⟩
  let vf : Fin 16 := ⟨v, hv⟩
  obtain ⟨f, _hfe, hfcontains, hfx⟩ :=
    (mem_muNegFiveOneTwoCrossOnlyServiceVariables_iff ef vf x).mp hxrow
  obtain ⟨g, _hge, hgcontains, hgy⟩ :=
    (mem_muNegFiveOneTwoCrossOnlyServiceVariables_iff ef vf y).mp hyrow
  obtain ⟨ix, hvarx, rfl⟩ :=
    muNegFiveOneTwoCrossOnlyHitLiteral?_eq_some hfx
  obtain ⟨iy, hvary, rfl⟩ :=
    muNegFiveOneTwoCrossOnlyHitLiteral?_eq_some hgy
  by_cases hxval :
      muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X ix = true
  · have hXf := muNegFiveOneTwoCrossOnlyOwnerRelation_of_val_true
      active X hsymm hvarx hxval
    have hyfalse :
        muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X iy = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hyval
      have hXg := muNegFiveOneTwoCrossOnlyOwnerRelation_of_val_true
        active X hsymm hvary hyval
      have hfg := hsem.service_unique ef vf f g
        hXf hfcontains hXg hgcontains
      subst g
      have : ix = iy := by simpa [hvarx] using hvary
      subst iy
      simp at hxy
    refine ⟨-Int.ofNat iy, by simp, ?_⟩
    simp [dimacsLitValue, hyfalse]
  · have hxf :
        muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X ix = false :=
      Bool.eq_false_of_not_eq_true hxval
    refine ⟨-Int.ofNat ix, by simp, ?_⟩
    simp [dimacsLitValue, hxf]

theorem muNegFiveOneTwoCrossOnlyInternalZeroClauseSatisfied_of_relation
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsem : MuNegFiveOneTwoCrossOnlyOwnerServiceSemantics active X)
    (hsymm : ∀ e f, X e f → X f e)
    (e v : Nat) (he : e < 64) (hv : v < 16)
    (htarget : muNegFiveOneTwoCrossOnlyOwnerTargetContains e v = false)
    (x : Int) (hx : x ∈ muNegFiveOneTwoCrossOnlyServiceVariables e v) :
    dimacsClauseSatisfied
      (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X)
      (muNegFiveOneTwoCrossOnlyActiveGuard e ++ [-x]) := by
  let ef : Fin 64 := ⟨e, he⟩
  let vf : Fin 16 := ⟨v, hv⟩
  by_cases henabled : muNegFiveOneTwoCrossOnlyOwnerEnabled active ef
  · obtain ⟨f, _hfe, hfcontains, hfx⟩ :=
      (mem_muNegFiveOneTwoCrossOnlyServiceVariables_iff ef vf x).mp hx
    obtain ⟨id, hvar, rfl⟩ :=
      muNegFiveOneTwoCrossOnlyHitLiteral?_eq_some hfx
    have hvalfalse :
        muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X id = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hval
      have hX := muNegFiveOneTwoCrossOnlyOwnerRelation_of_val_true
        active X hsymm hvar hval
      exact hsem.internal_zero ef vf f (by simpa using htarget)
        hfcontains hX
    refine ⟨-Int.ofNat id, List.mem_append.mpr (Or.inr (by simp)), ?_⟩
    simp [dimacsLitValue, hvalfalse]
  · obtain ⟨lit, hmem, hsat⟩ :=
      muNegFiveOneTwoCrossOnlyActiveGuard_satisfied_of_not_enabled
        active X ef henabled
    exact ⟨lit, List.mem_append.mpr (Or.inl hmem), hsat⟩

/-- The clean five-field owner laws imply every generated guarded service
clause. -/
theorem muNegFiveOneTwoCrossOnlyServiceClauses_satisfied
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsem : MuNegFiveOneTwoCrossOnlyOwnerServiceSemantics active X)
    (hsymm : ∀ e f, X e f → X f e)
    (hirr : ∀ e, ¬ X e e)
    (hcompat : ∀ e f, X e f →
      muNegFiveOneTwoCrossOnlyOwnerCompatible e f = true) :
    ∀ clause ∈ muNegFiveOneTwoCrossOnlyServiceClauses,
      dimacsClauseSatisfied
        (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X) clause := by
  intro clause hclause
  simp only [muNegFiveOneTwoCrossOnlyServiceClauses, List.mem_flatMap,
    List.mem_range] at hclause
  obtain ⟨e, he72, v, hv16, hclause⟩ := hclause
  split at hclause
  · next htarget =>
    rcases List.mem_append.mp hclause with hexists | hunique
    · simp only [List.mem_singleton] at hexists
      subst clause
      exact muNegFiveOneTwoCrossOnlyServiceExistsClauseSatisfied_of_relation
        active X hsem hirr hcompat e v he72 hv16 (by
          simpa only [muNegFiveOneTwoCrossOnlyOwnerTargetContains] using htarget)
    · exact muNegFiveOneTwoCrossOnlyServiceUniqueClauseSatisfied_of_relation
        active X hsem hsymm e v he72 hv16 (by
          simpa only [muNegFiveOneTwoCrossOnlyOwnerTargetContains] using htarget)
        clause hunique
  · next hnotTarget =>
    simp only [List.mem_map] at hclause
    obtain ⟨x, hx, rfl⟩ := hclause
    have hfalse :
        muNegFiveOneTwoCrossOnlyOwnerTargetContains e v = false := by
      apply Bool.eq_false_iff.mpr
      simpa only [muNegFiveOneTwoCrossOnlyOwnerTargetContains] using hnotTarget
    exact muNegFiveOneTwoCrossOnlyInternalZeroClauseSatisfied_of_relation
      active X hsem hsymm e v he72 hv16 hfalse x hx

theorem muNegFiveOneTwoCrossOnlyNoCommonClauseSatisfied_of_relation
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsem : MuNegFiveOneTwoCrossOnlyOwnerServiceSemantics active X)
    (hsymm : ∀ e f, X e f → X f e)
    (e f : Nat) (hef : e < f) (hf72 : f < 64)
    (hintersect : muNegFiveOneTwoCrossOnlyOwnersIntersect e f = true)
    (clause : DimacsClause)
    (hclause : clause ∈ muNegFiveOneTwoCrossOnlyNoCommonClauses e f) :
    dimacsClauseSatisfied
      (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X) clause := by
  simp only [muNegFiveOneTwoCrossOnlyNoCommonClauses, List.mem_filterMap]
    at hclause
  obtain ⟨k, hkcand, hclause⟩ := hclause
  simp only [muNegFiveOneTwoCrossOnlyCommonCandidates, List.mem_filter,
    List.mem_range] at hkcand
  have hk72 := hkcand.1
  cases hxe : muNegFiveOneTwoCrossOnlyHitLiteral? e k with
  | none => simp [hxe] at hclause
  | some x =>
    cases hyf : muNegFiveOneTwoCrossOnlyHitLiteral? f k with
    | none => simp [hxe, hyf] at hclause
    | some y =>
      simp [hxe, hyf] at hclause
      subst clause
      let ef : Fin 64 := ⟨e, by omega⟩
      let ff : Fin 64 := ⟨f, hf72⟩
      let kf : Fin 64 := ⟨k, hk72⟩
      have hxe' : muNegFiveOneTwoCrossOnlyHitLiteral? ef kf = some x := by
        simpa [ef, kf] using hxe
      have hyf' : muNegFiveOneTwoCrossOnlyHitLiteral? ff kf = some y := by
        simpa [ff, kf] using hyf
      obtain ⟨ix, hvarx, rfl⟩ :=
        muNegFiveOneTwoCrossOnlyHitLiteral?_eq_some hxe'
      obtain ⟨iy, hvary, rfl⟩ :=
        muNegFiveOneTwoCrossOnlyHitLiteral?_eq_some hyf'
      by_cases hxval :
          muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X ix = true
      · have hXek := muNegFiveOneTwoCrossOnlyOwnerRelation_of_val_true
          active X hsymm hvarx hxval
        have hyfalse :
            muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X iy = false := by
          apply Bool.eq_false_of_not_eq_true
          intro hyval
          have hXfk := muNegFiveOneTwoCrossOnlyOwnerRelation_of_val_true
            active X hsymm hvary hyval
          exact hsem.intersecting_no_common ef ff (by
            intro h
            have := congrArg Fin.val h
            dsimp [ef, ff] at this
            omega) (by simpa using hintersect) kf hXek hXfk
        refine ⟨-Int.ofNat iy, by simp, ?_⟩
        simp [dimacsLitValue, hyfalse]
      · have hxf :
            muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X ix = false :=
          Bool.eq_false_of_not_eq_true hxval
        refine ⟨-Int.ofNat ix, by simp, ?_⟩
        simp [dimacsLitValue, hxf]

theorem muNegFiveOneTwoCrossOnlyAtMostOneCommonClauseSatisfied_of_relation
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsem : MuNegFiveOneTwoCrossOnlyOwnerServiceSemantics active X)
    (hsymm : ∀ e f, X e f → X f e)
    (e f : Nat) (hef : e < f) (hf72 : f < 64)
    (clause : DimacsClause)
    (hclause : clause ∈
      muNegFiveOneTwoCrossOnlyAtMostOneCommonClauses e f) :
    dimacsClauseSatisfied
      (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X) clause := by
  simp only [muNegFiveOneTwoCrossOnlyAtMostOneCommonClauses, List.mem_flatMap,
    List.mem_filterMap, List.mem_filter] at hclause
  obtain ⟨k, hkcand, l, ⟨hlcand, hkl⟩, hclause⟩ := hclause
  have hk72 : k < 64 := by
    have hkdata := hkcand
    simp only [muNegFiveOneTwoCrossOnlyCommonCandidates, List.mem_filter,
      List.mem_range] at hkdata
    exact hkdata.1
  have hl72 : l < 64 := by
    have hldata := hlcand
    simp only [muNegFiveOneTwoCrossOnlyCommonCandidates, List.mem_filter,
      List.mem_range] at hldata
    exact hldata.1
  have hklNat : k < l := by simpa using hkl
  cases hxek : muNegFiveOneTwoCrossOnlyHitLiteral? e k with
  | none => simp [hxek] at hclause
  | some xek =>
    cases hxfk : muNegFiveOneTwoCrossOnlyHitLiteral? f k with
    | none => simp [hxek, hxfk] at hclause
    | some xfk =>
      cases hxel : muNegFiveOneTwoCrossOnlyHitLiteral? e l with
      | none => simp [hxek, hxfk, hxel] at hclause
      | some xel =>
        cases hxfl : muNegFiveOneTwoCrossOnlyHitLiteral? f l with
        | none => simp [hxek, hxfk, hxel, hxfl] at hclause
        | some xfl =>
          simp [hxek, hxfk, hxel, hxfl] at hclause
          subst clause
          let ef : Fin 64 := ⟨e, by omega⟩
          let ff : Fin 64 := ⟨f, hf72⟩
          let kf : Fin 64 := ⟨k, hk72⟩
          let lf : Fin 64 := ⟨l, hl72⟩
          have hxek' : muNegFiveOneTwoCrossOnlyHitLiteral? ef kf =
              some xek := by simpa [ef, kf] using hxek
          have hxfk' : muNegFiveOneTwoCrossOnlyHitLiteral? ff kf =
              some xfk := by simpa [ff, kf] using hxfk
          have hxel' : muNegFiveOneTwoCrossOnlyHitLiteral? ef lf =
              some xel := by simpa [ef, lf] using hxel
          have hxfl' : muNegFiveOneTwoCrossOnlyHitLiteral? ff lf =
              some xfl := by simpa [ff, lf] using hxfl
          obtain ⟨iek, hvek, rfl⟩ :=
            muNegFiveOneTwoCrossOnlyHitLiteral?_eq_some hxek'
          obtain ⟨ifk, hvfk, rfl⟩ :=
            muNegFiveOneTwoCrossOnlyHitLiteral?_eq_some hxfk'
          obtain ⟨iel, hvel, rfl⟩ :=
            muNegFiveOneTwoCrossOnlyHitLiteral?_eq_some hxel'
          obtain ⟨ifl, hvfl, rfl⟩ :=
            muNegFiveOneTwoCrossOnlyHitLiteral?_eq_some hxfl'
          by_cases hekval :
              muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X iek = true
          · by_cases hfkval :
                muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X ifk = true
            · by_cases helval :
                  muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X iel = true
              · have hflfalse :
                    muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X ifl =
                      false := by
                  apply Bool.eq_false_of_not_eq_true
                  intro hflval
                  have hXek := muNegFiveOneTwoCrossOnlyOwnerRelation_of_val_true
                    active X hsymm hvek hekval
                  have hXfk := muNegFiveOneTwoCrossOnlyOwnerRelation_of_val_true
                    active X hsymm hvfk hfkval
                  have hXel := muNegFiveOneTwoCrossOnlyOwnerRelation_of_val_true
                    active X hsymm hvel helval
                  have hXfl := muNegFiveOneTwoCrossOnlyOwnerRelation_of_val_true
                    active X hsymm hvfl hflval
                  exact hsem.no_two_common ef ff (by
                    intro h
                    have := congrArg Fin.val h
                    dsimp [ef, ff] at this
                    omega) kf lf (by
                      intro h
                      have := congrArg Fin.val h
                      dsimp [kf, lf] at this
                      exact (Nat.ne_of_lt hklNat) this)
                    hXek hXfk hXel hXfl
                refine ⟨-Int.ofNat ifl, by simp, ?_⟩
                simp [dimacsLitValue, hflfalse]
              · have hfalse := Bool.eq_false_of_not_eq_true helval
                refine ⟨-Int.ofNat iel, by simp, ?_⟩
                simp [dimacsLitValue, hfalse]
            · have hfalse := Bool.eq_false_of_not_eq_true hfkval
              refine ⟨-Int.ofNat ifk, by simp, ?_⟩
              simp [dimacsLitValue, hfalse]
          · have hfalse := Bool.eq_false_of_not_eq_true hekval
            refine ⟨-Int.ofNat iek, by simp, ?_⟩
            simp [dimacsLitValue, hfalse]

theorem muNegFiveOneTwoCrossOnlyC4Clauses_satisfied
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsem : MuNegFiveOneTwoCrossOnlyOwnerServiceSemantics active X)
    (hsymm : ∀ e f, X e f → X f e) :
    ∀ clause ∈ muNegFiveOneTwoCrossOnlyC4Clauses,
      dimacsClauseSatisfied
        (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X) clause := by
  intro clause hclause
  simp only [muNegFiveOneTwoCrossOnlyC4Clauses, List.mem_flatMap,
    List.mem_range, List.mem_filter] at hclause
  obtain ⟨e, he72, f, ⟨hf72, hef⟩, hclause⟩ := hclause
  split at hclause
  · next hintersect =>
    exact muNegFiveOneTwoCrossOnlyNoCommonClauseSatisfied_of_relation
      active X hsem hsymm e f (of_decide_eq_true hef) hf72
      (by simpa using hintersect) clause hclause
  · exact muNegFiveOneTwoCrossOnlyAtMostOneCommonClauseSatisfied_of_relation
      active X hsem hsymm e f (of_decide_eq_true hef) hf72 clause hclause

theorem muNegFiveOneTwoCrossOnlyHitVariable?_some_of_mem
    {e f : Nat} (hmem : (e, f) ∈ muNegFiveOneTwoCrossOnlyHitVariables) :
    e < 64 ∧ f < 64 ∧
      ∃ id, muNegFiveOneTwoCrossOnlyHitVariable? e f = some id := by
  have hbounds : e < 64 ∧ f < 64 := by
    simp only [muNegFiveOneTwoCrossOnlyHitVariables, List.mem_flatMap,
      List.mem_range, List.mem_map, List.mem_filter] at hmem
    obtain ⟨e', he', f', ⟨hf', hcond⟩, hp⟩ := hmem
    have heq : e' = e := congrArg Prod.fst hp
    have hfeq : f' = f := congrArg Prod.snd hp
    omega
  have hef : e < f := by
    simp only [muNegFiveOneTwoCrossOnlyHitVariables, List.mem_flatMap,
      List.mem_range, List.mem_map, List.mem_filter] at hmem
    obtain ⟨e', _, f', ⟨_, hcond⟩, hp⟩ := hmem
    have hef' : e' < f' := by
      simp at hcond
      exact hcond.1
    have heq : e' = e := congrArg Prod.fst hp
    have hfeq : f' = f := congrArg Prod.snd hp
    omega
  have hsome :
      (muNegFiveOneTwoCrossOnlyHitVariables.idxOf? (e, f)).isSome := by
    simpa using hmem
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨hbounds.1, hbounds.2, i + 65, ?_⟩
  simp [muNegFiveOneTwoCrossOnlyHitVariable?, hef, hi]

/-- Every encoded hit joins enabled owners, so each emitted negative-hit
activity guard is satisfied. -/
theorem muNegFiveOneTwoCrossOnlyHitActivityClauses_satisfied
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsymm : ∀ e f, X e f → X f e)
    (hends : ∀ e f, X e f → active e ∧ active f) :
    ∀ clause ∈ muNegFiveOneTwoCrossOnlyHitActivityClauses,
      dimacsClauseSatisfied
        (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X) clause := by
  intro clause hclause
  simp only [muNegFiveOneTwoCrossOnlyHitActivityClauses, List.mem_flatMap]
    at hclause
  obtain ⟨p, hp, hclause⟩ := hclause
  rcases p with ⟨e, f⟩
  obtain ⟨he, hf, hitId, hhit⟩ :=
    muNegFiveOneTwoCrossOnlyHitVariable?_some_of_mem hp
  let ef : Fin 64 := ⟨e, he⟩
  let ff : Fin 64 := ⟨f, hf⟩
  have hhitFin : muNegFiveOneTwoCrossOnlyHitVariable? ef ff = some hitId := by
    simpa [ef, ff] using hhit
  simp only [hhit, Option.getD_some] at hclause
  have hsatisfy (q : Fin 64) (activeId : Nat)
      (hactiveVar : muNegFiveOneTwoCrossOnlyActiveVariable? q = some activeId)
      (hendpoint : ∀ hX : X ef ff, active q) :
      dimacsClauseSatisfied
        (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X)
        [-Int.ofNat hitId, Int.ofNat activeId] := by
    by_cases hval :
        muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X hitId = true
    · have hX := muNegFiveOneTwoCrossOnlyOwnerRelation_of_val_true active X hsymm
          hhitFin hval
      refine ⟨Int.ofNat activeId, by simp, ?_⟩
      have haval := muNegFiveOneTwoCrossOnlyOwnerVal_active_true_of active X
        hactiveVar (hendpoint hX)
      simp [dimacsLitValue,
        (muNegFiveOneTwoCrossOnlyActiveVariable?_bounds hactiveVar).1, haval]
    · refine ⟨-Int.ofNat hitId, by simp, ?_⟩
      have hfalse :
          muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X hitId = false :=
        Bool.eq_false_of_not_eq_true hval
      simp [dimacsLitValue, hfalse]
  generalize hea : muNegFiveOneTwoCrossOnlyActiveVariable? e = oe at hclause
  generalize hfa : muNegFiveOneTwoCrossOnlyActiveVariable? f = of_ at hclause
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
theorem muNegFiveOneTwoCrossOnlyOwnerRelations_false
    (sigma : Bool)
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsymm : ∀ e f, X e f → X f e)
    (hends : ∀ e f, X e f → active e ∧ active f)
    (hfiber : ∀ left z, z < 8 →
      muNegFiveCanonicalFiberBitsAllowed 6 4 sigma left z
        (muNegFiveZeroThreeFiberBit
          (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X) left z) = true)
    (hbalance : ∀ x y a b c d,
      muNegFiveZeroThreeCrossIndex? ((x + 7) % 8) y = some a →
      muNegFiveZeroThreeCrossIndex? ((x + 1) % 8) y = some b →
      muNegFiveZeroThreeCrossIndex? x ((y + 1) % 8) = some c →
      muNegFiveZeroThreeCrossIndex? x ((y + 7) % 8) = some d →
      (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X a).toNat +
          (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X b).toNat =
        (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X c).toNat +
          (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X d).toNat)
    (hservice : ∀ clause ∈ muNegFiveOneTwoCrossOnlyServiceClauses,
      dimacsClauseSatisfied
        (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X) clause)
    (hc4 : ∀ clause ∈ muNegFiveOneTwoCrossOnlyC4Clauses,
      dimacsClauseSatisfied
        (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X) clause) : False := by
  apply muNegFiveOneTwoCrossOnlyOwnerConstraintSemantics_false
  exact
    { cross_degree :=
        muNegFiveOneTwoCrossDegreeClauses_satisfied sigma
          (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X) hfiber
      intertwining :=
        muNegFiveZeroThreeIntertwiningClauses_satisfied
          (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X) hbalance
      hit_activity :=
        muNegFiveOneTwoCrossOnlyHitActivityClauses_satisfied active X hsymm hends
      service := hservice
      exterior_c4 := hc4 }

/-- Fully clean relation terminal: the graph adapter supplies only owner laws
and the two structural cross-block equations. -/
theorem muNegFiveOneTwoCrossOnlyOwnerRelations_false_of_serviceSemantics
    (sigma : Bool)
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsem : MuNegFiveOneTwoCrossOnlyOwnerServiceSemantics active X)
    (hsymm : ∀ e f, X e f → X f e)
    (hirr : ∀ e, ¬ X e e)
    (hcompat : ∀ e f, X e f →
      muNegFiveOneTwoCrossOnlyOwnerCompatible e f = true)
    (hends : ∀ e f, X e f → active e ∧ active f)
    (hfiber : ∀ left z, z < 8 →
      muNegFiveCanonicalFiberBitsAllowed 6 4 sigma left z
        (muNegFiveZeroThreeFiberBit
          (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X) left z) = true)
    (hbalance : ∀ x y a b c d,
      muNegFiveZeroThreeCrossIndex? ((x + 7) % 8) y = some a →
      muNegFiveZeroThreeCrossIndex? ((x + 1) % 8) y = some b →
      muNegFiveZeroThreeCrossIndex? x ((y + 1) % 8) = some c →
      muNegFiveZeroThreeCrossIndex? x ((y + 7) % 8) = some d →
      (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X a).toNat +
          (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X b).toNat =
        (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X c).toNat +
          (muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X d).toNat) : False :=
  muNegFiveOneTwoCrossOnlyOwnerRelations_false sigma active X hsymm hends
    hfiber hbalance
    (muNegFiveOneTwoCrossOnlyServiceClauses_satisfied
      active X hsem hsymm hirr hcompat)
    (muNegFiveOneTwoCrossOnlyC4Clauses_satisfied active X hsem hsymm)

end Erdos85

#print axioms Erdos85.muNegFiveOneTwoCrossOnlyHitActivityClauses_satisfied
#print axioms Erdos85.muNegFiveOneTwoCrossOnlyServiceExistsClauseSatisfied_of_relation
#print axioms Erdos85.muNegFiveOneTwoCrossOnlyServiceClauses_satisfied
#print axioms Erdos85.muNegFiveOneTwoCrossOnlyNoCommonClauseSatisfied_of_relation
#print axioms Erdos85.muNegFiveOneTwoCrossOnlyC4Clauses_satisfied
#print axioms Erdos85.muNegFiveOneTwoCrossOnlyOwnerRelations_false_of_serviceSemantics
#print axioms Erdos85.muNegFiveOneTwoCrossOnlyOwnerRelations_false
