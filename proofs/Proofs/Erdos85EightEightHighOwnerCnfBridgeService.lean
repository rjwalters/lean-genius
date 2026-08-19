import Proofs.Erdos85EightEightHighOwnerCnfBridge

/-!
# Guarded service and C4 semantics for the high eight-plus-eight CNF

This file is deliberately independent of the graph-coordinate adapter.  It
turns clean finite relation laws for candidate owners into the guarded
service and common-neighbor DIMACS clause fields.
-/

namespace Erdos85

open Std Sat

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- A fixed same-shore owner is always enabled; a variable cross owner is
enabled precisely when its activity predicate holds. -/
def eightEightHighOwnerEnabled (active : Fin 64 → Prop) (e : Fin 64) : Prop :=
  match eightEightHighActiveVariable? e with
  | some _ => active e
  | none => True

/-- Clean relation-level laws needed by the guarded service and C4 clause
families. -/
structure EightEightHighOwnerServiceSemantics
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop) : Prop where
  service_exists : ∀ (e : Fin 64) (v : Fin 16),
    eightEightHighOwnerEnabled active e →
    eightEightHighOwnerTargetContains e v = true →
      ∃ f, X e f ∧ eightEightHighOwnerContains f v = true
  service_unique : ∀ (e : Fin 64) (v : Fin 16) (f g : Fin 64),
    X e f → eightEightHighOwnerContains f v = true →
    X e g → eightEightHighOwnerContains g v = true → f = g
  internal_zero : ∀ (e : Fin 64) (v : Fin 16) (f : Fin 64),
    eightEightHighOwnerTargetContains e v = false →
    eightEightHighOwnerContains f v = true → ¬ X e f
  intersecting_no_common : ∀ (e f : Fin 64),
    e ≠ f → eightEightHighOwnersIntersect e f = true →
      ∀ k, X e k → X f k → False
  no_two_common : ∀ (e f : Fin 64),
    e ≠ f → ∀ (k l : Fin 64), k ≠ l →
      X e k → X f k → X e l → X f l → False

theorem mem_eightEightHighServiceVariables_iff
    (e : Fin 64) (v : Fin 16) (lit : Int) :
    lit ∈ eightEightHighServiceVariables e v ↔
      ∃ f : Fin 64, f ≠ e ∧ eightEightHighOwnerContains f v = true ∧
        eightEightHighHitLiteral? e f = some lit := by
  simp only [eightEightHighServiceVariables, List.mem_filterMap,
    List.mem_range]
  constructor
  · rintro ⟨f, hf64, hflit⟩
    split at hflit
    · next hcond =>
      have hc : f ≠ e.val ∧ eightEightHighOwnerContains f v = true := by
        simpa using hcond
      refine ⟨⟨f, hf64⟩, ?_, ?_, ?_⟩
      · intro h
        exact hc.1 (congrArg Fin.val h)
      · simpa using hc.2
      · simpa using hflit
    · simp at hflit
  · rintro ⟨f, hfe, hcontains, hlit⟩
    refine ⟨f, f.2, ?_⟩
    rw [if_pos]
    · exact hlit
    · have hne : f.val ≠ e.val := fun h ↦ hfe (Fin.ext h)
      simp [hne, hcontains]

theorem eightEightHighHitVariable?_positive
    {e f : Fin 64} {id : Nat}
    (hvar : eightEightHighHitVariable? e f = some id) : 0 < id := by
  exact Nat.lt_trans (by omega : 0 < 32)
    (eightEightHighHitVariable?_above_active hvar)

theorem eightEightHighHitLiteral?_eq_some
    {e f : Fin 64} {lit : Int}
    (hlit : eightEightHighHitLiteral? e f = some lit) :
    ∃ id : Nat, eightEightHighHitVariable? e f = some id ∧
      lit = Int.ofNat id := by
  unfold eightEightHighHitLiteral? at hlit
  cases hvar : eightEightHighHitVariable? e f with
  | none => simp [hvar] at hlit
  | some id =>
      simp [hvar] at hlit
      exact ⟨id, rfl, hlit.symm⟩

theorem eightEightHighHitVariable?_exists
    (e f : Fin 64) (hef : e ≠ f)
    (hcompat : eightEightHighOwnerCompatible e f = true) :
    ∃ id, eightEightHighHitVariable? e f = some id := by
  have hs : (eightEightHighHitVariable? e f).isSome = true := by
    revert e f
    native_decide
  cases hvar : eightEightHighHitVariable? e f with
  | none => simp [hvar] at hs
  | some id => exact ⟨id, rfl⟩

theorem eightEightHighActiveGuard_satisfied_of_not_enabled
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    (e : Fin 64) (hdisabled : ¬ eightEightHighOwnerEnabled active e) :
    dimacsClauseSatisfied (eightEightHighOwnerValOfRelations active X)
      (eightEightHighActiveGuard e) := by
  unfold eightEightHighOwnerEnabled at hdisabled
  unfold eightEightHighActiveGuard
  cases hvar : eightEightHighActiveVariable? e with
  | none => simp [hvar] at hdisabled
  | some id =>
      have hnotactive : ¬ active e := by simpa [hvar] using hdisabled
      have hidpos := (eightEightHighActiveVariable?_bounds hvar).1
      have hvalfalse : eightEightHighOwnerValOfRelations active X id = false := by
        apply Bool.eq_false_of_not_eq_true
        intro hval
        exact hnotactive
          (eightEightHighOwnerActive_of_val_true active X hvar hval)
      refine ⟨-Int.ofNat id, by simp [hvar], ?_⟩
      simp [dimacsLitValue, hidpos, hvalfalse]

/-- A guarded positive service clause is satisfied either by its false
activity guard or by the actual unique-service relation edge. -/
theorem eightEightHighServiceExistsClauseSatisfied_of_relation
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsem : EightEightHighOwnerServiceSemantics active X)
    (hirr : ∀ e, ¬ X e e)
    (hcompat : ∀ e f, X e f → eightEightHighOwnerCompatible e f = true)
    (e v : Nat) (he : e < 64) (hv : v < 16)
    (htarget : eightEightHighOwnerTargetContains e v = true) :
    dimacsClauseSatisfied (eightEightHighOwnerValOfRelations active X)
      (eightEightHighActiveGuard e ++ eightEightHighServiceVariables e v) := by
  let ef : Fin 64 := ⟨e, he⟩
  let vf : Fin 16 := ⟨v, hv⟩
  by_cases henabled : eightEightHighOwnerEnabled active ef
  · obtain ⟨f, hX, hcontains⟩ :=
      hsem.service_exists ef vf henabled (by simpa using htarget)
    have hfe : f ≠ ef := by
      intro h
      subst f
      exact hirr ef hX
    obtain ⟨id, hvar⟩ :=
      eightEightHighHitVariable?_exists ef f hfe.symm (hcompat ef f hX)
    have hlit : eightEightHighHitLiteral? ef f = some (Int.ofNat id) := by
      simp [eightEightHighHitLiteral?, hvar]
    have hmem : Int.ofNat id ∈ eightEightHighServiceVariables e v :=
      (mem_eightEightHighServiceVariables_iff ef vf (Int.ofNat id)).mpr
        ⟨f, hfe, hcontains, hlit⟩
    refine ⟨Int.ofNat id, List.mem_append.mpr (Or.inr hmem), ?_⟩
    have hval := eightEightHighOwnerVal_hit_true_of active X hvar hX
    have hid := eightEightHighHitVariable?_positive hvar
    simp [dimacsLitValue, hid, hval]
  · obtain ⟨lit, hmem, hsat⟩ :=
      eightEightHighActiveGuard_satisfied_of_not_enabled active X ef henabled
    exact ⟨lit, List.mem_append.mpr (Or.inl hmem), hsat⟩

theorem eightEightHighServiceUniqueClauseSatisfied_of_relation
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsem : EightEightHighOwnerServiceSemantics active X)
    (hsymm : ∀ e f, X e f → X f e)
    (e v : Nat) (he : e < 64) (hv : v < 16)
    (_htarget : eightEightHighOwnerTargetContains e v = true)
    (clause : DimacsClause)
    (hclause : clause ∈ eightEightPairwiseNegativeClauses
      (eightEightHighServiceVariables e v)) :
    dimacsClauseSatisfied (eightEightHighOwnerValOfRelations active X) clause := by
  simp only [eightEightPairwiseNegativeClauses, List.mem_flatMap,
    List.mem_map, List.mem_filter] at hclause
  obtain ⟨x, hxrow, y, ⟨hyrow, hxy⟩, rfl⟩ := hclause
  let ef : Fin 64 := ⟨e, he⟩
  let vf : Fin 16 := ⟨v, hv⟩
  obtain ⟨f, _hfe, hfcontains, hfx⟩ :=
    (mem_eightEightHighServiceVariables_iff ef vf x).mp hxrow
  obtain ⟨g, _hge, hgcontains, hgy⟩ :=
    (mem_eightEightHighServiceVariables_iff ef vf y).mp hyrow
  obtain ⟨ix, hvarx, rfl⟩ := eightEightHighHitLiteral?_eq_some hfx
  obtain ⟨iy, hvary, rfl⟩ := eightEightHighHitLiteral?_eq_some hgy
  have hix := eightEightHighHitVariable?_positive hvarx
  have hiy := eightEightHighHitVariable?_positive hvary
  by_cases hxval : eightEightHighOwnerValOfRelations active X ix = true
  · have hXf := eightEightHighOwnerRelation_of_val_true
      active X hsymm hvarx hxval
    have hyfalse : eightEightHighOwnerValOfRelations active X iy = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hyval
      have hXg := eightEightHighOwnerRelation_of_val_true
        active X hsymm hvary hyval
      have hfg := hsem.service_unique ef vf f g hXf hfcontains hXg hgcontains
      subst g
      have : ix = iy := by simpa [hvarx] using hvary
      subst iy
      simp at hxy
    refine ⟨-Int.ofNat iy, by simp, ?_⟩
    simp [dimacsLitValue, hiy, hyfalse]
  · have hxf : eightEightHighOwnerValOfRelations active X ix = false :=
      Bool.eq_false_of_not_eq_true hxval
    refine ⟨-Int.ofNat ix, by simp, ?_⟩
    simp [dimacsLitValue, hix, hxf]

theorem eightEightHighInternalZeroClauseSatisfied_of_relation
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsem : EightEightHighOwnerServiceSemantics active X)
    (hsymm : ∀ e f, X e f → X f e)
    (e v : Nat) (he : e < 64) (hv : v < 16)
    (htarget : eightEightHighOwnerTargetContains e v = false)
    (x : Int) (hx : x ∈ eightEightHighServiceVariables e v) :
    dimacsClauseSatisfied (eightEightHighOwnerValOfRelations active X)
      (eightEightHighActiveGuard e ++ [-x]) := by
  let ef : Fin 64 := ⟨e, he⟩
  let vf : Fin 16 := ⟨v, hv⟩
  by_cases henabled : eightEightHighOwnerEnabled active ef
  · obtain ⟨f, _hfe, hfcontains, hfx⟩ :=
      (mem_eightEightHighServiceVariables_iff ef vf x).mp hx
    obtain ⟨id, hvar, rfl⟩ := eightEightHighHitLiteral?_eq_some hfx
    have hid := eightEightHighHitVariable?_positive hvar
    have hvalfalse : eightEightHighOwnerValOfRelations active X id = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hval
      have hX := eightEightHighOwnerRelation_of_val_true
        active X hsymm hvar hval
      exact hsem.internal_zero ef vf f (by simpa using htarget) hfcontains hX
    refine ⟨-Int.ofNat id, List.mem_append.mpr (Or.inr (by simp)), ?_⟩
    simp [dimacsLitValue, hid, hvalfalse]
  · obtain ⟨lit, hmem, hsat⟩ :=
      eightEightHighActiveGuard_satisfied_of_not_enabled active X ef henabled
    exact ⟨lit, List.mem_append.mpr (Or.inl hmem), hsat⟩

theorem eightEightHighNoCommonClauseSatisfied_of_relation
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsem : EightEightHighOwnerServiceSemantics active X)
    (hsymm : ∀ e f, X e f → X f e)
    (e f : Nat) (hef : e < f) (hf64 : f < 64)
    (hintersect : eightEightHighOwnersIntersect e f = true)
    (clause : DimacsClause)
    (hclause : clause ∈ eightEightHighNoCommonClauses e f) :
    dimacsClauseSatisfied (eightEightHighOwnerValOfRelations active X) clause := by
  simp only [eightEightHighNoCommonClauses, List.mem_filterMap] at hclause
  obtain ⟨k, hkcand, hclause⟩ := hclause
  simp only [eightEightHighCommonCandidates, List.mem_filter,
    List.mem_range] at hkcand
  have hk64 := hkcand.1
  cases hxe : eightEightHighHitLiteral? e k with
  | none => simp [hxe] at hclause
  | some x =>
    cases hyf : eightEightHighHitLiteral? f k with
    | none => simp [hxe, hyf] at hclause
    | some y =>
      simp [hxe, hyf] at hclause
      subst clause
      let ef : Fin 64 := ⟨e, by omega⟩
      let ff : Fin 64 := ⟨f, hf64⟩
      let kf : Fin 64 := ⟨k, hk64⟩
      have hxe' : eightEightHighHitLiteral? ef kf = some x := by
        simpa [ef, kf] using hxe
      have hyf' : eightEightHighHitLiteral? ff kf = some y := by
        simpa [ff, kf] using hyf
      obtain ⟨ix, hvarx, rfl⟩ := eightEightHighHitLiteral?_eq_some hxe'
      obtain ⟨iy, hvary, rfl⟩ := eightEightHighHitLiteral?_eq_some hyf'
      by_cases hxval : eightEightHighOwnerValOfRelations active X ix = true
      · have hXek := eightEightHighOwnerRelation_of_val_true
          active X hsymm hvarx hxval
        have hyfalse : eightEightHighOwnerValOfRelations active X iy = false := by
          apply Bool.eq_false_of_not_eq_true
          intro hyval
          have hXfk := eightEightHighOwnerRelation_of_val_true
            active X hsymm hvary hyval
          exact hsem.intersecting_no_common ef ff (by
            intro h
            have := congrArg Fin.val h
            dsimp [ef, ff] at this
            omega) (by simpa using hintersect) kf hXek hXfk
        refine ⟨-Int.ofNat iy, by simp, ?_⟩
        simp [dimacsLitValue, hyfalse]
      · have hxf : eightEightHighOwnerValOfRelations active X ix = false :=
          Bool.eq_false_of_not_eq_true hxval
        refine ⟨-Int.ofNat ix, by simp, ?_⟩
        simp [dimacsLitValue, hxf]

theorem eightEightHighAtMostOneCommonClauseSatisfied_of_relation
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsem : EightEightHighOwnerServiceSemantics active X)
    (hsymm : ∀ e f, X e f → X f e)
    (e f : Nat) (hef : e < f) (hf64 : f < 64)
    (clause : DimacsClause)
    (hclause : clause ∈ eightEightHighAtMostOneCommonClauses e f) :
    dimacsClauseSatisfied (eightEightHighOwnerValOfRelations active X) clause := by
  simp only [eightEightHighAtMostOneCommonClauses, List.mem_flatMap,
    List.mem_filterMap, List.mem_filter] at hclause
  obtain ⟨k, hkcand, l, ⟨hlcand, hkl⟩, hclause⟩ := hclause
  have hk64 : k < 64 := by
    have hkdata := hkcand
    simp only [eightEightHighCommonCandidates, List.mem_filter,
      List.mem_range] at hkdata
    exact hkdata.1
  have hl64 : l < 64 := by
    have hldata := hlcand
    simp only [eightEightHighCommonCandidates, List.mem_filter,
      List.mem_range] at hldata
    exact hldata.1
  have hklNat : k < l := by simpa using hkl
  cases hxek : eightEightHighHitLiteral? e k with
  | none => simp [hxek] at hclause
  | some xek =>
    cases hxfk : eightEightHighHitLiteral? f k with
    | none => simp [hxek, hxfk] at hclause
    | some xfk =>
      cases hxel : eightEightHighHitLiteral? e l with
      | none => simp [hxek, hxfk, hxel] at hclause
      | some xel =>
        cases hxfl : eightEightHighHitLiteral? f l with
        | none => simp [hxek, hxfk, hxel, hxfl] at hclause
        | some xfl =>
          simp [hxek, hxfk, hxel, hxfl] at hclause
          subst clause
          let ef : Fin 64 := ⟨e, by omega⟩
          let ff : Fin 64 := ⟨f, hf64⟩
          let kf : Fin 64 := ⟨k, hk64⟩
          let lf : Fin 64 := ⟨l, hl64⟩
          have hxek' : eightEightHighHitLiteral? ef kf = some xek := by
            simpa [ef, kf] using hxek
          have hxfk' : eightEightHighHitLiteral? ff kf = some xfk := by
            simpa [ff, kf] using hxfk
          have hxel' : eightEightHighHitLiteral? ef lf = some xel := by
            simpa [ef, lf] using hxel
          have hxfl' : eightEightHighHitLiteral? ff lf = some xfl := by
            simpa [ff, lf] using hxfl
          obtain ⟨iek, hvek, rfl⟩ := eightEightHighHitLiteral?_eq_some hxek'
          obtain ⟨ifk, hvfk, rfl⟩ := eightEightHighHitLiteral?_eq_some hxfk'
          obtain ⟨iel, hvel, rfl⟩ := eightEightHighHitLiteral?_eq_some hxel'
          obtain ⟨ifl, hvfl, rfl⟩ := eightEightHighHitLiteral?_eq_some hxfl'
          by_cases hekval : eightEightHighOwnerValOfRelations active X iek = true
          · by_cases hfkval : eightEightHighOwnerValOfRelations active X ifk = true
            · by_cases helval : eightEightHighOwnerValOfRelations active X iel = true
              · have hflfalse :
                    eightEightHighOwnerValOfRelations active X ifl = false := by
                  apply Bool.eq_false_of_not_eq_true
                  intro hflval
                  have hXek := eightEightHighOwnerRelation_of_val_true
                    active X hsymm hvek hekval
                  have hXfk := eightEightHighOwnerRelation_of_val_true
                    active X hsymm hvfk hfkval
                  have hXel := eightEightHighOwnerRelation_of_val_true
                    active X hsymm hvel helval
                  have hXfl := eightEightHighOwnerRelation_of_val_true
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

/-- Assemble the five guarded service/C4 fields with independently proved
cross-degree, intertwining, and hit-activity fields. -/
theorem EightEightHighOwnerServiceSemantics.to_constraintSemantics
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsem : EightEightHighOwnerServiceSemantics active X)
    (hsymm : ∀ e f, X e f → X f e)
    (hirr : ∀ e, ¬ X e e)
    (hcompat : ∀ e f, X e f → eightEightHighOwnerCompatible e f = true)
    (hcross : ∀ clause, clause ∈ eightEightHighCrossDegreeClauses →
      dimacsClauseSatisfied (eightEightHighOwnerValOfRelations active X) clause)
    (hinter : ∀ clause, clause ∈ eightEightHighIntertwiningClauses →
      dimacsClauseSatisfied (eightEightHighOwnerValOfRelations active X) clause)
    (hhit : ∀ clause, clause ∈ eightEightHighHitActivityClauses →
      dimacsClauseSatisfied (eightEightHighOwnerValOfRelations active X) clause) :
    EightEightHighOwnerConstraintSemantics
      (eightEightHighOwnerValOfRelations active X) := by
  refine ⟨hcross, hinter, hhit, ?_, ?_, ?_, ?_, ?_⟩
  · exact eightEightHighServiceExistsClauseSatisfied_of_relation
      active X hsem hirr hcompat
  · intro e v clause he hv ht hc
    exact eightEightHighServiceUniqueClauseSatisfied_of_relation
      active X hsem hsymm e v he hv ht clause hc
  · intro e v x he hv ht hx
    exact eightEightHighInternalZeroClauseSatisfied_of_relation
      active X hsem hsymm e v he hv ht x hx
  · intro e f clause hef hf hintersect hclause
    exact eightEightHighNoCommonClauseSatisfied_of_relation
      active X hsem hsymm e f hef hf hintersect clause hclause
  · intro e f clause hef hf _hdisjoint hclause
    exact eightEightHighAtMostOneCommonClauseSatisfied_of_relation
      active X hsem hsymm e f hef hf clause hclause

end Erdos85

#print axioms Erdos85.eightEightHighServiceExistsClauseSatisfied_of_relation
#print axioms Erdos85.eightEightHighServiceUniqueClauseSatisfied_of_relation
#print axioms Erdos85.eightEightHighInternalZeroClauseSatisfied_of_relation
#print axioms Erdos85.eightEightHighNoCommonClauseSatisfied_of_relation
#print axioms Erdos85.eightEightHighAtMostOneCommonClauseSatisfied_of_relation
#print axioms Erdos85.EightEightHighOwnerServiceSemantics.to_constraintSemantics
