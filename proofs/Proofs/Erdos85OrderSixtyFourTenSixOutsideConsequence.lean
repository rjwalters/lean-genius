import Proofs.Erdos85OrderSixtyFourTenSixOutsideEncoding

/-! # Semantic consequence of the six `[10,6]` outside-C formulas -/

namespace Erdos85

open Std Sat

theorem tenSixOutsideTarget_eq_one_of_adj_incidence
    (i : Fin 6) (C : SimpleGraph (Fin 48)) [DecidableRel C.Adj]
    (hs : OutsideCClauseSemantics C
      (fun u e ↦ tenSixIncidence i u e = true) (tenSixOutsideTarget i))
    (u : Fin 16) (e f : Fin 48) (hef : C.Adj e f)
    (huf : tenSixIncidence i u f = true) :
    tenSixOutsideTarget i u e = 1 := by
  have hle := tenSixOutsideTarget_le_one i u e
  by_contra hne
  have hz : tenSixOutsideTarget i u e = 0 := by omega
  exact hs.zero_service u e hz f hef huf

theorem tenSixOutsidePairs_mem_sorted (e f : Fin 48) (hef : e ≠ f) :
    (if e < f then (e, f) else (f, e)) ∈ tenSixOutsidePairs.toList := by
  native_decide +revert

/-- Every actual C-edge passes the generator's dominance filter.  This is
the key fact ensuring semantic service witnesses always have DIMACS IDs. -/
theorem tenSixOutsideAllowed_of_adj
    (i : Fin 6) (C : SimpleGraph (Fin 48)) [DecidableRel C.Adj]
    (hs : OutsideCClauseSemantics C
      (fun u e ↦ tenSixIncidence i u e = true) (tenSixOutsideTarget i))
    (e f : Fin 48) (hef : C.Adj e f) :
    let p := if e < f then (e, f) else (f, e)
    tenSixOutsideAllowed i p.1 p.2 = true := by
  have hne : e ≠ f := by
    intro h
    subst f
    exact C.loopless.irrefl e hef
  by_cases hlt : e < f
  · simp only [hlt, if_pos]
    unfold tenSixOutsideAllowed
    simp only [hlt, decide_true, Bool.true_and, List.all_eq_true,
      List.mem_finRange]
    intro u _hu
    rw [Bool.and_eq_true]
    constructor
    · by_cases huf : tenSixIncidence i u f = true
      · simp [huf, tenSixOutsideTarget_eq_one_of_adj_incidence
          i C hs u e f hef huf]
      · cases h : tenSixIncidence i u f <;> simp_all
    · by_cases hue : tenSixIncidence i u e = true
      · have hfe : C.Adj f e := hef.symm
        simp [hue, tenSixOutsideTarget_eq_one_of_adj_incidence
          i C hs u f e hfe hue]
      · cases h : tenSixIncidence i u e <;> simp_all
  · have hgt : f < e := _root_.lt_of_le_of_ne (_root_.not_lt.mp hlt) hne.symm
    simp only [hlt, if_false]
    unfold tenSixOutsideAllowed
    simp only [hgt, decide_true, Bool.true_and, List.all_eq_true,
      List.mem_finRange]
    intro u _hu
    rw [Bool.and_eq_true]
    constructor
    · by_cases hue : tenSixIncidence i u e = true
      · have hfe : C.Adj f e := hef.symm
        simp [hue, tenSixOutsideTarget_eq_one_of_adj_incidence
          i C hs u f e hfe hue]
      · cases h : tenSixIncidence i u e <;> simp_all
    · by_cases huf : tenSixIncidence i u f = true
      · simp [huf, tenSixOutsideTarget_eq_one_of_adj_incidence
          i C hs u e f hef huf]
      · cases h : tenSixIncidence i u f <;> simp_all

/-- Every actual C-edge has a concrete zero-based DIMACS identifier. -/
theorem exists_tenSixOutsideVar_of_adj
    (i : Fin 6) (C : SimpleGraph (Fin 48)) [DecidableRel C.Adj]
    (hs : OutsideCClauseSemantics C
      (fun u e ↦ tenSixIncidence i u e = true) (tenSixOutsideTarget i))
    (e f : Fin 48) (hef : C.Adj e f) :
    ∃ id, tenSixOutsideVar? i e f = some id := by
  let p := if e < f then (e, f) else (f, e)
  have hne : e ≠ f := by
    intro h
    subst f
    exact C.loopless.irrefl e hef
  have hpairs : p ∈ tenSixOutsidePairs.toList :=
    tenSixOutsidePairs_mem_sorted e f hne
  have hallowed : tenSixOutsideAllowed i p.1 p.2 = true :=
    tenSixOutsideAllowed_of_adj i C hs e f hef
  have hp : p ∈ (tenSixOutsideAllowedPairs i).toList := by
    have hpairsArray : p ∈ tenSixOutsidePairs := by simpa using hpairs
    have hpArray : p ∈ tenSixOutsideAllowedPairs i := by
      unfold tenSixOutsideAllowedPairs
      exact Array.mem_filter.mpr ⟨hpairsArray, hallowed⟩
    simpa using hpArray
  rw [tenSixOutsideVar?_eq_raw]
  unfold tenSixOutsideVarRaw?
  change ∃ id, (tenSixOutsideAllowedPairs i).toList.idxOf? p = some id
  cases hopt : (tenSixOutsideAllowedPairs i).toList.idxOf? p with
  | none =>
      exact False.elim ((List.idxOf?_eq_none_iff.mp hopt) hp)
  | some id => exact ⟨id, rfl⟩

/-- A semantic service neighbour occurs in the exact positive-clause term
list, with its certified variable identifier. -/
theorem exists_mem_tenSixOutsideServiceTerms_of_adj
    (i : Fin 6) (C : SimpleGraph (Fin 48)) [DecidableRel C.Adj]
    (hs : OutsideCClauseSemantics C
      (fun u e ↦ tenSixIncidence i u e = true) (tenSixOutsideTarget i))
    (u : Fin 16) (e f : Fin 48) (hef : C.Adj e f)
    (huf : tenSixIncidence i u f = true) :
    ∃ id, id ∈ tenSixOutsideServiceTerms i e u ∧
      tenSixOutsideVar? i e f = some id := by
  obtain ⟨id, hid⟩ := exists_tenSixOutsideVar_of_adj i C hs e f hef
  refine ⟨id, ?_, hid⟩
  simp only [tenSixOutsideServiceTerms, List.mem_filterMap]
  exact ⟨f, by simp, by simp [huf, hid]⟩

/-- Conversely, every service-term ID decodes to an incident candidate and
the graph-induced DIMACS valuation reads its actual C adjacency. -/
theorem tenSixOutsideServiceTerm_reifies
    (i : Fin 6) (C : SimpleGraph (Fin 48)) [DecidableRel C.Adj]
    (u : Fin 16) (e : Fin 48) {id : Nat}
    (hid : id ∈ tenSixOutsideServiceTerms i e u) :
    ∃ f : Fin 48, tenSixIncidence i u f = true ∧
      tenSixOutsideVar? i e f = some id ∧
      tenSixOutsideDimacsValuation i C id = decide (C.Adj e f) := by
  simp only [tenSixOutsideServiceTerms, List.mem_filterMap] at hid
  obtain ⟨f, _hf, hterm⟩ := hid
  split at hterm
  next huf =>
    cases hvar : tenSixOutsideVar? i e f <;> simp_all
    exact ⟨f, huf, hvar,
      tenSixOutsideDimacsValuation_var i C e f hvar⟩
  next huf => simp at hterm

end Erdos85
