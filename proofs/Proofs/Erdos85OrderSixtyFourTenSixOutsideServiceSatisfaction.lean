import Proofs.Erdos85OrderSixtyFourTenSixOutsideConsequence
import Proofs.Erdos85OrderSixtyFourTenSixOutsideListPairs

/-! # Satisfaction of the generated `[10,6]` service clauses -/

namespace Erdos85

open Std Sat

/-- Sorting an unordered pair with a fixed first input remains injective in
the other input. -/
private theorem sortedPair_right_injective (e f g : Fin 48)
    (h : (if e < f then (e, f) else (f, e)) =
      (if e < g then (e, g) else (g, e))) : f = g := by
  by_cases hef : e < f <;> by_cases heg : e < g
  · simpa [hef, heg] using congrArg Prod.snd h
  · simp [hef, heg] at h
    exact h.2.trans h.1
  · simp [hef, heg] at h
    exact h.1.trans h.2
  · simpa [hef, heg] using congrArg Prod.fst h

theorem tenSixOutsideVar?_injective_right
    (i : Fin 6) (e f g : Fin 48) {id : Nat}
    (hf : tenSixOutsideVar? i e f = some id)
    (hg : tenSixOutsideVar? i e g = some id) : f = g := by
  rw [tenSixOutsideVar?_eq_raw] at hf hg
  unfold tenSixOutsideVarRaw? at hf hg
  have hfget := (List.idxOf?_eq_some_iff.mp hf).choose_spec.1
  have hgget := (List.idxOf?_eq_some_iff.mp hg).choose_spec.1
  apply sortedPair_right_injective e f g
  exact hfget.symm.trans hgget

/-- The finite service-term lists contain no duplicate DIMACS identifiers. -/
theorem tenSixOutsideServiceTerms_nodup
    (i : Fin 6) (e : Fin 48) (u : Fin 16) :
    (tenSixOutsideServiceTerms i e u).Nodup := by
  unfold tenSixOutsideServiceTerms
  apply List.Nodup.filterMap
  · intro f g id hf hg
    by_cases hif : tenSixIncidence i u f = true
    · have hf' : tenSixOutsideVar? i e f = some id := by
        simpa [hif] using hf
      by_cases hig : tenSixIncidence i u g = true
      · have hg' : tenSixOutsideVar? i e g = some id := by
          simpa [hig] using hg
        exact tenSixOutsideVar?_injective_right i e f g hf' hg'
      · simp [hig] at hg
    · simp [hif] at hf
  · exact List.nodup_finRange 48

theorem tenSixOutside_zero_unit_eval
    (i : Fin 6) (C : SimpleGraph (Fin 48)) [DecidableRel C.Adj]
    (hs : OutsideCClauseSemantics C
      (fun u e ↦ tenSixIncidence i u e = true) (tenSixOutsideTarget i))
    (u : Fin 16) (e : Fin 48) {id : Nat}
    (ht : tenSixOutsideTarget i u e = 0)
    (hid : id ∈ tenSixOutsideServiceTerms i e u) :
    CNF.Clause.eval (tenSixOutsideDimacsValuation i C) [(id, false)] = true := by
  obtain ⟨f, huf, _hvar, hval⟩ :=
    tenSixOutsideServiceTerm_reifies i C u e hid
  have hnot : ¬C.Adj e f := by
    intro hef
    exact hs.zero_service u e ht f hef huf
  simp [CNF.Clause.eval, hval, hnot]

theorem tenSixOutside_positive_service_eval
    (i : Fin 6) (C : SimpleGraph (Fin 48)) [DecidableRel C.Adj]
    (hs : OutsideCClauseSemantics C
      (fun u e ↦ tenSixIncidence i u e = true) (tenSixOutsideTarget i))
    (u : Fin 16) (e : Fin 48)
    (ht : tenSixOutsideTarget i u e = 1) :
    CNF.Clause.eval (tenSixOutsideDimacsValuation i C)
      (positiveClause (tenSixOutsideServiceTerms i e u)) = true := by
  obtain ⟨f, hef, huf⟩ := hs.one_service_exists u e ht
  obtain ⟨id, hid, hvar⟩ :=
    exists_mem_tenSixOutsideServiceTerms_of_adj i C hs u e f hef huf
  rw [positiveClause_eval_eq_true_iff]
  refine ⟨id, hid, ?_⟩
  rw [tenSixOutsideDimacsValuation_var i C e f hvar]
  simp [hef]

theorem tenSixOutside_service_pair_eval
    (i : Fin 6) (C : SimpleGraph (Fin 48)) [DecidableRel C.Adj]
    (hs : OutsideCClauseSemantics C
      (fun u e ↦ tenSixIncidence i u e = true) (tenSixOutsideTarget i))
    (u : Fin 16) (e : Fin 48) (p : Nat × Nat)
    (ht : tenSixOutsideTarget i u e = 1)
    (hp : p ∈ listPairs (tenSixOutsideServiceTerms i e u)) :
    CNF.Clause.eval (tenSixOutsideDimacsValuation i C)
      [(p.1, false), (p.2, false)] = true := by
  have hpcomp := mem_listPairs_components hp
  have hpne := mem_listPairs_ne
    (tenSixOutsideServiceTerms_nodup i e u) hp
  obtain ⟨f, huf, hvarf, hvalf⟩ :=
    tenSixOutsideServiceTerm_reifies i C u e hpcomp.1
  obtain ⟨g, hug, hvarg, hvalg⟩ :=
    tenSixOutsideServiceTerm_reifies i C u e hpcomp.2
  have hfg : f ≠ g := by
    intro hfg
    subst g
    rw [hvarf] at hvarg
    exact hpne (Option.some.inj hvarg)
  by_cases hef : C.Adj e f
  · have hneg : ¬C.Adj e g := by
      intro heg
      exact hfg (hs.one_service_unique u e ht f g hef huf heg hug)
    simp [CNF.Clause.eval, hvalf, hvalg, hef, hneg]
  · simp [CNF.Clause.eval, hvalf, hef]

/-- Every clause generated at one `(outside vertex, inside vertex)` service
slot evaluates to true under the graph-induced valuation. -/
theorem tenSixOutside_serviceClauseAt_eval
    (i : Fin 6) (C : SimpleGraph (Fin 48)) [DecidableRel C.Adj]
    (hs : OutsideCClauseSemantics C
      (fun u e ↦ tenSixIncidence i u e = true) (tenSixOutsideTarget i))
    (e : Fin 48) (u : Fin 16) {clause : CNF.Clause Nat}
    (hclause : clause ∈ tenSixOutsideServiceClausesAt i e u) :
    CNF.Clause.eval (tenSixOutsideDimacsValuation i C) clause = true := by
  unfold tenSixOutsideServiceClausesAt at hclause
  by_cases hz : tenSixOutsideTarget i u e = 0
  · simp only [hz, if_pos, List.mem_map] at hclause
    obtain ⟨id, hid, rfl⟩ := hclause
    exact tenSixOutside_zero_unit_eval i C hs u e hz hid
  · have ho : tenSixOutsideTarget i u e = 1 := by
      have hle := tenSixOutsideTarget_le_one i u e
      omega
    simp only [hz, if_false, List.mem_append, List.mem_singleton,
      List.mem_map] at hclause
    rcases hclause with rfl | ⟨p, hp, rfl⟩
    · exact tenSixOutside_positive_service_eval i C hs u e ho
    · exact tenSixOutside_service_pair_eval i C hs u e p ho hp

/-- Every service clause in the generated outside CNF evaluates to true. -/
theorem tenSixOutside_serviceClause_eval
    (i : Fin 6) (C : SimpleGraph (Fin 48)) [DecidableRel C.Adj]
    (hs : OutsideCClauseSemantics C
      (fun u e ↦ tenSixIncidence i u e = true) (tenSixOutsideTarget i))
    {clause : CNF.Clause Nat}
    (hclause : clause ∈ tenSixOutsideServiceClauses i) :
    CNF.Clause.eval (tenSixOutsideDimacsValuation i C) clause = true := by
  simp only [tenSixOutsideServiceClauses, List.mem_flatMap,
    List.mem_finRange] at hclause
  obtain ⟨e, _he, u, _hu, hclause⟩ := hclause
  exact tenSixOutside_serviceClauseAt_eval i C hs e u hclause

end Erdos85
