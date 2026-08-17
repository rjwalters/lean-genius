import Proofs.Erdos85OrderSixtyFourTenSixOutsideServiceSatisfaction

/-! # Satisfaction of the generated `[10,6]` C4 clauses -/

namespace Erdos85

open Std Sat

/-- Decode one common-neighbour term into its outside witness and two
reified adjacency variables. -/
theorem tenSixOutsideCommonTerm_reifies
    (i : Fin 6) (C : SimpleGraph (Fin 48)) [DecidableRel C.Adj]
    (a b : Fin 48) {term : Nat × Nat}
    (hterm : term ∈ tenSixOutsideCommonTerms i a b) :
    ∃ c : Fin 48, c ≠ a ∧ c ≠ b ∧
      tenSixOutsideVar? i a c = some term.1 ∧
      tenSixOutsideVar? i b c = some term.2 ∧
      tenSixOutsideDimacsValuation i C term.1 = decide (C.Adj a c) ∧
      tenSixOutsideDimacsValuation i C term.2 = decide (C.Adj b c) := by
  simp only [tenSixOutsideCommonTerms, List.mem_filterMap] at hterm
  obtain ⟨c, _hc, hout⟩ := hterm
  split at hout
  next hskip => simp at hout
  next hkeep =>
    cases hac : tenSixOutsideVar? i a c <;>
      cases hbc : tenSixOutsideVar? i b c <;> simp_all
    rename_i ac bc
    have htermEq : term = (ac, bc) := by
      symm
      simpa [hac, hbc] using hout
    subst term
    have hca : c ≠ a := by
      intro h
      subst c
      simp at hkeep
    have hcb : c ≠ b := by
      intro h
      subst c
      simp at hkeep
    exact ⟨c, hca, hcb, hac, hbc,
      tenSixOutsideDimacsValuation_var i C a c hac,
      tenSixOutsideDimacsValuation_var i C b c hbc⟩

theorem tenSixOutsideCommonTerms_nodup
    (i : Fin 6) (a b : Fin 48) :
    (tenSixOutsideCommonTerms i a b).Nodup := by
  unfold tenSixOutsideCommonTerms
  apply List.Nodup.filterMap
  · intro c d term hc hd
    by_cases hcskip : c = a ∨ c = b
    · simp [hcskip] at hc
    · have hcskip' : (decide (c = a) || decide (c = b)) = false := by
        cases hca : decide (c = a) <;> cases hcb : decide (c = b) <;>
          simp_all
      by_cases hdskip : d = a ∨ d = b
      · simp [hdskip] at hd
      · have hdskip' : (decide (d = a) || decide (d = b)) = false := by
          cases hda : decide (d = a) <;> cases hdb : decide (d = b) <;>
            simp_all
        cases hac : tenSixOutsideVar? i a c <;>
          cases hbc : tenSixOutsideVar? i b c <;>
          simp [hcskip', hac, hbc] at hc
        rename_i ac bc
        cases had : tenSixOutsideVar? i a d <;>
          cases hbd : tenSixOutsideVar? i b d <;>
          simp [hdskip', had, hbd] at hd
        rename_i ad bd
        have hcEq : term = (ac, bc) := by
          symm
          simpa [hcskip', hac, hbc] using hc
        have hdEq : term = (ad, bd) := by
          symm
          simpa [hdskip', had, hbd] using hd
        have hacad : ac = ad := by
          have := congrArg Prod.fst (hcEq.symm.trans hdEq)
          simpa using this
        subst ad
        exact tenSixOutsideVar?_injective_right i a c d hac had
  · exact List.nodup_finRange 48

/-- Every four-negative clause emitted for fixed `a<b` is satisfied. -/
theorem tenSixOutsideC4ClausesAt_eval
    (i : Fin 6) (C : SimpleGraph (Fin 48)) [DecidableRel C.Adj]
    (hs : OutsideCClauseSemantics C
      (fun u e ↦ tenSixIncidence i u e = true) (tenSixOutsideTarget i))
    (a b : Fin 48) (hab : a ≠ b) {clause : CNF.Clause Nat}
    (hclause : clause ∈ tenSixOutsideC4ClausesAt i a b) :
    CNF.Clause.eval (tenSixOutsideDimacsValuation i C) clause = true := by
  unfold tenSixOutsideC4ClausesAt at hclause
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hclause
  obtain ⟨hp₁, hp₂⟩ := mem_listPairs_components hp
  have hpne : p.1 ≠ p.2 :=
    mem_listPairs_ne (tenSixOutsideCommonTerms_nodup i a b) hp
  obtain ⟨c, _hca, _hcb, hac, hbc, hvalaC, hvalbC⟩ :=
    tenSixOutsideCommonTerm_reifies i C a b hp₁
  obtain ⟨d, _hda, _hdb, had, hbd, hvalaD, hvalbD⟩ :=
    tenSixOutsideCommonTerm_reifies i C a b hp₂
  have hcd : c ≠ d := by
    intro h
    subst d
    rw [hac] at had
    rw [hbc] at hbd
    apply hpne
    exact Prod.ext (Option.some.inj had) (Option.some.inj hbd)
  rw [CNF.Clause.eval_cons, CNF.Clause.eval_cons,
    CNF.Clause.eval_cons, CNF.Clause.eval_cons, CNF.Clause.eval_nil,
    hvalaC, hvalbC, hvalaD, hvalbD]
  by_cases hac' : C.Adj a c <;> by_cases hbc' : C.Adj b c <;>
    by_cases had' : C.Adj a d <;> by_cases hbd' : C.Adj b d
  all_goals simp_all
  exact False.elim (hs.no_two_common a b c d hab hcd hac' hbc' had' hbd')

theorem mem_tenSixOutsidePairs_lt {p : Fin 48 × Fin 48}
    (hp : p ∈ tenSixOutsidePairs.toList) : p.1 < p.2 := by
  simpa [tenSixOutsidePairs] using hp

/-- Every generated four-negative C4 clause evaluates to true. -/
theorem tenSixOutsideC4Clause_eval
    (i : Fin 6) (C : SimpleGraph (Fin 48)) [DecidableRel C.Adj]
    (hs : OutsideCClauseSemantics C
      (fun u e ↦ tenSixIncidence i u e = true) (tenSixOutsideTarget i))
    {clause : CNF.Clause Nat}
    (hclause : clause ∈ tenSixOutsideC4Clauses i) :
    CNF.Clause.eval (tenSixOutsideDimacsValuation i C) clause = true := by
  simp only [tenSixOutsideC4Clauses, List.mem_flatMap] at hclause
  obtain ⟨p, hp, hclause⟩ := hclause
  have hab : p.1 ≠ p.2 := ne_of_lt (mem_tenSixOutsidePairs_lt hp)
  exact tenSixOutsideC4ClausesAt_eval i C hs p.1 p.2 hab hclause

end Erdos85
