import Proofs.Erdos85OrderSixtyFourTenSixOutsideConsequence
import Proofs.Erdos85OrderSixtyFourTenSixOutsideListPairs

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

theorem tenSixOutsideCommonTerms_nodup :
    ∀ (i : Fin 6) (a b : Fin 48),
      (tenSixOutsideCommonTerms i a b).Nodup := by
  native_decide

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
    exact Prod.ext (Option.some.inj had.symm) (Option.some.inj hbd.symm)
  rw [CNF.Clause.eval_cons, CNF.Clause.eval_cons,
    CNF.Clause.eval_cons, CNF.Clause.eval_cons, CNF.Clause.eval_nil,
    hvalaC, hvalbC, hvalaD, hvalbD]
  by_cases hac' : C.Adj a c <;> by_cases hbc' : C.Adj b c <;>
    by_cases had' : C.Adj a d <;> by_cases hbd' : C.Adj b d
  all_goals simp_all
  exact False.elim (hs.no_two_common a b c d hab hcd hac' hbc' had' hbd')

end Erdos85
