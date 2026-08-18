import Proofs.Erdos85OrderSixtyFourOutsideCnfSemantics

/-! # Evaluating the elementary outside-C certificate clauses

This file connects the graph-level semantic package to the four concrete
clause shapes emitted by `emit_c_cnf`: zero-service units, positive service
clauses, pairwise at-most-one clauses, and four-negative C4 clauses.
-/

namespace Erdos85

open Std Sat

def positiveClause (ids : List Nat) : CNF.Clause Nat :=
  ids.map fun id ↦ (id, true)

theorem positiveClause_eval_eq_true_iff
    (val : Nat → Bool) (ids : List Nat) :
    CNF.Clause.eval val (positiveClause ids) = true ↔
      ∃ id ∈ ids, val id = true := by
  induction ids with
  | nil => simp [positiveClause, CNF.Clause.eval]
  | cons id ids ih =>
      simp only [positiveClause, List.map_cons, CNF.Clause.eval_cons,
        Bool.or_eq_true, beq_iff_eq]
      change val id = true ∨
        CNF.Clause.eval val (positiveClause ids) = true ↔ _
      rw [ih]
      simp only [List.mem_cons]
      aesop

/-- Reification of a numbered outside-edge variable by adjacency in `C`. -/
def OutsideEdgeValReifies
    {E : Type*} (C : SimpleGraph E) [DecidableRel C.Adj]
    (edgeId : E → E → Nat) (val : Nat → Bool) : Prop :=
  ∀ e f, val (edgeId e f) = decide (C.Adj e f)

/-- A target-zero service term produces the generator's negative unit. -/
theorem outside_zeroService_unit_eval
    {U E : Type*} [Fintype E]
    (C : SimpleGraph E) [DecidableRel C.Adj]
    (incident : U → E → Prop) (target : U → E → Nat)
    (hs : OutsideCClauseSemantics C incident target)
    (edgeId : E → E → Nat) (val : Nat → Bool)
    (hreify : OutsideEdgeValReifies C edgeId val)
    (u : U) (e f : E) (ht : target u e = 0) (huf : incident u f) :
    CNF.Clause.eval val [(edgeId e f, false)] = true := by
  have hnot : ¬C.Adj e f := by
    intro hef
    exact hs.zero_service u e ht f hef huf
  rw [CNF.Clause.eval_cons, CNF.Clause.eval_nil, hreify]
  simp [hnot]

/-- For target one, any candidate list containing all service neighbours
makes the generator's positive clause true. -/
theorem outside_oneService_positive_eval
    {U E : Type*} [Fintype E]
    (C : SimpleGraph E) [DecidableRel C.Adj]
    (incident : U → E → Prop) (target : U → E → Nat)
    (hs : OutsideCClauseSemantics C incident target)
    (edgeId : E → E → Nat) (val : Nat → Bool)
    (hreify : OutsideEdgeValReifies C edgeId val)
    (u : U) (e : E) (ids : List Nat) (ht : target u e = 1)
    (hcover : ∀ f, C.Adj e f → incident u f → edgeId e f ∈ ids) :
    CNF.Clause.eval val (positiveClause ids) = true := by
  obtain ⟨f, hef, huf⟩ := hs.one_service_exists u e ht
  rw [positiveClause_eval_eq_true_iff]
  refine ⟨edgeId e f, hcover f hef huf, ?_⟩
  rw [hreify]
  simp [hef]

/-- The pairwise at-most-one service clause is true. -/
theorem outside_oneService_pair_eval
    {U E : Type*} [Fintype E]
    (C : SimpleGraph E) [DecidableRel C.Adj]
    (incident : U → E → Prop) (target : U → E → Nat)
    (hs : OutsideCClauseSemantics C incident target)
    (edgeId : E → E → Nat) (val : Nat → Bool)
    (hreify : OutsideEdgeValReifies C edgeId val)
    (u : U) (e f g : E) (ht : target u e = 1)
    (huf : incident u f) (hug : incident u g) (hfg : f ≠ g) :
    CNF.Clause.eval val
      [(edgeId e f, false), (edgeId e g, false)] = true := by
  rw [CNF.Clause.eval_cons, CNF.Clause.eval_cons, CNF.Clause.eval_nil,
    hreify, hreify]
  by_cases hef : C.Adj e f
  · have hneg : ¬C.Adj e g := by
      intro heg
      exact hfg (hs.one_service_unique u e ht f g hef huf heg hug)
    simp [hef, hneg]
  · simp [hef]

/-- The four-negative clause forbidding two common outside neighbours is
true under the semantic C4 condition. -/
theorem outside_c4_clause_eval
    {U E : Type*} [Fintype E]
    (C : SimpleGraph E) [DecidableRel C.Adj]
    (incident : U → E → Prop) (target : U → E → Nat)
    (hs : OutsideCClauseSemantics C incident target)
    (edgeId : E → E → Nat) (val : Nat → Bool)
    (hreify : OutsideEdgeValReifies C edgeId val)
    (a b c d : E) (hab : a ≠ b) (hcd : c ≠ d) :
    CNF.Clause.eval val [(edgeId a c, false), (edgeId b c, false),
      (edgeId a d, false), (edgeId b d, false)] = true := by
  simp only [CNF.Clause.eval_cons, CNF.Clause.eval_nil]
  rw [hreify a c, hreify b c, hreify a d, hreify b d]
  by_cases hac : C.Adj a c <;> by_cases hbc : C.Adj b c <;>
    by_cases had : C.Adj a d <;> by_cases hbd : C.Adj b d
  all_goals simp_all
  exact False.elim (hs.no_two_common a b c d hab hcd hac hbc had hbd)

end Erdos85
