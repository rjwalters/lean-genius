import Proofs.Erdos85OrderSixtyFourOutsideEdgeBijection

/-! # Semantic core of the order-64 outside-block CNFs

The certificate generator represents every possible outside edge by one
Boolean variable.  Its service clauses say that, for each outside vertex
`e` and inside vertex `u`, exactly `target u e` neighbours of `e` are
incident with `u`; its remaining clauses forbid two common neighbours.

This file packages those two graph statements in the clause-level form used
by the generator.  It deliberately does not depend on a particular DIMACS
numbering, so the forthcoming finite label-transport layer can reuse it for
all certified exterior-pair graphs.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The outside neighbours of `e` whose incidence pair contains `u`. -/
def outsideServiceFinset
    {U E : Type*} [Fintype E] [DecidableEq E]
    (C : SimpleGraph E) [DecidableRel C.Adj]
    (incident : U → E → Prop) [DecidableRel incident]
    (u : U) (e : E) : Finset E :=
  Finset.univ.filter fun f ↦ C.Adj e f ∧ incident u f

/-- Clause-level consequences needed by the elementary outside-C encoder. -/
structure OutsideCClauseSemantics
    {U E : Type*} [Fintype E]
    (C : SimpleGraph E) (incident : U → E → Prop)
    (target : U → E → Nat) : Prop where
  zero_service : ∀ u e, target u e = 0 →
    ∀ f, C.Adj e f → incident u f → False
  one_service_exists : ∀ u e, target u e = 1 →
    ∃ f, C.Adj e f ∧ incident u f
  one_service_unique : ∀ u e, target u e = 1 →
    ∀ f g, C.Adj e f → incident u f →
      C.Adj e g → incident u g → f = g
  no_two_common : ∀ a b c d, a ≠ b → c ≠ d →
    C.Adj a c → C.Adj b c → C.Adj a d → C.Adj b d → False

/-- Exact service counts and C4-freeness imply every semantic condition
represented by the outside-C CNF clauses. -/
theorem outsideCClauseSemantics_of_exact_service
    {U E : Type*} [Fintype E] [DecidableEq E]
    (C : SimpleGraph E) [DecidableRel C.Adj]
    (incident : U → E → Prop) [DecidableRel incident]
    (target : U → E → Nat)
    (hservice : ∀ u e,
      (outsideServiceFinset C incident u e).card = target u e)
    (hfree : ¬ containsC4 E C) :
    OutsideCClauseSemantics C incident target := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u e ht f hef huf
    have hmem : f ∈ outsideServiceFinset C incident u e := by
      simp [outsideServiceFinset, hef, huf]
    have hcard : (outsideServiceFinset C incident u e).card = 0 := by
      simpa [ht] using hservice u e
    have hempty := Finset.card_eq_zero.mp hcard
    rw [hempty] at hmem
    simp at hmem
  · intro u e ht
    have hcard : (outsideServiceFinset C incident u e).card = 1 := by
      simpa [ht] using hservice u e
    obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hcard
    refine ⟨f, ?_⟩
    have : f ∈ outsideServiceFinset C incident u e := by simp [hf]
    simpa [outsideServiceFinset] using this
  · intro u e ht f g hef huf heg hug
    have hcard : (outsideServiceFinset C incident u e).card = 1 := by
      simpa [ht] using hservice u e
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard
    have hf : f ∈ outsideServiceFinset C incident u e := by
      simp [outsideServiceFinset, hef, huf]
    have hg : g ∈ outsideServiceFinset C incident u e := by
      simp [outsideServiceFinset, heg, hug]
    simpa [hw] using (show f = w from by simpa [hw] using hf).trans
      (show g = w from by simpa [hw] using hg).symm
  · intro a b c d hab hcd hac hbc had hbd
    apply hfree
    refine ⟨![a, c, b, d], ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [C4, SimpleGraph.Adj.symm]

end

end Erdos85
