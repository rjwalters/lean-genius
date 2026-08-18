import Proofs.Erdos85OrderSixtyFourOutsideEdgeBijection
import Proofs.Erdos85OutsideCommonNeighborRouting

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

/-- The abstract service finset is exactly the outside half of the common-
neighbour partition used by the graph-facing routing theorem. -/
theorem outsideServiceFinset_induce_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : Set V) [DecidablePred (· ∈ c)]
    (u : c) (z : {x : V // x ∉ c}) :
    (outsideServiceFinset (G.induce cᶜ)
      (fun u' y ↦ G.Adj u'.1 y.1) u z).card =
      ((G.neighborFinset u.1 ∩ G.neighborFinset z.1).filter
        fun y ↦ y ∉ c).card := by
  classical
  apply Finset.card_bij (fun y _ ↦ y.1)
  · intro y hy
    simp only [outsideServiceFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] at hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset _ _).mpr hy.2,
      (G.mem_neighborFinset _ _).mpr hy.1⟩, y.2⟩
  · intro y _ w _ hyw
    exact Subtype.ext hyw
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    refine ⟨⟨y, hy'.2⟩, ?_, rfl⟩
    have hadj := Finset.mem_inter.mp hy'.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨
      (G.mem_neighborFinset _ _).mp hadj.2,
      (G.mem_neighborFinset _ _).mp hadj.1⟩⟩

/-- Pointwise graph routing gives the exact `inside + outside = 1` service
count consumed by the certificate target `1 - H B`. -/
theorem card_insideCommon_add_outsideService_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (u : c.supp) (z : {x : V // x ∉ c.supp}) :
    ((G.neighborFinset u.1 ∩ G.neighborFinset z.1).filter
        fun w ↦ w ∈ c.supp).card +
      (outsideServiceFinset (G.induce c.suppᶜ)
        (fun u' y ↦ G.Adj u'.1 y.1) u z).card = 1 := by
  classical
  rw [outsideServiceFinset_induce_card]
  simpa only using
    (card_insideCommon_add_card_outsideCommon_eq_one
      G hfree c u z.1 z.2)

/-- The generator's entrywise target `1 - H B`, expressed without matrix
casts as the one remaining service after internal common neighbors. -/
def outsideCertificateTarget
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (u : c.supp) (z : {x : V // x ∉ c.supp}) : Nat :=
  1 - ((G.neighborFinset u.1 ∩ G.neighborFinset z.1).filter
    fun w ↦ w ∈ c.supp).card

theorem outsideServiceFinset_card_eq_certificateTarget
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (u : c.supp) (z : {x : V // x ∉ c.supp}) :
    (outsideServiceFinset (G.induce c.suppᶜ)
      (fun u' y ↦ G.Adj u'.1 y.1) u z).card =
      outsideCertificateTarget G c u z := by
  have hroute := card_insideCommon_add_outsideService_eq_one
    G hfree c u z
  unfold outsideCertificateTarget
  omega

/-- A C4-free ambient graph satisfies every abstract clause family emitted
by the outside-C certificate generator, with its exact `1 - H B` target. -/
theorem outsideCClauseSemantics_of_ambient
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    OutsideCClauseSemantics (G.induce c.suppᶜ)
      (fun u y ↦ G.Adj u.1 y.1) (outsideCertificateTarget G c) := by
  classical
  apply outsideCClauseSemantics_of_exact_service
  · exact outsideServiceFinset_card_eq_certificateTarget G hfree c
  · intro hC4
    obtain ⟨f, hf, hadj⟩ := hC4
    apply hfree
    refine ⟨Subtype.val ∘ f, Subtype.val_injective.comp hf, ?_⟩
    intro i j hij
    exact hadj i j hij

end

end Erdos85
