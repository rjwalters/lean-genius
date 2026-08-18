import Proofs.Erdos85BinarySquareSizeTwoRoutingRegularity
import Proofs.Erdos85BinarySquareCrossRoutingSymmetry

/-! # Uniform via-color tilings in the all-size-two stratum -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Ordered endpoint pairs whose unique common neighbor lies in component
`via`.  Sigma coordinates make the row-fiber census definitionally visible. -/
def crossRoutingViaFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {source target : (secondOrderDefectGraph G).ConnectedComponent}
    (hst : source ≠ target)
    (via : (secondOrderDefectGraph G).ConnectedComponent) :
    Finset (Σ _ : source.supp, target.supp) :=
  Finset.univ.sigma fun x => (Finset.univ : Finset target.supp).filter fun z =>
    via = crossIntermediateComponent G hfree hst x z

/-- Different via-colors occupy disjoint endpoint cells. -/
theorem crossRoutingViaFinset_disjoint_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {source target : (secondOrderDefectGraph G).ConnectedComponent}
    (hst : source ≠ target)
    {via via' : (secondOrderDefectGraph G).ConnectedComponent}
    (hne : via ≠ via') :
    Disjoint (crossRoutingViaFinset G hfree hst via)
      (crossRoutingViaFinset G hfree hst via') := by
  classical
  rw [Finset.disjoint_left]
  intro p hp hp'
  simp only [crossRoutingViaFinset, Finset.mem_sigma, Finset.mem_univ,
    Finset.mem_filter, true_and] at hp hp'
  exact hne (hp.trans hp'.symm)

/-- The via-color classes tile the complete ordered endpoint grid. -/
theorem biUnion_crossRoutingViaFinset_eq_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {source target : (secondOrderDefectGraph G).ConnectedComponent}
    (hst : source ≠ target) :
    (Finset.univ : Finset
      (secondOrderDefectGraph G).ConnectedComponent).biUnion
        (crossRoutingViaFinset G hfree hst) = Finset.univ := by
  classical
  ext p
  constructor
  · intro _
    exact Finset.mem_univ p
  · intro _
    apply Finset.mem_biUnion.mpr
    refine ⟨crossIntermediateComponent G hfree hst p.1 p.2,
      Finset.mem_univ _, ?_⟩
    simp [crossRoutingViaFinset]

/-- Three local size-two hypotheses suffice: a via-color has exactly `8q`
endpoint cells between the source and target.  No fourth component, nor an
all-size-two global partition, is used. -/
theorem binarySquare_regular_threeSizeTwo_crossRoutingViaFinset_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    {source target : (secondOrderDefectGraph G).ConnectedComponent}
    (hst : source ≠ target)
    (via : (secondOrderDefectGraph G).ConnectedComponent)
    (hsource : source.supp.ncard = q * 2)
    (hvia : via.supp.ncard = q * 2)
    (htarget : target.supp.ncard = q * 2) :
    (crossRoutingViaFinset G hfree hst via).card = 8 * q := by
  classical
  rw [crossRoutingViaFinset, Finset.card_sigma]
  have hrow : ∀ x : source.supp,
      ((Finset.univ : Finset target.supp).filter fun z =>
        via = crossIntermediateComponent G hfree hst x z).card = 4 := by
    intro x
    exact binarySquare_regular_threeSizeTwoParts_routing_row_card_eq_four
      G hfree hq hreg hcard source via target hst
        hsource hvia htarget x
  simp_rw [hrow]
  rw [Finset.sum_const, Finset.card_univ, Set.fintypeCard_eq_ncard,
    hsource]
  change (q * 2) * 4 = 8 * q
  omega

/-- Global all-size-two convenience wrapper around the three-local theorem. -/
theorem binarySquare_regular_allSizeTwo_crossRoutingViaFinset_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hall : ∀ d : (secondOrderDefectGraph G).ConnectedComponent,
      d.supp.ncard = q * 2)
    {source target : (secondOrderDefectGraph G).ConnectedComponent}
    (hst : source ≠ target)
    (via : (secondOrderDefectGraph G).ConnectedComponent) :
    (crossRoutingViaFinset G hfree hst via).card = 8 * q :=
  binarySquare_regular_threeSizeTwo_crossRoutingViaFinset_card
    G hfree hq hreg hcard hst via (hall source) (hall via) (hall target)

/-- The six directed restricted owner factors among three components are
single cycle factors (a finite connected 2-regular factor is one cycle). -/
def HasThreeCyclicRestrictedOwnerFactors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (a b c : (secondOrderDefectGraph G).ConnectedComponent) : Prop :=
  (restrictedComponentOwnerGraph G a b).Connected ∧
  (restrictedComponentOwnerGraph G b a).Connected ∧
  (restrictedComponentOwnerGraph G a c).Connected ∧
  (restrictedComponentOwnerGraph G c a).Connected ∧
  (restrictedComponentOwnerGraph G b c).Connected ∧
  (restrictedComponentOwnerGraph G c b).Connected

/-- Precise unproved extension interface suggested by the q=8 third-block
death.  It mentions only three local size-two components: cyclic owner
factors should forbid their three via-tiles on one ordered grid from being
pairwise disjoint.  This is a `Prop`, not an asserted Lean axiom. -/
def ThreeSizeTwoViaTripleExclusionPrinciple
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) : Prop :=
  ∀ {q : ℕ},
    (∀ x, G.degree x = q) → Fintype.card V = q * q →
    ∀ (a b c : (secondOrderDefectGraph G).ConnectedComponent),
    ∀ (hab : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c),
    a.supp.ncard = q * 2 → b.supp.ncard = q * 2 →
    c.supp.ncard = q * 2 → HasThreeCyclicRestrictedOwnerFactors G a b c →
    ¬(Disjoint (crossRoutingViaFinset G hfree hab a)
          (crossRoutingViaFinset G hfree hab b) ∧
      Disjoint (crossRoutingViaFinset G hfree hab a)
          (crossRoutingViaFinset G hfree hab c) ∧
      Disjoint (crossRoutingViaFinset G hfree hab b)
          (crossRoutingViaFinset G hfree hab c))

/-- The via-tiling laws convert the three-component exclusion principle into
an immediate contradiction. -/
theorem false_of_threeSizeTwoViaTripleExclusionPrinciple
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hprinciple : ThreeSizeTwoViaTripleExclusionPrinciple G hfree)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a.supp.ncard = q * 2) (hb : b.supp.ncard = q * 2)
    (hc : c.supp.ncard = q * 2)
    (hcyclic : HasThreeCyclicRestrictedOwnerFactors G a b c) : False := by
  apply hprinciple hreg hcard a b c hab hac hbc ha hb hc hcyclic
  exact ⟨
    crossRoutingViaFinset_disjoint_of_ne G hfree hab hab,
    crossRoutingViaFinset_disjoint_of_ne G hfree hab hac,
    crossRoutingViaFinset_disjoint_of_ne G hfree hab hbc⟩

end

end Erdos85

#print axioms Erdos85.crossRoutingViaFinset_disjoint_of_ne
#print axioms Erdos85.biUnion_crossRoutingViaFinset_eq_univ
#print axioms Erdos85.binarySquare_regular_threeSizeTwo_crossRoutingViaFinset_card
#print axioms Erdos85.binarySquare_regular_allSizeTwo_crossRoutingViaFinset_card
#print axioms Erdos85.false_of_threeSizeTwoViaTripleExclusionPrinciple
