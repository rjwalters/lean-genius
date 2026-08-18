import Proofs.Erdos85BinarySquareRoutingRowStarDecomposition
import Proofs.Erdos85BinarySquareOwnerBlockEquitable
import Proofs.Erdos85BinarySquareMixedOwnerCanonicalForkCenters
import Proofs.Erdos85BinarySquareSameRouteOwnerForkCenters
import Proofs.Erdos85BinarySquareOppositeOwnerBowtieCenters
import Proofs.Erdos85OrderSixtyFourThreeComponentForkAdapter

/-! # Generic routing-row density from two separated fork centers -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Two distinct same-color centers over a common root contribute two
disjoint full star rows.  Their union occupies exactly `2*m_target` points of
an owner routing row of size `m_owner*m_target`; saturation is the special
case `m_owner=2`. -/
theorem binarySquare_regular_twoSeparatedCenters_routingRow_density
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = q * m d)
    {source target owner : (secondOrderDefectGraph G).ConnectedComponent}
    (hst : source ≠ target) (x : source.supp)
    (u₁ u₂ : owner.supp) (hu : u₁ ≠ u₂)
    (hxu₁ : G.Adj x.1 u₁.1) (hxu₂ : G.Adj x.1 u₂.1) :
    let S₁ := componentCrossNeighborFinset G target u₁
    let S₂ := componentCrossNeighborFinset G target u₂
    let R := (Finset.univ : Finset target.supp).filter fun y =>
      owner = crossIntermediateComponent G hfree hst x y
    Disjoint S₁ S₂ ∧ (S₁ ∪ S₂).card = 2 * m target ∧
      S₁ ∪ S₂ ⊆ R ∧ R.card = m owner * m target := by
  classical
  let S₁ := componentCrossNeighborFinset G target u₁
  let S₂ := componentCrossNeighborFinset G target u₂
  let R := (Finset.univ : Finset target.supp).filter fun y =>
    owner = crossIntermediateComponent G hfree hst x y
  have hu₁row : u₁ ∈ componentCrossNeighborFinset G owner x := by
    rw [componentCrossNeighborFinset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hxu₁⟩
  have hu₂row : u₂ ∈ componentCrossNeighborFinset G owner x := by
    rw [componentCrossNeighborFinset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hxu₂⟩
  have hdis : Disjoint S₁ S₂ := by
    exact routingRow_starRows_pairwise_disjoint
      G hfree hst x hu₁row hu₂row hu
  have hstarCard (u : owner.supp) :
      (componentCrossNeighborFinset G target u).card = m target := by
    rw [card_componentCrossNeighborFinset_eq_componentNeighborFinset]
    have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq hreg hcard owner target (x := u.1) u.2
    rw [hm target] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul
  have hunionCard : (S₁ ∪ S₂).card = 2 * m target := by
    rw [Finset.card_union_of_disjoint hdis]
    simp only [S₁, S₂, hstarCard]
    omega
  have hsubset : S₁ ∪ S₂ ⊆ R := by
    have hdecomp := routingRow_eq_biUnion_componentCrossNeighborFinset
      G hfree hst owner x
    change R = _ at hdecomp
    rw [hdecomp]
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact Finset.mem_biUnion.mpr ⟨u₁, hu₁row, hy⟩
    · exact Finset.mem_biUnion.mpr ⟨u₂, hu₂row, hy⟩
  have hRcard : R.card = m owner * m target := by
    let T := componentNeighborFinset
      (componentOwnerGraph G (secondOrderDefectGraph G) owner)
      (secondOrderDefectGraph G) target x.1
    have hRT : R.card = T.card := by
      apply Finset.card_bij (fun y _ => y.1)
      · intro y hy
        have hyRoute := (Finset.mem_filter.mp hy).2
        have hyOwner := componentOwnerGraph_adj_of_crossIntermediateComponent_eq_owner
          G hfree hst x y owner hyRoute.symm
        change y.1 ∈ componentNeighborFinset
          (componentOwnerGraph G (secondOrderDefectGraph G) owner)
          (secondOrderDefectGraph G) target x.1
        rw [componentNeighborFinset, Finset.mem_filter]
        exact ⟨((componentOwnerGraph G
          (secondOrderDefectGraph G) owner).mem_neighborFinset _ _).mpr hyOwner,
          (ConnectedComponent.mem_supp_iff target y.1).mp y.2⟩
      · intro y hy z hz heq
        exact Subtype.ext heq
      · intro y hy
        have hyData := Finset.mem_filter.mp hy
        have hySupp : y ∈ target.supp :=
          (ConnectedComponent.mem_supp_iff target y).mpr hyData.2
        let ys : target.supp := ⟨y, hySupp⟩
        have hyRoute := crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
          G hfree hst x ys owner
            (((componentOwnerGraph G
              (secondOrderDefectGraph G) owner).mem_neighborFinset _ _).mp hyData.1)
        refine ⟨ys, ?_, rfl⟩
        change ys ∈ (Finset.univ : Finset target.supp).filter (fun y =>
          owner = crossIntermediateComponent G hfree hst x y)
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hyRoute.symm⟩
    rw [hRT]
    have hT := binarySquare_regular_componentOwnerGraph_blockNeighborCard
      G hfree hq hreg hcard m hm owner source target x
    rw [if_neg hst] at hT
    exact hT
  exact ⟨hdis, hunionCard, hsubset, hRcard⟩

/-- Packaged graph-facing statement that two separated centers occupy a
known fraction of one routing row. -/
def HasTwoCenterRoutingRowDensity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (source target owner : (secondOrderDefectGraph G).ConnectedComponent)
    (hst : source ≠ target) (x : source.supp) : Prop :=
  ∃ u₁ u₂ : owner.supp, u₁ ≠ u₂ ∧ G.Adj x.1 u₁.1 ∧ G.Adj x.1 u₂.1 ∧
    let S₁ := componentCrossNeighborFinset G target u₁
    let S₂ := componentCrossNeighborFinset G target u₂
    let R := (Finset.univ : Finset target.supp).filter fun y =>
      owner = crossIntermediateComponent G hfree hst x y
    Disjoint S₁ S₂ ∧ (S₁ ∪ S₂).card = 2 * m target ∧
      S₁ ∪ S₂ ⊆ R ∧ R.card = m owner * m target

/-- An owner-level wrapper for a dense two-center routing-row fragment,
allowing its source, target, and root to vary. -/
def HasTwoCenterRoutingRowDensityForOwner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (owner : (secondOrderDefectGraph G).ConnectedComponent) : Prop :=
  ∃ (source target : (secondOrderDefectGraph G).ConnectedComponent)
      (hst : source ≠ target) (x : source.supp),
    HasTwoCenterRoutingRowDensity G hfree m source target owner hst x

/-- Owner-level saturation by two distinct star centers: their target stars
equal the entire routing row. -/
def HasTwoCenterRoutingRowSaturationForOwner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (owner : (secondOrderDefectGraph G).ConnectedComponent) : Prop :=
  ∃ (source target : (secondOrderDefectGraph G).ConnectedComponent)
      (hst : source ≠ target) (x : source.supp) (u₁ u₂ : owner.supp),
    u₁ ≠ u₂ ∧ G.Adj x.1 u₁.1 ∧ G.Adj x.1 u₂.1 ∧
      componentCrossNeighborFinset G target u₁ ∪
          componentCrossNeighborFinset G target u₂ =
        ((Finset.univ : Finset target.supp).filter fun y =>
          owner = crossIntermediateComponent G hfree hst x y)

/-- A two-center density fragment owned by a normalized size-two component
must saturate its routing row. -/
theorem twoCenterRoutingRowDensityForOwner_saturates_of_m_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (owner : (secondOrderDefectGraph G).ConnectedComponent)
    (hmo : m owner = 2)
    (h : HasTwoCenterRoutingRowDensityForOwner G hfree m owner) :
    HasTwoCenterRoutingRowSaturationForOwner G hfree owner := by
  rcases h with ⟨source, target, hst, x, u₁, u₂, hne, hx₁, hx₂,
    _hdis, hunionCard, hsub, hrowCard⟩
  refine ⟨source, target, hst, x, u₁, u₂, hne, hx₁, hx₂, ?_⟩
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hrowCard, hunionCard, hmo]

/-- Correct q-generic successor of canonical fork separation: one of its two
owner colors contributes a two-star routing-row fragment with exact density
`2/m_owner`. -/
theorem binarySquare_regular_ownerFork_forces_twoCenterRoutingRowDensity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = q * m d)
    {d e f₁ f₂ b c : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (hef₁ : e ≠ f₁) (hef₂ : e ≠ f₂)
    (hdf₁ : d ≠ f₁) (hdf₂ : d ≠ f₂) (hbc : b ≠ c)
    (x : d.supp) (y : e.supp) (z₁ : f₁.supp) (z₂ : f₂.supp)
    (hz : z₁.1 ≠ z₂.1)
    (hby₁ : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y.1 z₁.1)
    (hby₂ : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y.1 z₂.1)
    (hcx₁ : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj z₁.1 x.1)
    (hcx₂ : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj z₂.1 x.1) :
    HasTwoCenterRoutingRowDensity G hfree m d e c hde x ∨
      HasTwoCenterRoutingRowDensity G hfree m e d b hde.symm y := by
  have hcx₁' : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj x.1 z₁.1 :=
    ((componentOwnerGraph G (secondOrderDefectGraph G) c).adj_comm x.1 z₁.1).mpr hcx₁
  have hcx₂' : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj x.1 z₂.1 :=
    ((componentOwnerGraph G (secondOrderDefectGraph G) c).adj_comm x.1 z₂.1).mpr hcx₂
  let uc₁ : c.supp := ⟨crossCommonNeighbor G hfree hdf₁ x z₁,
    crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj G hfree hdf₁ x z₁
      hcx₁'⟩
  let uc₂ : c.supp := ⟨crossCommonNeighbor G hfree hdf₂ x z₂,
    crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj G hfree hdf₂ x z₂
      hcx₂'⟩
  let ub₁ : b.supp := ⟨crossCommonNeighbor G hfree hef₁ y z₁,
    crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj G hfree hef₁ y z₁ hby₁⟩
  let ub₂ : b.supp := ⟨crossCommonNeighbor G hfree hef₂ y z₂,
    crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj G hfree hef₂ y z₂ hby₂⟩
  have hsep := ownerFork_canonicalCenter_separation_without_root_separation
    G hfree hef₁ hef₂ hdf₁ hdf₂ hbc x y z₁ z₂ hz
      hby₁ hby₂ hcx₁ hcx₂
  change ub₁.1 ≠ ub₂.1 ∨ uc₁.1 ≠ uc₂.1 at hsep
  rcases hsep with hb | hc
  · right
    have hb' : ub₁ ≠ ub₂ := fun h => hb (congrArg Subtype.val h)
    refine ⟨ub₁, ub₂, hb',
      (crossCommonNeighbor_spec G hfree hef₁ y z₁).1,
      (crossCommonNeighbor_spec G hfree hef₂ y z₂).1, ?_⟩
    exact binarySquare_regular_twoSeparatedCenters_routingRow_density
      G hfree hq hreg hcard m hm hde.symm y ub₁ ub₂ hb'
        (crossCommonNeighbor_spec G hfree hef₁ y z₁).1
        (crossCommonNeighbor_spec G hfree hef₂ y z₂).1
  · left
    have hc' : uc₁ ≠ uc₂ := fun h => hc (congrArg Subtype.val h)
    refine ⟨uc₁, uc₂, hc',
      (crossCommonNeighbor_spec G hfree hdf₁ x z₁).1,
      (crossCommonNeighbor_spec G hfree hdf₂ x z₂).1, ?_⟩
    exact binarySquare_regular_twoSeparatedCenters_routingRow_density
      G hfree hq hreg hcard m hm hde x uc₁ uc₂ hc'
        (crossCommonNeighbor_spec G hfree hdf₁ x z₁).1
        (crossCommonNeighbor_spec G hfree hdf₂ x z₂).1

/-- A rainbow-pattern repeated closing reaches the generic density terminal
without exposing its witnesses manually. -/
theorem binarySquare_regular_rainbowRepeatedClosing_forces_twoCenterRoutingRowDensity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = q * m d)
    (a b c e f g : (secondOrderDefectGraph G).ConnectedComponent)
    (hef : e ≠ f) (hfg : f ≠ g) (heg : e ≠ g) (hbc : b ≠ c)
    (hrepeat : HasRepeatedClosingInBlock (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) e f g) :
    (∃ x : e.supp, HasTwoCenterRoutingRowDensity G hfree m e f c hef x) ∨
      (∃ y : f.supp, HasTwoCenterRoutingRowDensity G hfree m f e b hef.symm y) := by
  obtain ⟨x, y, z₁, z₂, hz, hx, hy, hz₁, hz₂,
    _haxy, hby₁, hcx₁, hby₂, hcx₂⟩ :=
    (hasRepeatedClosingInBlock_iff_exists_ownerFork
      (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) e f g).mp hrepeat
  let xs : e.supp := ⟨x, (ConnectedComponent.mem_supp_iff e x).mpr hx⟩
  let ys : f.supp := ⟨y, (ConnectedComponent.mem_supp_iff f y).mpr hy⟩
  let z₁s : g.supp := ⟨z₁, (ConnectedComponent.mem_supp_iff g z₁).mpr hz₁⟩
  let z₂s : g.supp := ⟨z₂, (ConnectedComponent.mem_supp_iff g z₂).mpr hz₂⟩
  have hdensity := binarySquare_regular_ownerFork_forces_twoCenterRoutingRowDensity
    G hfree hq hreg hcard m hm hef hfg hfg heg heg hbc
      xs ys z₁s z₂s hz hby₁ hby₂ hcx₁ hcx₂
  rcases hdensity with h | h
  · exact Or.inl ⟨xs, h⟩
  · exact Or.inr ⟨ys, h⟩

/-- An equal-root repeated closing also reaches a cross-component routing-row
density terminal.  Although both fork roots lie in `e`, either separated
center pair shares one of those roots and routes into the distinct closing
component `g`. -/
theorem binarySquare_regular_equalRootsRepeatedClosing_forces_twoCenterRoutingRowDensity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = q * m d)
    (a b c e f g : (secondOrderDefectGraph G).ConnectedComponent)
    (hbc : b ≠ c) (hef : e = f) (hfg : f ≠ g)
    (hrepeat : HasRepeatedClosingInBlock (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) e f g) :
    (∃ y : e.supp, HasTwoCenterRoutingRowDensity G hfree m e g b
        (hef ▸ hfg) y) ∨
      (∃ x : e.supp, HasTwoCenterRoutingRowDensity G hfree m e g c
        (hef ▸ hfg) x) := by
  subst f
  obtain ⟨x, y, z₁, z₂, _hz, _haxy, hby₁, hcx₁, hby₂, hcx₂, hsep⟩ :=
    hasRepeatedClosingInBlock_equalRoots_canonicalCenter_separation
      G hfree a b c e e g hbc rfl hfg hrepeat
  let ub₁ : b.supp := ⟨crossCommonNeighbor G hfree hfg y z₁,
    crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj
      G hfree hfg y z₁ hby₁⟩
  let ub₂ : b.supp := ⟨crossCommonNeighbor G hfree hfg y z₂,
    crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj
      G hfree hfg y z₂ hby₂⟩
  let uc₁ : c.supp := ⟨crossCommonNeighbor G hfree hfg x z₁,
    crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj
      G hfree hfg x z₁
        (((componentOwnerGraph G
          (secondOrderDefectGraph G) c).adj_comm _ _).mpr hcx₁)⟩
  let uc₂ : c.supp := ⟨crossCommonNeighbor G hfree hfg x z₂,
    crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj
      G hfree hfg x z₂
        (((componentOwnerGraph G
          (secondOrderDefectGraph G) c).adj_comm _ _).mpr hcx₂)⟩
  change ub₁.1 ≠ ub₂.1 ∨ uc₁.1 ≠ uc₂.1 at hsep
  rcases hsep with hb | hc
  · have hb' : ub₁ ≠ ub₂ := fun h => hb (congrArg Subtype.val h)
    refine Or.inl ⟨y, ub₁, ub₂, hb',
      (crossCommonNeighbor_spec G hfree hfg y z₁).1,
      (crossCommonNeighbor_spec G hfree hfg y z₂).1, ?_⟩
    exact binarySquare_regular_twoSeparatedCenters_routingRow_density
      G hfree hq hreg hcard m hm hfg y ub₁ ub₂ hb'
        (crossCommonNeighbor_spec G hfree hfg y z₁).1
        (crossCommonNeighbor_spec G hfree hfg y z₂).1
  · have hc' : uc₁ ≠ uc₂ := fun h => hc (congrArg Subtype.val h)
    refine Or.inr ⟨x, uc₁, uc₂, hc',
      (crossCommonNeighbor_spec G hfree hfg x z₁).1,
      (crossCommonNeighbor_spec G hfree hfg x z₂).1, ?_⟩
    exact binarySquare_regular_twoSeparatedCenters_routingRow_density
      G hfree hq hreg hcard m hm hfg x uc₁ uc₂ hc'
        (crossCommonNeighbor_spec G hfree hfg x z₁).1
        (crossCommonNeighbor_spec G hfree hfg x z₂).1

/-- If an equal-root fork has the same owner on both closing routes, its
q-generic same-route center separation still forces a density fragment for
that repeated route owner. -/
theorem binarySquare_regular_equalRootsSameRouteRepeatedClosing_forces_ownerDensity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = q * m d)
    (a b e f g : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hef : e = f) (hfg : f ≠ g)
    (hrepeat : HasRepeatedClosingInBlock (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) b) e f g) :
    HasTwoCenterRoutingRowDensityForOwner G hfree m b := by
  subst f
  obtain ⟨x, y, z₁, z₂, hz, hx, hy, hz₁, hz₂,
    haxy, hby₁, hbx₁, hby₂, hbx₂⟩ :=
      (hasRepeatedClosingInBlock_iff_exists_ownerFork
        (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) e e g).mp hrepeat
  let xs : e.supp := ⟨x, (ConnectedComponent.mem_supp_iff e x).mpr hx⟩
  let ys : e.supp := ⟨y, (ConnectedComponent.mem_supp_iff e y).mpr hy⟩
  let z₁s : g.supp := ⟨z₁, (ConnectedComponent.mem_supp_iff g z₁).mpr hz₁⟩
  let z₂s : g.supp := ⟨z₂, (ConnectedComponent.mem_supp_iff g z₂).mpr hz₂⟩
  let uy₁ : b.supp := ⟨crossCommonNeighbor G hfree hfg ys z₁s,
    crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj
      G hfree hfg ys z₁s hby₁⟩
  let uy₂ : b.supp := ⟨crossCommonNeighbor G hfree hfg ys z₂s,
    crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj
      G hfree hfg ys z₂s hby₂⟩
  let ux₁ : b.supp := ⟨crossCommonNeighbor G hfree hfg xs z₁s,
    crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj
      G hfree hfg xs z₁s
        (((componentOwnerGraph G
          (secondOrderDefectGraph G) b).adj_comm _ _).mpr hbx₁)⟩
  let ux₂ : b.supp := ⟨crossCommonNeighbor G hfree hfg xs z₂s,
    crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj
      G hfree hfg xs z₂s
        (((componentOwnerGraph G
          (secondOrderDefectGraph G) b).adj_comm _ _).mpr hbx₂)⟩
  have hsep := sameRouteOwnerFork_canonicalCenter_separation
    G hfree hfg hab xs ys z₁s z₂s hz haxy hby₁ hbx₁ hby₂ hbx₂
  change uy₁.1 ≠ uy₂.1 ∨ ux₁.1 ≠ ux₂.1 at hsep
  rcases hsep with hysep | hxsep
  · have hysep' : uy₁ ≠ uy₂ := fun h => hysep (congrArg Subtype.val h)
    refine ⟨e, g, hfg, ys, uy₁, uy₂, hysep',
      (crossCommonNeighbor_spec G hfree hfg ys z₁s).1,
      (crossCommonNeighbor_spec G hfree hfg ys z₂s).1, ?_⟩
    exact binarySquare_regular_twoSeparatedCenters_routingRow_density
      G hfree hq hreg hcard m hm hfg ys uy₁ uy₂ hysep'
        (crossCommonNeighbor_spec G hfree hfg ys z₁s).1
        (crossCommonNeighbor_spec G hfree hfg ys z₂s).1
  · have hxsep' : ux₁ ≠ ux₂ := fun h => hxsep (congrArg Subtype.val h)
    refine ⟨e, g, hfg, xs, ux₁, ux₂, hxsep',
      (crossCommonNeighbor_spec G hfree hfg xs z₁s).1,
      (crossCommonNeighbor_spec G hfree hfg xs z₂s).1, ?_⟩
    exact binarySquare_regular_twoSeparatedCenters_routingRow_density
      G hfree hq hreg hcard m hm hfg xs ux₁ ux₂ hxsep'
        (crossCommonNeighbor_spec G hfree hfg xs z₁s).1
        (crossCommonNeighbor_spec G hfree hfg xs z₂s).1

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_twoSeparatedCenters_routingRow_density
#print axioms Erdos85.twoCenterRoutingRowDensityForOwner_saturates_of_m_eq_two
#print axioms Erdos85.binarySquare_regular_ownerFork_forces_twoCenterRoutingRowDensity
#print axioms Erdos85.binarySquare_regular_rainbowRepeatedClosing_forces_twoCenterRoutingRowDensity
#print axioms Erdos85.binarySquare_regular_equalRootsRepeatedClosing_forces_twoCenterRoutingRowDensity
#print axioms Erdos85.binarySquare_regular_equalRootsSameRouteRepeatedClosing_forces_ownerDensity
