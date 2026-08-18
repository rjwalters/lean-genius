import Proofs.Erdos85OrderSixtyFourFourSelectorSupportCardinality

/-!
# Unique labels for four-selector cubes

The four-coordinate support is not merely an orthogonal array of cardinality
`1024`: it is partitioned by the ambient vertices into disjoint
`2 × 2 × 2 × 2` cubes.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The selector of an ambient label, regarded as a finset in the component
support subtype. -/
def componentNeighborSupportFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent) (x : V) :
    Finset c.supp := by
  classical
  exact Finset.univ.filter fun u =>
    u.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) c x

/-- The four-coordinate cube carried by one ambient label. -/
def fourSelectorLabelFiberFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent) (x : V) :
    Finset (c.supp × (d.supp × (e.supp × f.supp))) :=
  componentNeighborSupportFinset G c x ×ˢ
    (componentNeighborSupportFinset G d x ×ˢ
      (componentNeighborSupportFinset G e x ×ˢ
        componentNeighborSupportFinset G f x))

/-- Membership in the label fiber is exactly the four selector-incidence
conditions occurring in `fourSelectorHyperCubeSupport`. -/
theorem mem_fourSelectorLabelFiberFinset_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent) (x : V)
    (p : c.supp × (d.supp × (e.supp × f.supp))) :
    p ∈ fourSelectorLabelFiberFinset G c d e f x ↔
      p.1.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) c x ∧
      p.2.1.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) d x ∧
      p.2.2.1.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) e x ∧
      p.2.2.2.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) f x := by
  simp [fourSelectorLabelFiberFinset, componentNeighborSupportFinset]

/-- A supported four-tuple has a unique ambient label as soon as its first
two coordinates belong to distinct defect components. -/
theorem fourSelectorHyperCubeSupport_existsUnique_label
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d)
    (p : c.supp × (d.supp × (e.supp × f.supp)))
    (hp : p ∈ fourSelectorHyperCubeSupport G c d e f) :
    ∃! x : V, p ∈ fourSelectorLabelFiberFinset G c d e f x := by
  rcases hp with ⟨x, hxc, hxd, hxe, hxf⟩
  refine ⟨x, (mem_fourSelectorLabelFiberFinset_iff G c d e f x p).2
    ⟨hxc, hxd, hxe, hxf⟩, ?_⟩
  intro y hy
  have hy' := (mem_fourSelectorLabelFiberFinset_iff G c d e f y p).1 hy
  obtain ⟨z, hz, hzUnique⟩ :=
    existsUnique_mem_cross_componentNeighborFinsets
      G hfree c d hcd p.1 p.2.1
  exact (hzUnique y ⟨hy'.1, hy'.2.1⟩).trans
    (hzUnique x ⟨hxc, hxd⟩).symm

/-- In a normalized size-two component, the selector of every ambient label
has two points even after passing to the component-support subtype. -/
theorem binarySquare_regular_componentNeighborSupportFinset_card_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (x : V) :
    (componentNeighborSupportFinset G c x).card = 2 := by
  classical
  have hs := binarySquare_regular_sizeTwoPart_selector_card
    G hfree hq hreg hcard c hc x
  obtain ⟨u, v, huv, huvPair⟩ := Finset.card_eq_two.mp hs
  have hu := Finset.mem_filter.mp (show
    u ∈ componentNeighborFinset G (secondOrderDefectGraph G) c x by
      rw [huvPair]; simp [huv])
  have hv := Finset.mem_filter.mp (show
    v ∈ componentNeighborFinset G (secondOrderDefectGraph G) c x by
      rw [huvPair]; simp)
  let u' : c.supp := ⟨u,
    (SimpleGraph.ConnectedComponent.mem_supp_iff c u).2 hu.2⟩
  let v' : c.supp := ⟨v,
    (SimpleGraph.ConnectedComponent.mem_supp_iff c v).2 hv.2⟩
  have huv' : u' ≠ v' := fun h => huv (congrArg Subtype.val h)
  have heq : componentNeighborSupportFinset G c x = {u', v'} := by
    ext z
    simp only [componentNeighborSupportFinset, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    rw [huvPair]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  rw [heq]
  simp [huv']

/-- Four normalized size-two coordinates give every ambient label an exact
16-point selector cube. -/
theorem binarySquare_regular_fourSelectorLabelFiberFinset_card_sixteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2)
    (he : e.supp.ncard = q * 2) (hf : f.supp.ncard = q * 2) (x : V) :
    (fourSelectorLabelFiberFinset G c d e f x).card = 16 := by
  simp [fourSelectorLabelFiberFinset, Finset.card_product,
    binarySquare_regular_componentNeighborSupportFinset_card_two
      G hfree hq hreg hcard c hc x,
    binarySquare_regular_componentNeighborSupportFinset_card_two
      G hfree hq hreg hcard d hd x,
    binarySquare_regular_componentNeighborSupportFinset_card_two
      G hfree hq hreg hcard e he x,
    binarySquare_regular_componentNeighborSupportFinset_card_two
      G hfree hq hreg hcard f hf x]

/-- Label fibers of two distinct ambient vertices are disjoint. -/
theorem fourSelectorLabelFiberFinset_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d)
    {x y : V} (hxy : x ≠ y) :
    Disjoint (fourSelectorLabelFiberFinset G c d e f x)
      (fourSelectorLabelFiberFinset G c d e f y) := by
  rw [Finset.disjoint_left]
  intro p hpx hpy
  have hp : p ∈ fourSelectorHyperCubeSupport G c d e f := by
    exact ⟨x, (mem_fourSelectorLabelFiberFinset_iff G c d e f x p).1 hpx⟩
  obtain ⟨z, hz, hzUnique⟩ :=
    fourSelectorHyperCubeSupport_existsUnique_label G hfree c d e f hcd p hp
  exact hxy ((hzUnique x hpx).trans (hzUnique y hpy).symm)

/-- The finite four-selector support is exactly the union of the cubes carried
by all ambient labels. Together with `fourSelectorLabelFiberFinset_disjoint`,
this is the explicit disjoint-cube partition interface. -/
theorem fourSelectorHyperCubeSupportFinset_eq_biUnion_labelFibers
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent) :
    fourSelectorHyperCubeSupportFinset G c d e f =
      Finset.univ.biUnion (fourSelectorLabelFiberFinset G c d e f) := by
  classical
  ext p
  simp [fourSelectorHyperCubeSupportFinset, fourSelectorHyperCubeSupport,
    mem_fourSelectorLabelFiberFinset_iff]

end

end Erdos85
