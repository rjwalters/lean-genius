import Proofs.Erdos85BinarySquareRoutingRowStarDecomposition

/-! # Canonical center pairs across defect-adjacent roots -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A target vertex records its canonical common-neighbor center with each of
two roots. -/
def crossRootCenterPair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d e : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x y : d.supp) (w : e.supp) : V × V :=
  (crossCommonNeighbor G hfree hde x w,
    crossCommonNeighbor G hfree hde y w)

/-- The edge set of center pairs contributed by one remote target component. -/
def crossRootCenterPairFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d e : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x y : d.supp) : Finset (V × V) :=
  (Finset.univ : Finset e.supp).image
    (crossRootCenterPair G hfree hde x y)

/-- The full grid of possible ordered centers at two roots. -/
def crossRootCenterGrid
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) : Finset (V × V) :=
  G.neighborFinset x ×ˢ G.neighborFinset y

/-- Every canonical center pair lies in the ambient neighbor grid. -/
theorem crossRootCenterPairFinset_subset_centerGrid
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d e : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x y : d.supp) :
    crossRootCenterPairFinset G hfree hde x y ⊆
      crossRootCenterGrid G x.1 y.1 := by
  intro p hp
  obtain ⟨w, _hw, rfl⟩ := Finset.mem_image.mp hp
  rw [crossRootCenterGrid, Finset.mem_product]
  exact ⟨(G.mem_neighborFinset x.1 _).mpr
      (crossCommonNeighbor_spec G hfree hde x w).1,
    (G.mem_neighborFinset y.1 _).mpr
      (crossCommonNeighbor_spec G hfree hde y w).1⟩

/-- If the two roots are adjacent in the second-order defect graph, their
center-pair encoding of a remote component is injective.  Equality of both
centers for two different target vertices would give a four-cycle; equality
of the two centers with each other would give the defect-adjacent roots a
common neighbor. -/
theorem crossRootCenterPair_injective_of_secondOrderDefect_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d e : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x y : d.supp)
    (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1) :
    Function.Injective (crossRootCenterPair G hfree hde x y) := by
  intro w₁ w₂ hpairs
  let u := crossCommonNeighbor G hfree hde x w₁
  let v := crossCommonNeighbor G hfree hde y w₁
  have hxy : x.1 ≠ y.1 := (secondOrderDefectGraph G).ne_of_adj hxyD
  have huSpec := crossCommonNeighbor_spec G hfree hde x w₁
  have hvSpec := crossCommonNeighbor_spec G hfree hde y w₁
  have huv : u ≠ v := by
    intro huv
    have hyu : G.Adj y.1 u := by
      rw [huv]
      exact hvSpec.1
    apply not_secondOrderDefect_adj_of_commonNeighbor G hfree hxy
      huSpec.1 hyu
    exact hxyD
  have huEq :
      crossCommonNeighbor G hfree hde x w₁ =
        crossCommonNeighbor G hfree hde x w₂ :=
    congrArg Prod.fst hpairs
  have hvEq :
      crossCommonNeighbor G hfree hde y w₁ =
        crossCommonNeighbor G hfree hde y w₂ :=
    congrArg Prod.snd hpairs
  have huSpec₂ := crossCommonNeighbor_spec G hfree hde x w₂
  have hvSpec₂ := crossCommonNeighbor_spec G hfree hde y w₂
  rw [← huEq] at huSpec₂
  rw [← hvEq] at hvSpec₂
  apply Subtype.ext
  by_contra hw
  apply hfree
  exact containsC4_of_two_common huv hw
    huSpec.2 hvSpec.2 huSpec₂.2 hvSpec₂.2

/-- The target component contributes exactly one transition edge per target
vertex. -/
theorem card_crossRootCenterPairFinset_of_secondOrderDefect_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d e : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x y : d.supp)
    (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1) :
    (crossRootCenterPairFinset G hfree hde x y).card = e.supp.ncard := by
  rw [crossRootCenterPairFinset,
    Finset.card_image_of_injective _
      (crossRootCenterPair_injective_of_secondOrderDefect_adj
        G hfree hde x y hxyD), Finset.card_univ]
  simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq e.supp

/-- Distinct remote target components contribute edge-disjoint transition
graphs for the same defect-adjacent root pair. -/
theorem crossRootCenterPairFinset_disjoint_of_target_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d e f : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f)
    (x y : d.supp)
    (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1) :
    Disjoint (crossRootCenterPairFinset G hfree hde x y)
      (crossRootCenterPairFinset G hfree hdf x y) := by
  classical
  rw [Finset.disjoint_left]
  intro p hpe hpf
  obtain ⟨w, _hw, rfl⟩ := Finset.mem_image.mp hpe
  obtain ⟨z, _hz, hpairs⟩ := Finset.mem_image.mp hpf
  let u := crossCommonNeighbor G hfree hde x w
  let v := crossCommonNeighbor G hfree hde y w
  have hxy : x.1 ≠ y.1 := (secondOrderDefectGraph G).ne_of_adj hxyD
  have huSpec := crossCommonNeighbor_spec G hfree hde x w
  have hvSpec := crossCommonNeighbor_spec G hfree hde y w
  have huv : u ≠ v := by
    intro huv
    have hyu : G.Adj y.1 u := by
      rw [huv]
      exact hvSpec.1
    exact (not_secondOrderDefect_adj_of_commonNeighbor G hfree hxy
      huSpec.1 hyu) hxyD
  have hwz : w.1 ≠ z.1 := by
    intro hwz
    apply hef
    have hwe := (ConnectedComponent.mem_supp_iff e w.1).mp w.2
    have hzf := (ConnectedComponent.mem_supp_iff f z.1).mp z.2
    exact hwe.symm.trans ((congrArg
      (secondOrderDefectGraph G).connectedComponentMk hwz).trans hzf)
  have huEq :
      crossCommonNeighbor G hfree hde x w =
        crossCommonNeighbor G hfree hdf x z :=
    (congrArg Prod.fst hpairs).symm
  have hvEq :
      crossCommonNeighbor G hfree hde y w =
        crossCommonNeighbor G hfree hdf y z :=
    (congrArg Prod.snd hpairs).symm
  have huSpecZ := crossCommonNeighbor_spec G hfree hdf x z
  have hvSpecZ := crossCommonNeighbor_spec G hfree hdf y z
  rw [← huEq] at huSpecZ
  rw [← hvEq] at hvSpecZ
  exact hfree (containsC4_of_two_common huv hwz
    huSpec.2 hvSpec.2 huSpecZ.2 hvSpecZ.2)

/-- Three distinct remote size-sixteen components pack forty-eight distinct
transition edges into the common center-pair grid of a defect edge. -/
theorem three_crossRootCenterPairFinsets_union_card_eq_fortyEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d e f g : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (hdf : d ≠ f) (hdg : d ≠ g)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (he : e.supp.ncard = 16) (hf : f.supp.ncard = 16)
    (hg : g.supp.ncard = 16)
    (x y : d.supp)
    (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1) :
    ((crossRootCenterPairFinset G hfree hde x y ∪
        crossRootCenterPairFinset G hfree hdf x y) ∪
      crossRootCenterPairFinset G hfree hdg x y).card = 48 := by
  let Se := crossRootCenterPairFinset G hfree hde x y
  let Sf := crossRootCenterPairFinset G hfree hdf x y
  let Sg := crossRootCenterPairFinset G hfree hdg x y
  have hEF : Disjoint Se Sf :=
    crossRootCenterPairFinset_disjoint_of_target_ne
      G hfree hde hdf hef x y hxyD
  have hEG : Disjoint Se Sg :=
    crossRootCenterPairFinset_disjoint_of_target_ne
      G hfree hde hdg heg x y hxyD
  have hFG : Disjoint Sf Sg :=
    crossRootCenterPairFinset_disjoint_of_target_ne
      G hfree hdf hdg hfg x y hxyD
  have hUG : Disjoint (Se ∪ Sf) Sg :=
    Finset.disjoint_union_left.mpr ⟨hEG, hFG⟩
  rw [Finset.card_union_of_disjoint hUG,
    Finset.card_union_of_disjoint hEF]
  rw [card_crossRootCenterPairFinset_of_secondOrderDefect_adj
      G hfree hde x y hxyD,
    card_crossRootCenterPairFinset_of_secondOrderDefect_adj
      G hfree hdf x y hxyD,
    card_crossRootCenterPairFinset_of_secondOrderDefect_adj
      G hfree hdg x y hxyD, he, hf, hg]

/-- At order sixty-four, three remote size-sixteen components leave exactly
sixteen unused pairs in the `8 × 8` center grid of a defect edge. -/
theorem orderSixtyFour_three_remoteTargets_centerGrid_complement_card_eq_sixteen
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ z, G.degree z = 8)
    {d e f g : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (hdf : d ≠ f) (hdg : d ≠ g)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (he : e.supp.ncard = 16) (hf : f.supp.ncard = 16)
    (hg : g.supp.ncard = 16)
    (x y : d.supp)
    (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1) :
    (crossRootCenterGrid G x.1 y.1 \ ((
        crossRootCenterPairFinset G hfree hde x y ∪
          crossRootCenterPairFinset G hfree hdf x y) ∪
        crossRootCenterPairFinset G hfree hdg x y)).card = 16 := by
  let U := (crossRootCenterPairFinset G hfree hde x y ∪
      crossRootCenterPairFinset G hfree hdf x y) ∪
    crossRootCenterPairFinset G hfree hdg x y
  have hUcard : U.card = 48 :=
    three_crossRootCenterPairFinsets_union_card_eq_fortyEight
      G hfree hde hdf hdg hef heg hfg he hf hg x y hxyD
  have hUsub : U ⊆ crossRootCenterGrid G x.1 y.1 := by
    rw [Finset.union_subset_iff, Finset.union_subset_iff]
    exact ⟨⟨crossRootCenterPairFinset_subset_centerGrid G hfree hde x y,
      crossRootCenterPairFinset_subset_centerGrid G hfree hdf x y⟩,
      crossRootCenterPairFinset_subset_centerGrid G hfree hdg x y⟩
  change (crossRootCenterGrid G x.1 y.1 \ U).card = 16
  rw [Finset.card_sdiff_of_subset hUsub, hUcard, crossRootCenterGrid,
    Finset.card_product, G.card_neighborFinset_eq_degree,
    G.card_neighborFinset_eq_degree, hreg x.1, hreg y.1]

/-- The fiber of the first-center coordinate is exactly that center's target
selector.  Together with injectivity, this identifies the cross-root encoding
as the edge set of a simple bipartite transition graph. -/
theorem crossRootCenterPair_fst_fiber_eq_componentCrossNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d e c : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x y : d.supp) (u : c.supp)
    (hxu : G.Adj x.1 u.1) :
    ((Finset.univ : Finset e.supp).filter fun w =>
      (crossRootCenterPair G hfree hde x y w).1 = u.1) =
        componentCrossNeighborFinset G e u := by
  classical
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    crossRootCenterPair, componentCrossNeighborFinset]
  constructor
  · intro hcenter
    have hspec := (crossCommonNeighbor_spec G hfree hde x w).2
    rw [hcenter] at hspec
    exact hspec.symm
  · intro huw
    symm
    exact eq_crossCommonNeighbor_of_adj G hfree hde x w
      ⟨hxu, huw.symm⟩

/-- Symmetric second-coordinate fiber description. -/
theorem crossRootCenterPair_snd_fiber_eq_componentCrossNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d e c : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x y : d.supp) (u : c.supp)
    (hyu : G.Adj y.1 u.1) :
    ((Finset.univ : Finset e.supp).filter fun w =>
      (crossRootCenterPair G hfree hde x y w).2 = u.1) =
        componentCrossNeighborFinset G e u := by
  classical
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    crossRootCenterPair, componentCrossNeighborFinset]
  constructor
  · intro hcenter
    have hspec := (crossCommonNeighbor_spec G hfree hde y w).2
    rw [hcenter] at hspec
    exact hspec.symm
  · intro huw
    symm
    exact eq_crossCommonNeighbor_of_adj G hfree hde y w
      ⟨hyu, huw.symm⟩

/-- In the normalized size-two regime every first-coordinate transition
fiber has degree two. -/
theorem binarySquare_regular_sizeTwo_crossRootCenterPair_fst_fiber_card_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ z, G.degree z = q) (hcard : Fintype.card V = q * q)
    {d e c : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (he : e.supp.ncard = q * 2)
    (x y : d.supp) (u : c.supp) (hxu : G.Adj x.1 u.1) :
    (((Finset.univ : Finset e.supp).filter fun w =>
      (crossRootCenterPair G hfree hde x y w).1 = u.1).card) = 2 := by
  rw [crossRootCenterPair_fst_fiber_eq_componentCrossNeighborFinset
    G hfree hde x y u hxu]
  rw [card_componentCrossNeighborFinset_eq_componentNeighborFinset]
  exact binarySquare_regular_sizeTwoPart_selector_card
    G hfree hq hreg hcard e he u.1

/-- In the normalized size-two regime every second-coordinate transition
fiber has degree two. -/
theorem binarySquare_regular_sizeTwo_crossRootCenterPair_snd_fiber_card_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ z, G.degree z = q) (hcard : Fintype.card V = q * q)
    {d e c : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (he : e.supp.ncard = q * 2)
    (x y : d.supp) (u : c.supp) (hyu : G.Adj y.1 u.1) :
    (((Finset.univ : Finset e.supp).filter fun w =>
      (crossRootCenterPair G hfree hde x y w).2 = u.1).card) = 2 := by
  rw [crossRootCenterPair_snd_fiber_eq_componentCrossNeighborFinset
    G hfree hde x y u hyu]
  rw [card_componentCrossNeighborFinset_eq_componentNeighborFinset]
  exact binarySquare_regular_sizeTwoPart_selector_card
    G hfree hq hreg hcard e he u.1

/-- Image-level version: every actual first center has degree two in the
transition graph contributed by a size-two target component. -/
theorem binarySquare_regular_sizeTwo_crossRootCenterPairFinset_fst_degree_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ z, G.degree z = q) (hcard : Fintype.card V = q * q)
    {d e c : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (he : e.supp.ncard = q * 2)
    (x y : d.supp)
    (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1)
    (u : c.supp) (hxu : G.Adj x.1 u.1) :
    ((crossRootCenterPairFinset G hfree hde x y).filter fun p =>
      p.1 = u.1).card = 2 := by
  classical
  let F := crossRootCenterPair G hfree hde x y
  let P := (Finset.univ : Finset e.supp).filter fun w => (F w).1 = u.1
  have himage :
      (crossRootCenterPairFinset G hfree hde x y).filter (fun p =>
        p.1 = u.1) = P.image F := by
    ext p
    simp only [crossRootCenterPairFinset, Finset.mem_filter,
      Finset.mem_image, Finset.mem_univ, true_and, P, F]
    constructor
    · rintro ⟨⟨w, _hw, rfl⟩, hfirst⟩
      exact ⟨w, hfirst, rfl⟩
    · rintro ⟨w, hfirst, rfl⟩
      exact ⟨⟨w, rfl⟩, hfirst⟩
  rw [himage, Finset.card_image_of_injective _
    (crossRootCenterPair_injective_of_secondOrderDefect_adj
      G hfree hde x y hxyD)]
  exact binarySquare_regular_sizeTwo_crossRootCenterPair_fst_fiber_card_eq_two
    G hfree hq hreg hcard hde he x y u hxu

/-- Symmetric image-level degree-two statement for second centers. -/
theorem binarySquare_regular_sizeTwo_crossRootCenterPairFinset_snd_degree_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ z, G.degree z = q) (hcard : Fintype.card V = q * q)
    {d e c : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (he : e.supp.ncard = q * 2)
    (x y : d.supp)
    (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1)
    (u : c.supp) (hyu : G.Adj y.1 u.1) :
    ((crossRootCenterPairFinset G hfree hde x y).filter fun p =>
      p.2 = u.1).card = 2 := by
  classical
  let F := crossRootCenterPair G hfree hde x y
  let P := (Finset.univ : Finset e.supp).filter fun w => (F w).2 = u.1
  have himage :
      (crossRootCenterPairFinset G hfree hde x y).filter (fun p =>
        p.2 = u.1) = P.image F := by
    ext p
    simp only [crossRootCenterPairFinset, Finset.mem_filter,
      Finset.mem_image, Finset.mem_univ, true_and, P, F]
    constructor
    · rintro ⟨⟨w, _hw, rfl⟩, hsecond⟩
      exact ⟨w, hsecond, rfl⟩
    · rintro ⟨w, hsecond, rfl⟩
      exact ⟨⟨w, rfl⟩, hsecond⟩
  rw [himage, Finset.card_image_of_injective _
    (crossRootCenterPair_injective_of_secondOrderDefect_adj
      G hfree hde x y hxyD)]
  exact binarySquare_regular_sizeTwo_crossRootCenterPair_snd_fiber_card_eq_two
    G hfree hq hreg hcard hde he x y u hyu

/-- After the three remote size-sixteen factors are removed at order 64, the
fourth factor still has degree two at every first center. -/
theorem orderSixtyFour_three_remoteTargets_complement_fst_degree_two
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ z, G.degree z = 8)
    {d e f g c : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (hdf : d ≠ f) (hdg : d ≠ g)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (he : e.supp.ncard = 16) (hf : f.supp.ncard = 16)
    (hg : g.supp.ncard = 16)
    (x y : d.supp)
    (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1)
    (u : c.supp) (hxu : G.Adj x.1 u.1) :
    ((crossRootCenterGrid G x.1 y.1 \ ((
        crossRootCenterPairFinset G hfree hde x y ∪
          crossRootCenterPairFinset G hfree hdf x y) ∪
        crossRootCenterPairFinset G hfree hdg x y)).filter fun p =>
      p.1 = u.1).card = 2 := by
  classical
  let Se := crossRootCenterPairFinset G hfree hde x y
  let Sf := crossRootCenterPairFinset G hfree hdf x y
  let Sg := crossRootCenterPairFinset G hfree hdg x y
  let U := (Se ∪ Sf) ∪ Sg
  let P := fun p : Fin 64 × Fin 64 => p.1 = u.1
  have hEF : Disjoint Se Sf :=
    crossRootCenterPairFinset_disjoint_of_target_ne
      G hfree hde hdf hef x y hxyD
  have hEG : Disjoint Se Sg :=
    crossRootCenterPairFinset_disjoint_of_target_ne
      G hfree hde hdg heg x y hxyD
  have hFG : Disjoint Sf Sg :=
    crossRootCenterPairFinset_disjoint_of_target_ne
      G hfree hdf hdg hfg x y hxyD
  have hEF' : Disjoint (Se.filter P) (Sf.filter P) :=
    hEF.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hEG' : Disjoint (Se.filter P) (Sg.filter P) :=
    hEG.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hFG' : Disjoint (Sf.filter P) (Sg.filter P) :=
    hFG.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hUfilter : (U.filter P).card = 6 := by
    rw [show U = (Se ∪ Sf) ∪ Sg by rfl, Finset.filter_union,
      Finset.filter_union,
      Finset.card_union_of_disjoint
        (Finset.disjoint_union_left.mpr ⟨hEG', hFG'⟩),
      Finset.card_union_of_disjoint hEF']
    rw [binarySquare_regular_sizeTwo_crossRootCenterPairFinset_fst_degree_two
        G hfree (q := 8) (by norm_num) hreg (by norm_num)
          hde he x y hxyD u hxu,
      binarySquare_regular_sizeTwo_crossRootCenterPairFinset_fst_degree_two
        G hfree (q := 8) (by norm_num) hreg (by norm_num)
          hdf hf x y hxyD u hxu,
      binarySquare_regular_sizeTwo_crossRootCenterPairFinset_fst_degree_two
        G hfree (q := 8) (by norm_num) hreg (by norm_num)
          hdg hg x y hxyD u hxu]
  have hUsub : U ⊆ crossRootCenterGrid G x.1 y.1 := by
    rw [show U = (Se ∪ Sf) ∪ Sg by rfl,
      Finset.union_subset_iff, Finset.union_subset_iff]
    exact ⟨⟨crossRootCenterPairFinset_subset_centerGrid G hfree hde x y,
      crossRootCenterPairFinset_subset_centerGrid G hfree hdf x y⟩,
      crossRootCenterPairFinset_subset_centerGrid G hfree hdg x y⟩
  have hUfilterSub : U.filter P ⊆
      (crossRootCenterGrid G x.1 y.1).filter P :=
    by
      intro p hp
      exact Finset.mem_filter.mpr
        ⟨hUsub (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
  have hgridFilter :
      ((crossRootCenterGrid G x.1 y.1).filter P).card = 8 := by
    have huMem : u.1 ∈ G.neighborFinset x.1 :=
      (G.mem_neighborFinset x.1 u.1).mpr hxu
    have heq : (crossRootCenterGrid G x.1 y.1).filter P =
        {u.1} ×ˢ G.neighborFinset y.1 := by
      ext p
      simp only [Finset.mem_filter, crossRootCenterGrid,
        Finset.mem_product, Finset.mem_singleton, P]
      constructor
      · rintro ⟨⟨_hp₁, hp₂⟩, hp₁⟩
        exact ⟨hp₁, hp₂⟩
      · rintro ⟨hp₁, hp₂⟩
        exact ⟨⟨by simpa [hp₁] using huMem, hp₂⟩, hp₁⟩
    rw [heq, Finset.card_product]
    simp [G.card_neighborFinset_eq_degree, hreg y.1]
  change ((crossRootCenterGrid G x.1 y.1 \ U).filter P).card = 2
  have hfilterSdiff :
      (crossRootCenterGrid G x.1 y.1 \ U).filter P =
        (crossRootCenterGrid G x.1 y.1).filter P \ U.filter P := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  rw [hfilterSdiff]
  rw [Finset.card_sdiff_of_subset hUfilterSub, hgridFilter, hUfilter]

/-- Symmetrically, the fourth factor has degree two at every second center. -/
theorem orderSixtyFour_three_remoteTargets_complement_snd_degree_two
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ z, G.degree z = 8)
    {d e f g c : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (hdf : d ≠ f) (hdg : d ≠ g)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (he : e.supp.ncard = 16) (hf : f.supp.ncard = 16)
    (hg : g.supp.ncard = 16)
    (x y : d.supp)
    (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1)
    (u : c.supp) (hyu : G.Adj y.1 u.1) :
    ((crossRootCenterGrid G x.1 y.1 \ ((
        crossRootCenterPairFinset G hfree hde x y ∪
          crossRootCenterPairFinset G hfree hdf x y) ∪
        crossRootCenterPairFinset G hfree hdg x y)).filter fun p =>
      p.2 = u.1).card = 2 := by
  classical
  let Se := crossRootCenterPairFinset G hfree hde x y
  let Sf := crossRootCenterPairFinset G hfree hdf x y
  let Sg := crossRootCenterPairFinset G hfree hdg x y
  let U := (Se ∪ Sf) ∪ Sg
  let P := fun p : Fin 64 × Fin 64 => p.2 = u.1
  have hEF : Disjoint Se Sf :=
    crossRootCenterPairFinset_disjoint_of_target_ne
      G hfree hde hdf hef x y hxyD
  have hEG : Disjoint Se Sg :=
    crossRootCenterPairFinset_disjoint_of_target_ne
      G hfree hde hdg heg x y hxyD
  have hFG : Disjoint Sf Sg :=
    crossRootCenterPairFinset_disjoint_of_target_ne
      G hfree hdf hdg hfg x y hxyD
  have hEF' : Disjoint (Se.filter P) (Sf.filter P) :=
    hEF.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hEG' : Disjoint (Se.filter P) (Sg.filter P) :=
    hEG.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hFG' : Disjoint (Sf.filter P) (Sg.filter P) :=
    hFG.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hUfilter : (U.filter P).card = 6 := by
    rw [show U = (Se ∪ Sf) ∪ Sg by rfl, Finset.filter_union,
      Finset.filter_union,
      Finset.card_union_of_disjoint
        (Finset.disjoint_union_left.mpr ⟨hEG', hFG'⟩),
      Finset.card_union_of_disjoint hEF']
    rw [binarySquare_regular_sizeTwo_crossRootCenterPairFinset_snd_degree_two
        G hfree (q := 8) (by norm_num) hreg (by norm_num)
          hde he x y hxyD u hyu,
      binarySquare_regular_sizeTwo_crossRootCenterPairFinset_snd_degree_two
        G hfree (q := 8) (by norm_num) hreg (by norm_num)
          hdf hf x y hxyD u hyu,
      binarySquare_regular_sizeTwo_crossRootCenterPairFinset_snd_degree_two
        G hfree (q := 8) (by norm_num) hreg (by norm_num)
          hdg hg x y hxyD u hyu]
  have hUsub : U ⊆ crossRootCenterGrid G x.1 y.1 := by
    rw [show U = (Se ∪ Sf) ∪ Sg by rfl,
      Finset.union_subset_iff, Finset.union_subset_iff]
    exact ⟨⟨crossRootCenterPairFinset_subset_centerGrid G hfree hde x y,
      crossRootCenterPairFinset_subset_centerGrid G hfree hdf x y⟩,
      crossRootCenterPairFinset_subset_centerGrid G hfree hdg x y⟩
  have hUfilterSub : U.filter P ⊆
      (crossRootCenterGrid G x.1 y.1).filter P := by
    intro p hp
    exact Finset.mem_filter.mpr
      ⟨hUsub (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
  have hgridFilter :
      ((crossRootCenterGrid G x.1 y.1).filter P).card = 8 := by
    have huMem : u.1 ∈ G.neighborFinset y.1 :=
      (G.mem_neighborFinset y.1 u.1).mpr hyu
    have heq : (crossRootCenterGrid G x.1 y.1).filter P =
        G.neighborFinset x.1 ×ˢ {u.1} := by
      ext p
      simp only [Finset.mem_filter, crossRootCenterGrid,
        Finset.mem_product, Finset.mem_singleton, P]
      constructor
      · rintro ⟨⟨hp₁, _hp₂⟩, hp₂⟩
        exact ⟨hp₁, hp₂⟩
      · rintro ⟨hp₁, hp₂⟩
        exact ⟨⟨hp₁, by simpa [hp₂] using huMem⟩, hp₂⟩
    rw [heq, Finset.card_product]
    simp [G.card_neighborFinset_eq_degree, hreg x.1]
  change ((crossRootCenterGrid G x.1 y.1 \ U).filter P).card = 2
  have hfilterSdiff :
      (crossRootCenterGrid G x.1 y.1 \ U).filter P =
        (crossRootCenterGrid G x.1 y.1).filter P \ U.filter P := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  rw [hfilterSdiff]
  rw [Finset.card_sdiff_of_subset hUfilterSub, hgridFilter, hUfilter]

end

end Erdos85
