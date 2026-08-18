import Proofs.Erdos85BinarySquareTwoOwnerDefectEdgeResidue
import Proofs.Erdos85BinarySquareMixedOwnerRectangleRouting
import Proofs.Erdos85RoutingOwnerRainbowHexagon
import Proofs.Erdos85BinarySquareCenterGridOperator

/-! # Same-owner middles inject into the center grid -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A canonical owner-component common neighbor, with an irrelevant fallback
off owner edges. -/
def componentOwnerCenter
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent]
    (owner : D.ConnectedComponent) (x z : V) : V :=
  if h : (componentOwnerGraph G D owner).Adj x z then
    (Classical.choose
      (componentOwnerGraph_adj_exists_owner_commonNeighbor G D owner h)).1
  else x

theorem componentOwnerCenter_spec
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent]
    (owner : D.ConnectedComponent) {x z : V}
    (h : (componentOwnerGraph G D owner).Adj x z) :
    componentOwnerCenter G D owner x z ∈ owner.supp ∧
      G.Adj x (componentOwnerCenter G D owner x z) ∧
      G.Adj z (componentOwnerCenter G D owner x z) := by
  rw [componentOwnerCenter, dif_pos h]
  let u := Classical.choose
    (componentOwnerGraph_adj_exists_owner_commonNeighbor G D owner h)
  have hu := Classical.choose_spec
    (componentOwnerGraph_adj_exists_owner_commonNeighbor G D owner h)
  exact ⟨u.2, hu.1, hu.2⟩

theorem componentOwnerCenter_eq_of_commonNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (D : SimpleGraph V) [DecidableEq D.ConnectedComponent]
    (owner : D.ConnectedComponent) {x z u : V}
    (h : (componentOwnerGraph G D owner).Adj x z)
    (hxu : G.Adj x u) (hzu : G.Adj z u) :
    componentOwnerCenter G D owner x z = u := by
  have hc := componentOwnerCenter_spec G D owner h
  by_contra hne
  apply hfree
  exact containsC4_of_two_common hne h.ne hc.2.1 hxu hc.2.2 hzu

/-- The nondefect part of the owner-selector center grid. -/
def sameOwnerNondefectCenterPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (owner : (secondOrderDefectGraph G).ConnectedComponent)
    (x y : V) : Finset (V × V) :=
  ((componentNeighborFinset G (secondOrderDefectGraph G) owner x) ×ˢ
    componentNeighborFinset G (secondOrderDefectGraph G) owner y).filter
      fun p => ¬ (secondOrderDefectGraph G).Adj p.1 p.2

/-- The defect cells in an owner-selector center grid. -/
def sameOwnerDefectCenterPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (owner : (secondOrderDefectGraph G).ConnectedComponent)
    (x y : V) : Finset (V × V) :=
  ((componentNeighborFinset G (secondOrderDefectGraph G) owner x) ×ˢ
    componentNeighborFinset G (secondOrderDefectGraph G) owner y).filter
      fun p => (secondOrderDefectGraph G).Adj p.1 p.2

/-- Exact center-grid realization: same-owner middles are in bijection with
the nondefect pairs in the two owner selectors. -/
theorem sameOwner_coloredTwoStepMiddles_card_eq_nondefectCenterPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (owner : (secondOrderDefectGraph G).ConnectedComponent)
    {x y : V} (hxyD : (secondOrderDefectGraph G).Adj x y) :
    (coloredTwoStepMiddles
      (componentOwnerGraph G (secondOrderDefectGraph G) owner)
      (componentOwnerGraph G (secondOrderDefectGraph G) owner) x y).card =
      (sameOwnerNondefectCenterPairs G owner x y).card := by
  classical
  let D := secondOrderDefectGraph G
  let O := componentOwnerGraph G D owner
  let S := coloredTwoStepMiddles O O x y
  let T := sameOwnerNondefectCenterPairs G owner x y
  let f : V → V × V := fun z =>
    (componentOwnerCenter G D owner x z,
      componentOwnerCenter G D owner y z)
  apply Finset.card_bij (fun z _ => f z)
  · intro z hz
    have hz' := (Finset.mem_filter.mp hz).2
    have hu := componentOwnerCenter_spec G D owner hz'.1
    have hv := componentOwnerCenter_spec G D owner hz'.2.symm
    have huv : (f z).1 ≠ (f z).2 := by
      intro huv
      have huv' : componentOwnerCenter G D owner x z =
          componentOwnerCenter G D owner y z := by simpa [f] using huv
      apply (not_secondOrderDefect_adj_of_commonNeighbor G hfree hxyD.ne
        hu.2.1 (huv' ▸ hv.2.1)) hxyD
    have hnotD := not_secondOrderDefect_adj_of_commonNeighbor
      G hfree huv hu.2.2.symm hv.2.2.symm
    apply Finset.mem_filter.mpr
    refine ⟨?_, hnotD⟩
    rw [Finset.mem_product]
    constructor
    · rw [componentNeighborFinset]
      exact Finset.mem_filter.mpr
        ⟨(G.mem_neighborFinset x _).mpr hu.2.1,
          (ConnectedComponent.mem_supp_iff owner _).mp hu.1⟩
    · rw [componentNeighborFinset]
      exact Finset.mem_filter.mpr
        ⟨(G.mem_neighborFinset y _).mpr hv.2.1,
          (ConnectedComponent.mem_supp_iff owner _).mp hv.1⟩
  · intro z₁ hz₁ z₂ hz₂ hpair
    have hz₁' := (Finset.mem_filter.mp hz₁).2
    have hz₂' := (Finset.mem_filter.mp hz₂).2
    have hu₁ := componentOwnerCenter_spec G D owner hz₁'.1
    have hv₁ := componentOwnerCenter_spec G D owner hz₁'.2.symm
    have hu₂ := componentOwnerCenter_spec G D owner hz₂'.1
    have hv₂ := componentOwnerCenter_spec G D owner hz₂'.2.symm
    have huEq : componentOwnerCenter G D owner x z₁ =
        componentOwnerCenter G D owner x z₂ := by
      simpa [f] using congrArg Prod.fst hpair
    have hvEq : componentOwnerCenter G D owner y z₁ =
        componentOwnerCenter G D owner y z₂ := by
      simpa [f] using congrArg Prod.snd hpair
    rw [← huEq] at hu₂
    rw [← hvEq] at hv₂
    have huv : (f z₁).1 ≠ (f z₁).2 := by
      intro huv
      have huv' : componentOwnerCenter G D owner x z₁ =
          componentOwnerCenter G D owner y z₁ := by simpa [f] using huv
      apply (not_secondOrderDefect_adj_of_commonNeighbor G hfree hxyD.ne
        hu₁.2.1 (huv' ▸ hv₁.2.1)) hxyD
    by_contra hne
    apply hfree
    exact containsC4_of_two_common huv hne
      hu₁.2.2 hv₁.2.2 hu₂.2.2 hv₂.2.2
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpProd := Finset.mem_product.mp hp'.1
    have hxp : G.Adj x p.1 := by
      exact (G.mem_neighborFinset x p.1).mp
        (Finset.mem_filter.mp hpProd.1).1
    have hyp : G.Adj y p.2 := by
      exact (G.mem_neighborFinset y p.2).mp
        (Finset.mem_filter.mp hpProd.2).1
    have hp1mem : p.1 ∈ owner.supp :=
      (ConnectedComponent.mem_supp_iff owner p.1).mpr
        (Finset.mem_filter.mp hpProd.1).2
    have hp2mem : p.2 ∈ owner.supp :=
      (ConnectedComponent.mem_supp_iff owner p.2).mpr
        (Finset.mem_filter.mp hpProd.2).2
    let d := D.connectedComponentMk x
    let xs : d.supp := ⟨x, ConnectedComponent.connectedComponentMk_mem⟩
    let ys : d.supp := ⟨y, (ConnectedComponent.mem_supp_iff d y).mpr
      (ConnectedComponent.connectedComponentMk_eq_of_adj hxyD.symm)⟩
    have hpGrid : p ∈ crossRootCenterGrid G x y := by
      rw [crossRootCenterGrid, Finset.mem_product]
      exact ⟨(G.mem_neighborFinset x p.1).mpr hxp,
        (G.mem_neighborFinset y p.2).mpr hyp⟩
    obtain hDp | ⟨z, hpz⟩ := centerGrid_pair_defect_or_exists_commonNeighbor
      G hfree xs ys hxyD hpGrid
    · exact False.elim (hp'.2 hDp)
    · have hzx : z ≠ x := by
        intro h
        subst z
        exact (not_secondOrderDefect_adj_of_commonNeighbor G hfree hxyD.ne
          hpz.2.symm hyp) hxyD
      have hzy : z ≠ y := by
        intro h
        subst z
        exact (not_secondOrderDefect_adj_of_commonNeighbor G hfree hxyD.ne
          hxp hpz.1.symm) hxyD
      have hOxz := componentOwnerGraph_adj_of_commonNeighbor_mem_owner
        G D owner hzx.symm hp1mem hxp hpz.1.symm
      have hOzy := componentOwnerGraph_adj_of_commonNeighbor_mem_owner
        G D owner hzy hp2mem hpz.2.symm hyp
      refine ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hOxz, hOzy⟩, ?_⟩
      apply Prod.ext
      · exact componentOwnerCenter_eq_of_commonNeighbor
          G hfree D owner hOxz hxp hpz.1.symm
      · exact componentOwnerCenter_eq_of_commonNeighbor
          G hfree D owner hOzy.symm hyp hpz.2.symm

/-- Exact complement identity: the same-owner middles and the defect cells
partition the full owner-selector center grid. -/
theorem sameOwner_coloredTwoStepMiddles_card_add_defectCenterPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (owner : (secondOrderDefectGraph G).ConnectedComponent)
    {x y : V} (hxyD : (secondOrderDefectGraph G).Adj x y) :
    (coloredTwoStepMiddles
      (componentOwnerGraph G (secondOrderDefectGraph G) owner)
      (componentOwnerGraph G (secondOrderDefectGraph G) owner) x y).card +
      (sameOwnerDefectCenterPairs G owner x y).card =
      (componentNeighborFinset G (secondOrderDefectGraph G) owner x).card *
        (componentNeighborFinset G (secondOrderDefectGraph G) owner y).card := by
  rw [sameOwner_coloredTwoStepMiddles_card_eq_nondefectCenterPairs
    G hfree owner hxyD]
  simpa [sameOwnerNondefectCenterPairs, sameOwnerDefectCenterPairs,
    Finset.card_product] using
    (Finset.card_filter_add_card_filter_not
      (s := (componentNeighborFinset G (secondOrderDefectGraph G) owner x) ×ˢ
        componentNeighborFinset G (secondOrderDefectGraph G) owner y)
      (fun p : V × V => ¬ (secondOrderDefectGraph G).Adj p.1 p.2))

/-- With exactly two defect components, their two diagonal selector blocks
partition every defect cell of the ambient cross-root center grid. -/
theorem twoComponents_union_sameOwnerDefectCenterPairs_eq_crossRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (a b : (secondOrderDefectGraph G).ConnectedComponent) (hab : a ≠ b)
    (x y : V) :
    sameOwnerDefectCenterPairs G a x y ∪
        sameOwnerDefectCenterPairs G b x y =
      crossRootDefectCenterPairs G x y := by
  classical
  let D := secondOrderDefectGraph G
  have hexhaust (c : D.ConnectedComponent) : c = a ∨ c = b := by
    by_contra hc
    simp only [not_or] at hc
    have hsub : ({a, b, c} : Finset D.ConnectedComponent) ⊆ Finset.univ :=
      Finset.subset_univ _
    have hle := Finset.card_le_card hsub
    have hthree : ({a, b, c} : Finset D.ConnectedComponent).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hab, Ne.symm hc.1⟩),
        Finset.card_insert_of_notMem (by
          simpa only [Finset.mem_singleton] using Ne.symm hc.2)]
      rfl
    rw [hthree, Finset.card_univ, hcount] at hle
    omega
  ext p
  constructor
  · intro hp
    rw [Finset.mem_union] at hp
    rcases hp with hp | hp
    · have hp' := Finset.mem_filter.mp hp
      have hprod := Finset.mem_product.mp hp'.1
      apply Finset.mem_filter.mpr
      refine ⟨?_, hp'.2⟩
      rw [crossRootCenterGrid, Finset.mem_product]
      exact ⟨(Finset.mem_filter.mp hprod.1).1,
        (Finset.mem_filter.mp hprod.2).1⟩
    · have hp' := Finset.mem_filter.mp hp
      have hprod := Finset.mem_product.mp hp'.1
      apply Finset.mem_filter.mpr
      refine ⟨?_, hp'.2⟩
      rw [crossRootCenterGrid, Finset.mem_product]
      exact ⟨(Finset.mem_filter.mp hprod.1).1,
        (Finset.mem_filter.mp hprod.2).1⟩
  · intro hp
    have hp' := Finset.mem_filter.mp hp
    have hgrid := Finset.mem_product.mp hp'.1
    have hcomp : D.connectedComponentMk p.2 = D.connectedComponentMk p.1 :=
      ConnectedComponent.connectedComponentMk_eq_of_adj hp'.2.symm
    rcases hexhaust (D.connectedComponentMk p.1) with ha | hb
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hp'.2⟩
      · exact Finset.mem_filter.mpr ⟨hgrid.1, ha⟩
      · exact Finset.mem_filter.mpr ⟨hgrid.2, hcomp.trans ha⟩
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hp'.2⟩
      · exact Finset.mem_filter.mpr ⟨hgrid.1, hb⟩
      · exact Finset.mem_filter.mpr ⟨hgrid.2, hcomp.trans hb⟩

/-- Selector defect blocks belonging to distinct components are disjoint. -/
theorem sameOwnerDefectCenterPairs_disjoint_of_owner_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    {a b : (secondOrderDefectGraph G).ConnectedComponent} (hab : a ≠ b)
    (x y : V) :
    Disjoint (sameOwnerDefectCenterPairs G a x y)
      (sameOwnerDefectCenterPairs G b x y) := by
  rw [Finset.disjoint_left]
  intro p hpa hpb
  have hpaProd := Finset.mem_product.mp (Finset.mem_filter.mp hpa).1
  have hpbProd := Finset.mem_product.mp (Finset.mem_filter.mp hpb).1
  have hpaComp := (Finset.mem_filter.mp hpaProd.1).2
  have hpbComp := (Finset.mem_filter.mp hpbProd.1).2
  exact hab (hpaComp.symm.trans hpbComp)

/-- At a defect edge, same-owner middles inject into the product of the two
owner selectors. -/
theorem sameOwner_coloredTwoStepMiddles_card_le_centerGrid
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (owner : (secondOrderDefectGraph G).ConnectedComponent)
    {x y : V} (hxyD : (secondOrderDefectGraph G).Adj x y) :
    (coloredTwoStepMiddles
      (componentOwnerGraph G (secondOrderDefectGraph G) owner)
      (componentOwnerGraph G (secondOrderDefectGraph G) owner) x y).card ≤
      (componentNeighborFinset G (secondOrderDefectGraph G) owner x).card *
        (componentNeighborFinset G (secondOrderDefectGraph G) owner y).card := by
  classical
  let D := secondOrderDefectGraph G
  let O := componentOwnerGraph G D owner
  let S := coloredTwoStepMiddles O O x y
  let X := componentNeighborFinset G D owner x
  let Y := componentNeighborFinset G D owner y
  let f : {z // z ∈ S} → V × V := fun z =>
    (componentOwnerCenter G D owner x z.1,
      componentOwnerCenter G D owner y z.1)
  have hfmem : ∀ z : {z // z ∈ S}, f z ∈ X ×ˢ Y := by
    intro z
    have hz := (Finset.mem_filter.mp z.2).2
    have hu := componentOwnerCenter_spec G D owner hz.1
    have hv := componentOwnerCenter_spec G D owner hz.2.symm
    rw [Finset.mem_product]
    constructor
    · change componentOwnerCenter G D owner x z.1 ∈
        componentNeighborFinset G D owner x
      rw [componentNeighborFinset]
      exact Finset.mem_filter.mpr
        ⟨(G.mem_neighborFinset x _).mpr hu.2.1,
          (ConnectedComponent.mem_supp_iff owner _).mp hu.1⟩
    · change componentOwnerCenter G D owner y z.1 ∈
        componentNeighborFinset G D owner y
      rw [componentNeighborFinset]
      exact Finset.mem_filter.mpr
        ⟨(G.mem_neighborFinset y _).mpr hv.2.1,
          (ConnectedComponent.mem_supp_iff owner _).mp hv.1⟩
  have hfinj : Function.Injective f := by
    intro z₁ z₂ hpair
    have hz₁ := (Finset.mem_filter.mp z₁.2).2
    have hz₂ := (Finset.mem_filter.mp z₂.2).2
    let u := componentOwnerCenter G D owner x z₁.1
    let v := componentOwnerCenter G D owner y z₁.1
    have hu₁ := componentOwnerCenter_spec G D owner hz₁.1
    have hv₁ := componentOwnerCenter_spec G D owner hz₁.2.symm
    have huEq : componentOwnerCenter G D owner x z₁.1 =
        componentOwnerCenter G D owner x z₂.1 := congrArg Prod.fst hpair
    have hvEq : componentOwnerCenter G D owner y z₁.1 =
        componentOwnerCenter G D owner y z₂.1 := congrArg Prod.snd hpair
    have hu₂ := componentOwnerCenter_spec G D owner hz₂.1
    have hv₂ := componentOwnerCenter_spec G D owner hz₂.2.symm
    rw [← huEq] at hu₂
    rw [← hvEq] at hv₂
    have huv : u ≠ v := by
      intro huv
      apply (componentOwnerGraph_adj_not_secondOrderDefect_adj G hfree owner ?_)
        hxyD
      exact componentOwnerGraph_adj_of_commonNeighbor_mem_owner
        G D owner hxyD.ne hu₁.1 hu₁.2.1 (by simpa [u, v, huv] using hv₁.2.1)
    apply Subtype.ext
    by_contra hzNe
    apply hfree
    exact containsC4_of_two_common huv hzNe
      hu₁.2.2 hv₁.2.2 hu₂.2.2 hv₂.2.2
  have himage : S.attach.image f ⊆ X ×ˢ Y := by
    intro p hp
    obtain ⟨z, _hz, rfl⟩ := Finset.mem_image.mp hp
    exact hfmem z
  calc
    S.card = S.attach.card := by simp
    _ = (S.attach.image f).card :=
      (Finset.card_image_of_injective _ hfinj).symm
    _ ≤ (X ×ˢ Y).card := Finset.card_le_card himage
    _ = X.card * Y.card := Finset.card_product X Y

/-- In a normalized component of size `qm`, the same-owner middle capacity
at every defect edge is at most `m²`. -/
theorem binarySquare_regular_sameOwner_defectEdge_card_le_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (owner : (secondOrderDefectGraph G).ConnectedComponent) {m : ℕ}
    (howner : owner.supp.ncard = q * m)
    {x y : V} (hxyD : (secondOrderDefectGraph G).Adj x y) :
    (coloredTwoStepMiddles
      (componentOwnerGraph G (secondOrderDefectGraph G) owner)
      (componentOwnerGraph G (secondOrderDefectGraph G) owner) x y).card ≤
        m * m := by
  have hsel (z : V) :
      (componentNeighborFinset G (secondOrderDefectGraph G) owner z).card = m := by
    have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq hreg hcard
      ((secondOrderDefectGraph G).connectedComponentMk z) owner (x := z) (by rfl)
    rw [howner] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul
  simpa [hsel x, hsel y] using
    (sameOwner_coloredTwoStepMiddles_card_le_centerGrid
      G hfree owner hxyD)

/-- In a normalized component of size `qm`, the exact complement of the
same-owner middles inside the `m × m` center grid is its defect-cell count. -/
theorem binarySquare_regular_sameOwner_defectEdge_card_add_defectCells_eq_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (owner : (secondOrderDefectGraph G).ConnectedComponent) {m : ℕ}
    (howner : owner.supp.ncard = q * m)
    {x y : V} (hxyD : (secondOrderDefectGraph G).Adj x y) :
    (coloredTwoStepMiddles
      (componentOwnerGraph G (secondOrderDefectGraph G) owner)
      (componentOwnerGraph G (secondOrderDefectGraph G) owner) x y).card +
      (sameOwnerDefectCenterPairs G owner x y).card = m * m := by
  have hsel (z : V) :
      (componentNeighborFinset G (secondOrderDefectGraph G) owner z).card = m := by
    have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq hreg hcard
      ((secondOrderDefectGraph G).connectedComponentMk z) owner (x := z) (by rfl)
    rw [howner] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul
  simpa [hsel x, hsel y] using
    (sameOwner_coloredTwoStepMiddles_card_add_defectCenterPairs
      G hfree owner hxyD)

/-- Exact two-owner center-grid ledger at a defect edge.  The same-owner
middle counts plus all defect cells between the ambient root neighborhoods
equal the sum of the two diagonal selector-grid areas. -/
theorem binarySquare_regular_twoComponents_defectEdge_exact_centerGrid_ledger
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (a b : (secondOrderDefectGraph G).ConnectedComponent) (hab : a ≠ b)
    {m_a m_b : ℕ} (ha : a.supp.ncard = q * m_a)
    (hb : b.supp.ncard = q * m_b)
    {x y : V} (hxyD : (secondOrderDefectGraph G).Adj x y) :
    (coloredTwoStepMiddles
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) a) x y).card +
    (coloredTwoStepMiddles
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) b) x y).card +
      (crossRootDefectCenterPairs G x y).card =
        m_a * m_a + m_b * m_b := by
  have haExact :=
    binarySquare_regular_sameOwner_defectEdge_card_add_defectCells_eq_sq
      G hfree hq hreg hcard a ha hxyD
  have hbExact :=
    binarySquare_regular_sameOwner_defectEdge_card_add_defectCells_eq_sq
      G hfree hq hreg hcard b hb hxyD
  have hunion := twoComponents_union_sameOwnerDefectCenterPairs_eq_crossRoot
    G hcount a b hab x y
  have hdis := sameOwnerDefectCenterPairs_disjoint_of_owner_ne
    G hab x y
  have hdefect :
      (sameOwnerDefectCenterPairs G a x y).card +
          (sameOwnerDefectCenterPairs G b x y).card =
        (crossRootDefectCenterPairs G x y).card := by
    rw [← Finset.card_union_of_disjoint hdis, hunion]
  omega

/-- Operator form of the exact two-owner ledger.  Consequently the total
same-owner closing count on a defect edge depends only on its defect
codegree (the corresponding entry of `D²`). -/
theorem binarySquare_regular_twoComponents_defectEdge_sameOwner_add_codegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q r : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDreg : ∀ x, (secondOrderDefectGraph G).degree x = r)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (a b : (secondOrderDefectGraph G).ConnectedComponent) (hab : a ≠ b)
    {m_a m_b : ℕ} (ha : a.supp.ncard = q * m_a)
    (hb : b.supp.ncard = q * m_b)
    {x y : V} (hxyD : (secondOrderDefectGraph G).Adj x y) :
    ((coloredTwoStepMiddles
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) a) x y).card : ℤ) +
    ((coloredTwoStepMiddles
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) b) x y).card : ℤ) +
    (q - 1 : ℤ) + r -
      ((secondOrderDefectGraph G).adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ) x y =
      (m_a * m_a + m_b * m_b : ℕ) := by
  have hledger :=
    binarySquare_regular_twoComponents_defectEdge_exact_centerGrid_ledger
      G hfree hq hreg hcard hcount a b hab ha hb hxyD
  have hcross : ((crossRootDefectCenterPairs G x y).card : ℤ) =
      (q - 1 : ℤ) + r -
        ((secondOrderDefectGraph G).adjMatrix ℤ *
          (secondOrderDefectGraph G).adjMatrix ℤ) x y := by
    rw [← adj_defect_adj_apply_eq_card_crossRootDefectCenterPairs G x y,
      adj_defect_adj_apply_eq_degree_terms_sub_defect_sq
        G hfree hreg hDreg x y]
    simp [SimpleGraph.adjMatrix_apply, hxyD]
  have hledgerZ :
      ((coloredTwoStepMiddles
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a) x y).card : ℤ) +
      ((coloredTwoStepMiddles
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) x y).card : ℤ) +
      ((crossRootDefectCenterPairs G x y).card : ℤ) =
        (m_a * m_a + m_b * m_b : ℕ) := by
    exact_mod_cast hledger
  rw [hcross] at hledgerZ
  omega

/-- Intrinsic q-generic form: on every defect edge, the total same-owner
closing count plus `2(q-1)` minus the defect codegree is constant. -/
theorem binarySquare_regular_twoComponents_defectEdge_sameOwner_codegree_constant
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (a b : (secondOrderDefectGraph G).ConnectedComponent) (hab : a ≠ b)
    {m_a m_b : ℕ} (ha : a.supp.ncard = q * m_a)
    (hb : b.supp.ncard = q * m_b)
    {x y : V} (hxyD : (secondOrderDefectGraph G).Adj x y) :
    ((coloredTwoStepMiddles
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) a) x y).card : ℤ) +
    ((coloredTwoStepMiddles
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) b) x y).card : ℤ) +
    2 * (q - 1 : ℤ) -
      ((secondOrderDefectGraph G).adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ) x y =
      (m_a * m_a + m_b * m_b : ℕ) := by
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDreg : ∀ z, (secondOrderDefectGraph G).degree z = q - 1 := by
    intro z
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus z
    change (secondOrderDefectGraph G).degree z = (q - 3) + 2 at h
    omega
  have h :=
    binarySquare_regular_twoComponents_defectEdge_sameOwner_add_codegree
      G hfree hq hreg hcard hDreg hcount a b hab ha hb hxyD
  norm_num at h ⊢
  omega

/-- The two-owner defect-edge sandwich: certified same-owner pressure is
bounded above by the sum of the two center-grid capacities. -/
theorem binarySquare_regular_twoComponents_defectEdge_sameOwner_sandwich
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (a b : (secondOrderDefectGraph G).ConnectedComponent) (hab : a ≠ b)
    {m_a m_b : ℕ} (ha : a.supp.ncard = q * m_a)
    (hb : b.supp.ncard = q * m_b)
    {x y : V} (hxyD : (secondOrderDefectGraph G).Adj x y) :
    (q * q - 2 * (q - 1)) - 2 * m_a * m_b ≤ m_a * m_a + m_b * m_b := by
  let A := componentOwnerGraph G (secondOrderDefectGraph G) a
  let B := componentOwnerGraph G (secondOrderDefectGraph G) b
  let AA := coloredTwoStepMiddles A A x y
  let BB := coloredTwoStepMiddles B B x y
  have hlo : (q * q - 2 * (q - 1)) - 2 * m_a * m_b ≤
      (AA ∪ BB).card := by
    exact binarySquare_regular_twoComponents_defectEdge_sameOwner_card_lower
      G hfree hq hreg hcard hcount a b hab ha hb hxyD
  have hAA : AA.card ≤ m_a * m_a := by
    exact binarySquare_regular_sameOwner_defectEdge_card_le_sq
      G hfree hq hreg hcard a ha hxyD
  have hBB : BB.card ≤ m_b * m_b := by
    exact binarySquare_regular_sameOwner_defectEdge_card_le_sq
      G hfree hq hreg hcard b hb hxyD
  have hdis : Disjoint AA BB := by
    exact coloredTwoStepMiddles_disjoint_of_orderedOwners_ne
      G hfree a a b b (by simpa using hab) x y
  rw [Finset.card_union_of_disjoint hdis] at hlo
  omega

end

end Erdos85
