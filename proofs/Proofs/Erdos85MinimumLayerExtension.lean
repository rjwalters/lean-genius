import Proofs.Erdos85MinimumLayerDescent
import Proofs.Erdos85ConflictDefectDuality

/-!
# Rigidity of an exact-boundary extension

For the exact-boundary graph induced on the minimum defect layer, the
ambient defect relation restricts to the child's own defect relation.  This
is the key input for showing that distinct child vertices have disjoint
external neighborhoods.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- The ambient second-order defect graph, restricted to the minimum layer. -/
def minimumLayerParentDefect {V : Type*} (D : SimpleGraph V)
    (c₀ : D.ConnectedComponent) :
    SimpleGraph (minimumLayerVertex D c₀) :=
  D.comap minimumLayerVertexValue

noncomputable instance minimumLayerVertexDecidableEq
    {V : Type*} (D : SimpleGraph V) (c₀ : D.ConnectedComponent) :
    DecidableEq (minimumLayerVertex D c₀) := Classical.decEq _

noncomputable instance minimumLayerParentDefectDecidableRel
    {V : Type*} (D : SimpleGraph V) [DecidableRel D.Adj]
    (c₀ : D.ConnectedComponent) :
    DecidableRel (minimumLayerParentDefect D c₀).Adj := Classical.decRel _

/-- Every ambient defect neighbor of a minimum-layer vertex remains in the
same minimum component. -/
def minimumLayerParentDefectNeighborEquiv
    {V : Type*} (D : SimpleGraph V) (c₀ : D.ConnectedComponent)
    (x : minimumLayerVertex D c₀) :
    (minimumLayerParentDefect D c₀).neighborSet x ≃
      D.neighborSet x.2.1 where
  toFun y := ⟨y.1.2.1, y.2⟩
  invFun y := by
    have hcomp : D.connectedComponentMk y.1 = x.1.1 :=
      (ConnectedComponent.connectedComponentMk_eq_of_adj y.2.symm).trans
        ((ConnectedComponent.mem_supp_iff x.1.1 x.2.1).mp x.2.2)
    have hymem : y.1 ∈ x.1.1.supp :=
      (ConnectedComponent.mem_supp_iff x.1.1 y.1).mpr hcomp
    exact ⟨⟨x.1, ⟨y.1, hymem⟩⟩, y.2⟩
  left_inv y := by
    apply Subtype.ext
    apply minimumLayerVertexValue_injective
    rfl
  right_inv y := Subtype.ext rfl

/-- Restricting a regular defect graph to a union of its components
preserves every vertex degree. -/
theorem minimumLayerParentDefect_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (k : ℕ) (hreg : ∀ v : V, D.degree v = k)
    (c₀ : D.ConnectedComponent) (x : minimumLayerVertex D c₀) :
    (minimumLayerParentDefect D c₀).degree x = k := by
  classical
  rw [← (minimumLayerParentDefect D c₀).card_neighborSet_eq_degree,
    Fintype.card_congr (minimumLayerParentDefectNeighborEquiv D c₀ x),
    D.card_neighborSet_eq_degree, hreg]

/-- A parent defect edge inside the minimum layer is also a defect edge for
the induced child graph. -/
theorem minimumLayerParentDefect_le_childDefect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hfreeChild : ¬ containsC4
      (minimumLayerVertex (secondOrderDefectGraph G) c₀)
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀)) :
    minimumLayerParentDefect (secondOrderDefectGraph G) c₀ ≤
      secondOrderDefectGraph
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀) := by
  classical
  intro x y hP
  let H := minimumLayerGraph G (secondOrderDefectGraph G) c₀
  have hxyValue : x.2.1 ≠ y.2.1 :=
    (secondOrderDefectGraph G).ne_of_adj hP
  have hxy : x ≠ y := fun h ↦ hxyValue (congrArg minimumLayerVertexValue h)
  have hparent := card_common_eq_if_secondOrderDefect
    G hfree x.2.1 y.2.1 hxyValue
  have hyMem : y.2.1 ∈ (secondOrderDefectGraph G).neighborFinset x.2.1 :=
    ((secondOrderDefectGraph G).mem_neighborFinset x.2.1 y.2.1).mpr hP
  rw [if_pos hyMem] at hparent
  have hchildEmpty :
      H.neighborFinset x ∩ H.neighborFinset y = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨hzx, hzy⟩ := Finset.mem_inter.mp hz
    have hzParent : z.2.1 ∈
        G.neighborFinset x.2.1 ∩ G.neighborFinset y.2.1 := by
      exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset x.2.1 z.2.1).mpr
            ((H.mem_neighborFinset x z).mp hzx),
          (G.mem_neighborFinset y.2.1 z.2.1).mpr
            ((H.mem_neighborFinset y z).mp hzy)⟩
    have hne := Finset.card_ne_zero.mpr ⟨z.2.1, hzParent⟩
    exact hne hparent
  rw [← commonNeighborConflict_compl_eq_secondOrderDefectGraph H hfreeChild,
    SimpleGraph.compl_adj, commonNeighborConflict_adj_iff]
  exact ⟨hxy, by simp [hchildEmpty]⟩

/-- Since both defect graphs are two-regular, the preceding inclusion is an
equality.  In particular, formation of the second-order defect graph
commutes with passage to the minimum-layer child. -/
theorem minimumLayerParentDefect_eq_childDefect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3) :
    minimumLayerParentDefect (secondOrderDefectGraph G) c₀ =
      secondOrderDefectGraph
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀) := by
  classical
  let H := minimumLayerGraph G (secondOrderDefectGraph G) c₀
  let P := minimumLayerParentDefect (secondOrderDefectGraph G) c₀
  let C := secondOrderDefectGraph H
  have hfreeChild : ¬ containsC4 _ H :=
    minimumLayerGraph_c4Free G (secondOrderDefectGraph G) c₀ hfree
  have hle : P ≤ C :=
    minimumLayerParentDefect_le_childDefect G hfree c₀ hfreeChild
  have hdegP : ∀ x, P.degree x = 2 := by
    intro x
    exact minimumLayerParentDefect_degree (secondOrderDefectGraph G) 2
      (secondOrderDefectGraph_degree_eq_two G hfree hd heven hmin hcard) c₀ x
  have hdegC : ∀ x, C.degree x = 2 := by
    intro x
    apply secondOrderDefectGraph_degree_eq_excess_add_two
      H hfreeChild hregChild (e := 0)
    simpa using hcardChild
  ext x y
  constructor
  · intro hP
    exact hle hP
  · intro hC
    have hsub : P.neighborFinset x ⊆ C.neighborFinset x := by
      intro z hz
      exact (C.mem_neighborFinset x z).mpr
        (hle ((P.mem_neighborFinset x z).mp hz))
    have heq : P.neighborFinset x = C.neighborFinset x := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [P.card_neighborFinset_eq_degree, C.card_neighborFinset_eq_degree,
        hdegP, hdegC]
    have hy : y ∈ C.neighborFinset x := (C.mem_neighborFinset x y).mpr hC
    rw [← heq] at hy
    exact (P.mem_neighborFinset x y).mp hy

/-- Distinct vertices of the exact-boundary child cannot share a neighbor
outside the child.  Equivalently, the rows of the child-to-complement
incidence matrix have disjoint supports. -/
theorem minimumLayer_no_common_external_neighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    {x y : minimumLayerVertex (secondOrderDefectGraph G) c₀} (hxy : x ≠ y)
    {z : V}
    (hzOutside : z ∉ Set.range
      (minimumLayerVertexValue :
        minimumLayerVertex (secondOrderDefectGraph G) c₀ → V))
    (hzx : G.Adj z x.2.1) (hzy : G.Adj z y.2.1) : False := by
  classical
  let H := minimumLayerGraph G (secondOrderDefectGraph G) c₀
  let P := minimumLayerParentDefect (secondOrderDefectGraph G) c₀
  let C := secondOrderDefectGraph H
  have hdefectEq : P = C :=
    minimumLayerParentDefect_eq_childDefect G hfree hd heven hmin hcard
      c₀ hregChild hcardChild
  have hxyValue : x.2.1 ≠ y.2.1 :=
    minimumLayerVertexValue_injective.ne hxy
  by_cases hPxy : P.Adj x y
  · have hparent := card_common_eq_if_secondOrderDefect
      G hfree x.2.1 y.2.1 hxyValue
    have hyMem : y.2.1 ∈
        (secondOrderDefectGraph G).neighborFinset x.2.1 :=
      ((secondOrderDefectGraph G).mem_neighborFinset x.2.1 y.2.1).mpr hPxy
    rw [if_pos hyMem] at hparent
    have hzMem : z ∈ G.neighborFinset x.2.1 ∩ G.neighborFinset y.2.1 :=
      Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset x.2.1 z).mpr hzx.symm,
          (G.mem_neighborFinset y.2.1 z).mpr hzy.symm⟩
    exact (Finset.card_ne_zero.mpr ⟨z, hzMem⟩) hparent
  · have hCxy : ¬ C.Adj x y := by simpa [hdefectEq] using hPxy
    have hchild := card_common_eq_if_secondOrderDefect
      H (minimumLayerGraph_c4Free G (secondOrderDefectGraph G) c₀ hfree)
      x y hxy
    have hyNotMem : y ∉ C.neighborFinset x := by
      simpa [C.mem_neighborFinset] using hCxy
    rw [if_neg hyNotMem] at hchild
    have hnonempty : (H.neighborFinset x ∩ H.neighborFinset y).Nonempty :=
      Finset.card_pos.mp (by omega)
    let q := hnonempty.choose
    have hqmem := hnonempty.choose_spec
    have ⟨hqx, hqy⟩ := Finset.mem_inter.mp hqmem
    have hqOutsideNe : q.2.1 ≠ z := by
      intro hqz
      apply hzOutside
      exact ⟨q, hqz⟩
    exact hfree (containsC4_of_two_common hxyValue hqOutsideNe
      ((H.mem_neighborFinset x q).mp hqx).symm
      ((H.mem_neighborFinset y q).mp hqy).symm hzx hzy)

def minimumLayerImageFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [Fintype D.ConnectedComponent]
    [DecidableEq D.ConnectedComponent] (c₀ : D.ConnectedComponent) : Finset V :=
  Finset.univ.image
    (minimumLayerVertexValue (D := D) (c₀ := c₀))

def minimumLayerExternalNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent) (x : minimumLayerVertex D c₀) : Finset V :=
  G.neighborFinset x.2.1 \ minimumLayerImageFinset D c₀

theorem card_minimumLayerImageFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [Fintype D.ConnectedComponent]
    [DecidableEq D.ConnectedComponent] (c₀ : D.ConnectedComponent) :
    (minimumLayerImageFinset D c₀).card =
      Fintype.card (minimumLayerVertex D c₀) := by
  classical
  rw [minimumLayerImageFinset,
    Finset.card_image_of_injective _
      (minimumLayerVertexValue_injective (D := D) (c₀ := c₀)),
    Finset.card_univ]

/-- Exactly the `s` internal neighbors of a child vertex are removed from
its ambient neighborhood, leaving `d-s` external neighbors. -/
theorem card_minimumLayerExternalNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent) {d s : ℕ}
    (hregParent : ∀ v : V, G.degree v = d)
    (hregChild : ∀ x : minimumLayerVertex D c₀,
      (minimumLayerGraph G D c₀).degree x = s)
    (x : minimumLayerVertex D c₀) :
    (minimumLayerExternalNeighborFinset G D c₀ x).card = d - s := by
  classical
  let H := minimumLayerGraph G D c₀
  let ι : minimumLayerVertex D c₀ ↪ V :=
    ⟨minimumLayerVertexValue,
      minimumLayerVertexValue_injective (D := D) (c₀ := c₀)⟩
  have hinter : minimumLayerImageFinset D c₀ ∩ G.neighborFinset x.2.1 =
      (H.neighborFinset x).map ι := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzU, hzN⟩ := Finset.mem_inter.mp hz
      change z ∈ Finset.univ.image
        (minimumLayerVertexValue (D := D) (c₀ := c₀)) at hzU
      obtain ⟨q, _hqUniv, hq⟩ := Finset.mem_image.mp hzU
      subst z
      apply Finset.mem_map.mpr
      refine ⟨q, (H.mem_neighborFinset x q).mpr ?_, rfl⟩
      exact (G.mem_neighborFinset x.2.1 q.2.1).mp hzN
    · intro hz
      obtain ⟨q, hqN, hq⟩ := Finset.mem_map.mp hz
      subst z
      exact Finset.mem_inter.mpr
        ⟨by
          change minimumLayerVertexValue q ∈
            Finset.univ.image
              (minimumLayerVertexValue (D := D) (c₀ := c₀))
          exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩,
         (G.mem_neighborFinset x.2.1 q.2.1).mpr
            ((H.mem_neighborFinset x q).mp hqN)⟩
  rw [minimumLayerExternalNeighborFinset, Finset.card_sdiff, hinter,
    Finset.card_map, G.card_neighborFinset_eq_degree,
    H.card_neighborFinset_eq_degree, hregParent, hregChild]

/-- The external-neighborhood rows of distinct child vertices are pairwise
disjoint. -/
theorem minimumLayer_externalNeighbor_pairwiseDisjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3) :
    (↑(Finset.univ : Finset
      (minimumLayerVertex (secondOrderDefectGraph G) c₀)) : Set _).PairwiseDisjoint
      (minimumLayerExternalNeighborFinset G (secondOrderDefectGraph G) c₀) := by
  classical
  intro x _hx y _hy hxy
  change Disjoint
    (minimumLayerExternalNeighborFinset G (secondOrderDefectGraph G) c₀ x)
    (minimumLayerExternalNeighborFinset G (secondOrderDefectGraph G) c₀ y)
  rw [Finset.disjoint_left]
  intro z hzx hzy
  have hzx' := Finset.mem_sdiff.mp hzx
  have hzy' := Finset.mem_sdiff.mp hzy
  exact minimumLayer_no_common_external_neighbor G hfree hd heven hmin hcard
    c₀ hregChild hcardChild hxy
    (by
      intro hzRange
      obtain ⟨q, hq⟩ := hzRange
      apply hzx'.2
      change z ∈ Finset.univ.image
        (minimumLayerVertexValue
          (D := secondOrderDefectGraph G) (c₀ := c₀))
      exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, hq⟩)
    ((G.mem_neighborFinset x.2.1 z).mp hzx'.1).symm
    ((G.mem_neighborFinset y.2.1 z).mp hzy'.1).symm

/-- Every external-neighborhood row lies in the complement of the child. -/
theorem minimumLayer_externalBiUnion_subset_complement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent) :
    Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀) ⊆
      Finset.univ \ minimumLayerImageFinset D c₀ := by
  classical
  intro z hz
  obtain ⟨x, _hx, hzx⟩ := Finset.mem_biUnion.mp hz
  have hdiff := Finset.mem_sdiff.mp hzx
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hdiff.2⟩

/-- The disjoint external neighborhoods inject the `|U|(d-s)` cross
incidences into the complement of the child. -/
theorem minimumLayer_cross_incidence_le_complement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3) :
    Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) * (d - s) ≤
      Fintype.card V -
        Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨a, rfl⟩ : ∃ a : ℕ, d = a + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  have hregParent : ∀ v : V, G.degree v = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by omega) hmin hbelow
  have hcardE : ∀ x : minimumLayerVertex D c₀, (E x).card = d - s := by
    intro x
    exact card_minimumLayerExternalNeighborFinset G D c₀
      hregParent hregChild x
  have hpair :
      (↑(Finset.univ : Finset (minimumLayerVertex D c₀)) : Set _).PairwiseDisjoint E := by
    intro x _hx y _hy hxy
    change Disjoint (E x) (E y)
    rw [Finset.disjoint_left]
    intro z hzx hzy
    have hzx' := Finset.mem_sdiff.mp hzx
    have hzy' := Finset.mem_sdiff.mp hzy
    exact minimumLayer_no_common_external_neighbor G hfree hd heven hmin hcard
      c₀ hregChild hcardChild hxy
      (by
        intro hzRange
        obtain ⟨q, hq⟩ := hzRange
        apply hzx'.2
        change z ∈ Finset.univ.image
          (minimumLayerVertexValue (D := D) (c₀ := c₀))
        exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, hq⟩)
      ((G.mem_neighborFinset x.2.1 z).mp hzx'.1).symm
      ((G.mem_neighborFinset y.2.1 z).mp hzy'.1).symm
  have hunionSub : (Finset.univ.biUnion E) ⊆ Finset.univ \ U := by
    intro z hz
    obtain ⟨x, _hx, hzx⟩ := Finset.mem_biUnion.mp hz
    have hdiff := Finset.mem_sdiff.mp hzx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hdiff.2⟩
  calc
    Fintype.card (minimumLayerVertex D c₀) * (d - s) =
        ∑ x : minimumLayerVertex D c₀, (E x).card := by
          simp_rw [hcardE]
          simp
    _ = (Finset.univ.biUnion E).card :=
      (Finset.card_biUnion hpair).symm
    _ ≤ (Finset.univ \ U).card := Finset.card_le_card hunionSub
    _ = Fintype.card V - Fintype.card (minimumLayerVertex D c₀) := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ U),
        Finset.card_univ, card_minimumLayerImageFinset]

private theorem exactBoundary_order_difference_factor
    (d s : ℕ) (hsd : s < d) :
      (d * (d - 1) + 3) - (s * (s - 1) + 3) =
        (d - s) * (d + s - 1) := by
  have hmul : s * (s - 1) ≤ d * (d - 1) :=
    Nat.mul_le_mul (Nat.le_of_lt hsd)
      (Nat.sub_le_sub_right (Nat.le_of_lt hsd) 1)
  have hle : s * (s - 1) + 3 ≤ d * (d - 1) + 3 := by omega
  rw [Nat.sub_eq_iff_eq_add hle]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hsd
  cases s with
  | zero => simp
  | succ n =>
      have h₁ : n + 1 - 1 = n := by omega
      have h₂ : n + 1 + t + 1 - (n + 1) = t + 1 := by omega
      have h₃ : n + 1 + t + 1 - 1 = n + t + 1 := by omega
      have h₄ : n + 1 + t + 1 + (n + 1) - 1 = 2 * n + t + 2 := by
        omega
      rw [h₁, h₂, h₃, h₄]
      ring

private theorem extension_degree_gap_arithmetic
    (d s : ℕ) (hd : 4 ≤ d) (hsd : s < d)
    (hcross :
      (s * (s - 1) + 3) * (d - s) ≤
        (d * (d - 1) + 3) - (s * (s - 1) + 3)) :
    (s - 1) * (s - 1) + 3 ≤ d := by
  have hdiff := exactBoundary_order_difference_factor d s hsd
  rw [hdiff, Nat.mul_comm (d - s)] at hcross
  have hpos : 0 < d - s := Nat.sub_pos_of_lt hsd
  have hcancel : s * (s - 1) + 3 ≤ d + s - 1 :=
    Nat.le_of_mul_le_mul_right hcross hpos
  by_cases hs : s ≤ 1
  · interval_cases s <;> omega
  · have hs2 : 2 ≤ s := by omega
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, s = t + 2 := ⟨s - 2, by omega⟩
    norm_num at hcancel ⊢
    nlinarith

/-- **Quadratic extension gap.**  A strict exact-boundary parent of degree
`d` containing its minimum-layer child of degree `s` must satisfy
`d ≥ (s-1)²+3`.  Thus descent steps shrink at least at a square-root rate. -/
theorem minimumLayer_extension_degree_gap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hsd : s < d) :
    (s - 1) * (s - 1) + 3 ≤ d := by
  have hcross := minimumLayer_cross_incidence_le_complement
    G hfree hd heven hmin hcard c₀ hregChild hcardChild
  rw [hcard, hcardChild] at hcross
  exact extension_degree_gap_arithmetic d s hd hsd hcross

/-- Graph-facing capstone: outside degrees `4` and `12`, every exact even
boundary graph contains a strictly smaller exact even boundary graph, and
the parent degree is at least quadratic in the child degree. -/
theorem secondOrder_minimumLayer_quadratic_descent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard) :
    ∃ s : ℕ,
      (∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s) ∧
      ¬ containsC4 (minimumLayerVertex (secondOrderDefectGraph G) c₀)
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀) ∧
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3 ∧
      Even s ∧
      (d ≠ 4 → d ≠ 12 →
        s < d ∧ (s - 1) * (s - 1) + 3 ≤ d) := by
  obtain ⟨s, hreg, hfreeChild, hcardChild, hsEven, hlt⟩ :=
    secondOrder_minimumLayer_descent
      G hfree hd heven hmin hcard c₀ hc₀min
  refine ⟨s, hreg, hfreeChild, hcardChild, hsEven, ?_⟩
  intro hd4 hd12
  have hsd := hlt hd4 hd12
  exact ⟨hsd, minimumLayer_extension_degree_gap
    G hfree hd heven hmin hcard c₀ hreg hcardChild hsd⟩

/-- An exterior vertex missed by every child-to-complement incidence row
has one distinct neighbor in each row.  Hence the entire child injects into
that vertex's ambient neighborhood. -/
theorem minimumLayer_card_le_degree_of_unused_vertex
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (z : V)
    (hzOutside : z ∉ minimumLayerImageFinset (secondOrderDefectGraph G) c₀)
    (hzUnused : z ∉ Finset.univ.biUnion
      (minimumLayerExternalNeighborFinset G (secondOrderDefectGraph G) c₀)) :
    Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) ≤ d := by
  classical
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨a, rfl⟩ : ∃ a : ℕ, d = a + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  have hregParent : ∀ v : V, G.degree v = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by omega) hmin hbelow
  have hzNoChildAdj : ∀ u : minimumLayerVertex D c₀, ¬ G.Adj z u.2.1 := by
    intro u hzu
    apply hzUnused
    apply Finset.mem_biUnion.mpr
    refine ⟨u, Finset.mem_univ _, ?_⟩
    apply Finset.mem_sdiff.mpr
    exact ⟨(G.mem_neighborFinset u.2.1 z).mpr hzu.symm, hzOutside⟩
  have hservice : ∀ u : minimumLayerVertex D c₀,
      ∃ q : V, q ∈ E u ∧ q ∈ G.neighborFinset z := by
    intro u
    have hzNotD : ¬ D.Adj u.2.1 z := by
      intro hD
      have hcomp : D.connectedComponentMk z = u.1.1 :=
        (ConnectedComponent.connectedComponentMk_eq_of_adj hD.symm).trans
          ((ConnectedComponent.mem_supp_iff u.1.1 u.2.1).mp u.2.2)
      have hzSupp : z ∈ u.1.1.supp :=
        (ConnectedComponent.mem_supp_iff u.1.1 z).mpr hcomp
      apply hzOutside
      change z ∈ Finset.univ.image
        (minimumLayerVertexValue (D := D) (c₀ := c₀))
      exact Finset.mem_image.mpr
        ⟨⟨u.1, ⟨z, hzSupp⟩⟩, Finset.mem_univ _, rfl⟩
    have huz : u.2.1 ≠ z := by
      intro huz
      apply hzOutside
      change z ∈ Finset.univ.image
        (minimumLayerVertexValue (D := D) (c₀ := c₀))
      exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, huz⟩
    have hcommon := card_common_eq_if_secondOrderDefect
      G hfree u.2.1 z huz
    have hzNotMem : z ∉ D.neighborFinset u.2.1 := by
      simpa [D.mem_neighborFinset] using hzNotD
    rw [if_neg hzNotMem] at hcommon
    have hnonempty : (G.neighborFinset u.2.1 ∩ G.neighborFinset z).Nonempty :=
      Finset.card_pos.mp (by omega)
    let q := hnonempty.choose
    have hqmem := hnonempty.choose_spec
    have ⟨hqu, hqz⟩ := Finset.mem_inter.mp hqmem
    have hqOutside : q ∉ minimumLayerImageFinset D c₀ := by
      intro hqU
      obtain ⟨v, _hv, hvq⟩ := Finset.mem_image.mp hqU
      apply hzNoChildAdj v
      have hzq : G.Adj z q := (G.mem_neighborFinset z q).mp hqz
      change v.2.1 = q at hvq
      rw [hvq]
      exact hzq
    exact ⟨q, Finset.mem_sdiff.mpr ⟨hqu, hqOutside⟩, hqz⟩
  let f : minimumLayerVertex D c₀ → ↥(G.neighborFinset z) :=
    fun u ↦ ⟨(hservice u).choose, (hservice u).choose_spec.2⟩
  have hfMem : ∀ u : minimumLayerVertex D c₀, (f u).1 ∈ E u := by
    intro u
    exact (hservice u).choose_spec.1
  have hfInjective : Function.Injective f := by
    intro u v huv
    by_contra huvNe
    have hu := Finset.mem_sdiff.mp (hfMem u)
    have hv := Finset.mem_sdiff.mp (hfMem v)
    have hval : (f u).1 = (f v).1 := congrArg Subtype.val huv
    exact minimumLayer_no_common_external_neighbor G hfree hd heven hmin hcard
      c₀ hregChild hcardChild huvNe
      (by
        intro hrange
        obtain ⟨w, hw⟩ := hrange
        apply hu.2
        change (f u).1 ∈ Finset.univ.image
          (minimumLayerVertexValue (D := D) (c₀ := c₀))
        exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, hw⟩)
      ((G.mem_neighborFinset u.2.1 (f u).1).mp hu.1).symm
      (by
        rw [hval]
        exact ((G.mem_neighborFinset v.2.1 (f v).1).mp hv.1).symm)
  have hle := Fintype.card_le_of_injective f hfInjective
  calc
    Fintype.card (minimumLayerVertex D c₀) ≤
        Fintype.card ↥(G.neighborFinset z) := hle
    _ = (G.neighborFinset z).card := Fintype.card_coe _
    _ = G.degree z := G.card_neighborFinset_eq_degree z
    _ = d := hregParent z

private theorem extension_saturation_degree_eq
    (d s : ℕ) (hspos : 0 < s) (hsd : s < d)
    (hcount :
      (s * (s - 1) + 3) * (d - s) =
        (d * (d - 1) + 3) - (s * (s - 1) + 3)) :
    d = (s - 1) * (s - 1) + 3 := by
  rw [exactBoundary_order_difference_factor d s hsd,
    Nat.mul_comm (d - s)] at hcount
  have hpos : 0 < d - s := Nat.sub_pos_of_lt hsd
  rw [Nat.mul_comm (s * (s - 1) + 3) (d - s),
    Nat.mul_comm (d + s - 1) (d - s)] at hcount
  have hcancel : s * (s - 1) + 3 = d + s - 1 :=
    Nat.eq_of_mul_eq_mul_left hpos hcount
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, s = t + 1 := ⟨s - 1, by omega⟩
  norm_num at hcancel ⊢
  nlinarith

/-- **Sharp extension dichotomy.**  For a strict parent-child extension,
either every exterior vertex is used by a child incidence row, forcing the
exceptional equality `d=(s-1)²+3`, or an unused exterior vertex sees one
distinct representative from every row, forcing the stronger bound
`|U|=s²-s+3≤d`. -/
theorem minimumLayer_extension_saturation_or_childOrder_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hsd : s < d) :
    d = (s - 1) * (s - 1) + 3 ∨ s * (s - 1) + 3 ≤ d := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  by_cases hcover : Finset.univ \ U ⊆ Finset.univ.biUnion E
  · by_cases hs0 : s = 0
    · right
      subst s
      norm_num
      omega
    · left
      apply extension_saturation_degree_eq d s (Nat.pos_of_ne_zero hs0) hsd
      have hcross := minimumLayer_cross_incidence_le_complement
        G hfree hd heven hmin hcard c₀ hregChild hcardChild
      have hcompLeUnion : (Finset.univ \ U).card ≤
          (Finset.univ.biUnion E).card := Finset.card_le_card hcover
      have hunionLeSum : (Finset.univ.biUnion E).card ≤
          ∑ x : minimumLayerVertex D c₀, (E x).card :=
        Finset.card_biUnion_le
      have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
        rw [hcard]
        obtain ⟨a, rfl⟩ : ∃ a : ℕ, d = a + 4 := ⟨d - 4, by omega⟩
        norm_num
        nlinarith
      have hregParent : ∀ v : V, G.degree v = d :=
        regular_of_minDegree_card_lt_nextMooreLayer
          G hfree (by omega) hmin hbelow
      have hcardE : ∀ x : minimumLayerVertex D c₀, (E x).card = d - s := by
        intro x
        exact card_minimumLayerExternalNeighborFinset G D c₀
          hregParent hregChild x
      have hsum : (∑ x : minimumLayerVertex D c₀, (E x).card) =
          Fintype.card (minimumLayerVertex D c₀) * (d - s) := by
        simp_rw [hcardE]
        simp
      have hcompCard : (Finset.univ \ U).card =
          Fintype.card V - Fintype.card (minimumLayerVertex D c₀) := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ U),
          Finset.card_univ, card_minimumLayerImageFinset]
      have hreverse :
          Fintype.card V - Fintype.card (minimumLayerVertex D c₀) ≤
            Fintype.card (minimumLayerVertex D c₀) * (d - s) := by
        rw [← hcompCard]
        exact hcompLeUnion.trans (hunionLeSum.trans_eq hsum)
      have hcount :
          Fintype.card (minimumLayerVertex D c₀) * (d - s) =
            Fintype.card V - Fintype.card (minimumLayerVertex D c₀) := by
        exact Nat.le_antisymm hcross hreverse
      dsimp [D] at hcount
      rw [hcard, hcardChild] at hcount
      exact hcount
  · right
    obtain ⟨z, hzComp, hzUnused⟩ := Finset.not_subset.mp hcover
    have hzOutside := (Finset.mem_sdiff.mp hzComp).2
    have hle := minimumLayer_card_le_degree_of_unused_vertex
      G hfree hd heven hmin hcard c₀ hregChild hcardChild z hzOutside hzUnused
    simpa [hcardChild] using hle

/-- In the even-degree setting, the nonsaturated lower bound improves by
one because the child boundary order is odd. -/
theorem minimumLayer_extension_even_saturation_or_gap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hsd : s < d) :
    d = (s - 1) * (s - 1) + 3 ∨ s * (s - 1) + 4 ≤ d := by
  rcases minimumLayer_extension_saturation_or_childOrder_le
    G hfree hd heven hmin hcard c₀ hregChild hcardChild hsd with heq | hle
  · exact Or.inl heq
  · right
    obtain ⟨a, ha⟩ := heven
    obtain ⟨b, hb⟩ := Nat.even_mul_pred_self s
    omega

/-- Graph-facing sharp capstone for the descent tower. -/
theorem secondOrder_minimumLayer_sharp_descent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard) :
    ∃ s : ℕ,
      (∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s) ∧
      ¬ containsC4 (minimumLayerVertex (secondOrderDefectGraph G) c₀)
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀) ∧
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3 ∧
      Even s ∧
      (d ≠ 4 → d ≠ 12 → s < d ∧
        (d = (s - 1) * (s - 1) + 3 ∨ s * (s - 1) + 4 ≤ d)) := by
  obtain ⟨s, hreg, hfreeChild, hcardChild, hsEven, hlt⟩ :=
    secondOrder_minimumLayer_descent
      G hfree hd heven hmin hcard c₀ hc₀min
  refine ⟨s, hreg, hfreeChild, hcardChild, hsEven, ?_⟩
  intro hd4 hd12
  have hsd := hlt hd4 hd12
  exact ⟨hsd, minimumLayer_extension_even_saturation_or_gap
    G hfree hd heven hmin hcard c₀ hreg hcardChild hsd⟩

/-- In the saturated branch, the disjoint external-neighborhood rows cover
the entire complement of the child. -/
theorem minimumLayer_externalBiUnion_eq_complement_of_saturated
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hspos : 0 < s) (hsd : s < d)
    (hsat : d = (s - 1) * (s - 1) + 3) :
    Finset.univ.biUnion
        (minimumLayerExternalNeighborFinset G (secondOrderDefectGraph G) c₀) =
      Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀ := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  have hsub : Finset.univ.biUnion E ⊆ Finset.univ \ U :=
    minimumLayer_externalBiUnion_subset_complement G D c₀
  have hpair := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree hd heven hmin hcard c₀ hregChild hcardChild
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨a, rfl⟩ : ∃ a : ℕ, d = a + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  have hregParent : ∀ v : V, G.degree v = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by omega) hmin hbelow
  have hcardE : ∀ x : minimumLayerVertex D c₀, (E x).card = d - s := by
    intro x
    exact card_minimumLayerExternalNeighborFinset G D c₀
      hregParent hregChild x
  have hsatOrder : s * (s - 1) + 3 = d + s - 1 := by
    rw [hsat]
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, s = t + 1 := ⟨s - 1, by omega⟩
    norm_num
    ring
  have horderDiff := exactBoundary_order_difference_factor d s hsd
  have hcardEq : (Finset.univ.biUnion E).card = (Finset.univ \ U).card := by
    calc
      (Finset.univ.biUnion E).card =
          ∑ x : minimumLayerVertex D c₀, (E x).card :=
        Finset.card_biUnion hpair
      _ = Fintype.card (minimumLayerVertex D c₀) * (d - s) := by
        simp_rw [hcardE]
        simp
      _ = (s * (s - 1) + 3) * (d - s) := by rw [hcardChild]
      _ = (d * (d - 1) + 3) - (s * (s - 1) + 3) := by
        rw [horderDiff, ← hsatOrder]
        exact Nat.mul_comm _ _
      _ = Fintype.card V - Fintype.card (minimumLayerVertex D c₀) := by
        rw [hcard, hcardChild]
      _ = (Finset.univ \ U).card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ U),
          Finset.card_univ, card_minimumLayerImageFinset]
  exact Finset.eq_of_subset_of_card_le hsub hcardEq.ge

/-- Saturation turns the exterior rows into a perfect one-design: every
exterior vertex has a unique child owner. -/
theorem minimumLayer_existsUnique_externalOwner_of_saturated
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hspos : 0 < s) (hsd : s < d)
    (hsat : d = (s - 1) * (s - 1) + 3)
    {z : V}
    (hzOutside : z ∉ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) :
    ∃! x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      z ∈ minimumLayerExternalNeighborFinset G (secondOrderDefectGraph G) c₀ x := by
  classical
  let E := minimumLayerExternalNeighborFinset G (secondOrderDefectGraph G) c₀
  have hcover := minimumLayer_externalBiUnion_eq_complement_of_saturated
    G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
  have hzComp : z ∈ Finset.univ \
      minimumLayerImageFinset (secondOrderDefectGraph G) c₀ :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzOutside⟩
  rw [← hcover] at hzComp
  obtain ⟨x, _hx, hzx⟩ := Finset.mem_biUnion.mp hzComp
  refine ⟨x, hzx, ?_⟩
  intro y hzy
  by_contra hxy
  have hpair := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree hd heven hmin hcard c₀ hregChild hcardChild
  have hdisj := hpair (Finset.mem_univ x) (Finset.mem_univ y) (Ne.symm hxy)
  exact (Finset.disjoint_left.mp hdisj hzx hzy).elim

/-- **Owned exterior block law.**  If an exterior vertex `z` is owned by `v`,
then its degree into the exterior row owned by `u` is zero over an edge
`u-v` of the child and one over a nonedge.  Saturation is not needed: the
ownership witness and disjointness of the child rows suffice. -/
theorem minimumLayer_externalBlock_card_of_owned
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (u v : minimumLayerVertex (secondOrderDefectGraph G) c₀) {z : V}
    (hzv : z ∈ minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀ v) :
    (G.neighborFinset z ∩ minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀ u).card =
        if (minimumLayerGraph G (secondOrderDefectGraph G) c₀).Adj u v
        then 0 else 1 := by
  classical
  let D := secondOrderDefectGraph G
  let H := minimumLayerGraph G D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  have hzv' := Finset.mem_sdiff.mp hzv
  have hzOutside : z ∉ minimumLayerImageFinset D c₀ := hzv'.2
  have huz : u.2.1 ≠ z := by
    intro huz
    apply hzOutside
    change z ∈ Finset.univ.image
      (minimumLayerVertexValue (D := D) (c₀ := c₀))
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, huz⟩
  have hzNotD : ¬ D.Adj u.2.1 z := by
    intro hD
    have hcomp : D.connectedComponentMk z = u.1.1 :=
      (ConnectedComponent.connectedComponentMk_eq_of_adj hD.symm).trans
        ((ConnectedComponent.mem_supp_iff u.1.1 u.2.1).mp u.2.2)
    have hzSupp : z ∈ u.1.1.supp :=
      (ConnectedComponent.mem_supp_iff u.1.1 z).mpr hcomp
    apply hzOutside
    change z ∈ Finset.univ.image
      (minimumLayerVertexValue (D := D) (c₀ := c₀))
    exact Finset.mem_image.mpr
      ⟨⟨u.1, ⟨z, hzSupp⟩⟩, Finset.mem_univ _, rfl⟩
  have hcommon := card_common_eq_if_secondOrderDefect
    G hfree u.2.1 z huz
  have hzNotMem : z ∉ D.neighborFinset u.2.1 := by
    simpa [D.mem_neighborFinset] using hzNotD
  rw [if_neg hzNotMem] at hcommon
  obtain ⟨q, hqset⟩ := Finset.card_eq_one.mp hcommon
  have hpair := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree hd heven hmin hcard c₀ hregChild hcardChild
  have howner : ∀ {w : minimumLayerVertex D c₀}, z ∈ E w → w = v := by
    intro w hzw
    by_contra hwv
    have hdisj := hpair (Finset.mem_univ w) (Finset.mem_univ v) hwv
    exact (Finset.disjoint_left.mp hdisj hzw hzv).elim
  by_cases huv : H.Adj u v
  · rw [if_pos huv]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    have ⟨hrz, hru⟩ := Finset.mem_inter.mp hr
    have hru' := Finset.mem_sdiff.mp hru
    have hrv : v.2.1 ≠ r := by
      intro hvr
      apply hru'.2
      change r ∈ Finset.univ.image
        (minimumLayerVertexValue (D := D) (c₀ := c₀))
      exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, hvr⟩
    exact hfree (containsC4_of_two_common huz hrv
      huv.symm ((G.mem_neighborFinset v.2.1 z).mp hzv'.1)
        ((G.mem_neighborFinset u.2.1 r).mp hru'.1).symm
        ((G.mem_neighborFinset z r).mp hrz).symm)
  · rw [if_neg huv]
    have hqmem : q ∈ G.neighborFinset u.2.1 ∩ G.neighborFinset z := by
      rw [hqset]
      exact Finset.mem_singleton_self q
    have ⟨hqu, hqz⟩ := Finset.mem_inter.mp hqmem
    have hqOutside : q ∉ minimumLayerImageFinset D c₀ := by
      intro hqU
      obtain ⟨w, _hw, hwq⟩ := Finset.mem_image.mp hqU
      have hzw : z ∈ E w := by
        apply Finset.mem_sdiff.mpr
        refine ⟨?_, hzOutside⟩
        have hzq : G.Adj z q := (G.mem_neighborFinset z q).mp hqz
        change w.2.1 = q at hwq
        exact (G.mem_neighborFinset w.2.1 z).mpr (by simpa [hwq] using hzq.symm)
      have hwv := howner hzw
      apply huv
      change G.Adj u.2.1 v.2.1
      change w.2.1 = q at hwq
      rw [← hwv, hwq]
      exact (G.mem_neighborFinset u.2.1 q).mp hqu
    apply Finset.card_eq_one.mpr
    refine ⟨q, ?_⟩
    ext r
    constructor
    · intro hr
      have ⟨hrz, hru⟩ := Finset.mem_inter.mp hr
      have hru' := Finset.mem_sdiff.mp hru
      have hrCommon : r ∈ G.neighborFinset u.2.1 ∩ G.neighborFinset z :=
        Finset.mem_inter.mpr
          ⟨hru'.1, by
            exact (G.mem_neighborFinset z r).mpr
              ((G.mem_neighborFinset z r).mp hrz)⟩
      rw [hqset] at hrCommon
      simpa using hrCommon
    · intro hr
      have hrq : r = q := Finset.mem_singleton.mp hr
      subst r
      exact Finset.mem_inter.mpr
        ⟨hqz, Finset.mem_sdiff.mpr ⟨hqu, hqOutside⟩⟩

/-- **Saturated block law.**  Compatibility wrapper for the original
saturated interface; the stronger owned-vertex theorem above shows that its
three saturation assumptions are unnecessary. -/
theorem minimumLayer_saturated_externalBlock_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (_hspos : 0 < s) (_hsd : s < d)
    (_hsat : d = (s - 1) * (s - 1) + 3)
    (u v : minimumLayerVertex (secondOrderDefectGraph G) c₀) {z : V}
    (hzv : z ∈ minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀ v) :
    (G.neighborFinset z ∩ minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀ u).card =
        if (minimumLayerGraph G (secondOrderDefectGraph G) c₀).Adj u v
        then 0 else 1 := by
  exact minimumLayer_externalBlock_card_of_owned
    G hfree hd heven hmin hcard c₀ hregChild hcardChild u v hzv

/-- Above a child edge there are no edges between the corresponding exterior
rows.  This is the empty-block half of the saturated matching lift. -/
theorem minimumLayer_saturated_externalBlock_eq_empty_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hspos : 0 < s) (hsd : s < d)
    (hsat : d = (s - 1) * (s - 1) + 3)
    (u v : minimumLayerVertex (secondOrderDefectGraph G) c₀) {z : V}
    (hzv : z ∈ minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀ v)
    (huv : (minimumLayerGraph G (secondOrderDefectGraph G) c₀).Adj u v) :
    G.neighborFinset z ∩ minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀ u = ∅ := by
  apply Finset.card_eq_zero.mp
  simpa [huv] using minimumLayer_saturated_externalBlock_card
    G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat u v hzv

/-- Above a child nonedge, every vertex in one exterior row has a unique
neighbor in the other row.  Together with symmetry this says that the block
is a perfect matching. -/
theorem minimumLayer_saturated_externalBlock_existsUnique_of_not_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hspos : 0 < s) (hsd : s < d)
    (hsat : d = (s - 1) * (s - 1) + 3)
    (u v : minimumLayerVertex (secondOrderDefectGraph G) c₀) {z : V}
    (hzv : z ∈ minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀ v)
    (huv : ¬(minimumLayerGraph G (secondOrderDefectGraph G) c₀).Adj u v) :
    ∃! r : V,
      r ∈ minimumLayerExternalNeighborFinset
        G (secondOrderDefectGraph G) c₀ u ∧ G.Adj z r := by
  have hcardBlock :
      (G.neighborFinset z ∩ minimumLayerExternalNeighborFinset
        G (secondOrderDefectGraph G) c₀ u).card = 1 := by
    simpa [huv] using minimumLayer_saturated_externalBlock_card
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat u v hzv
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hcardBlock
  refine ⟨r, ?_, ?_⟩
  · have hrmem : r ∈ G.neighborFinset z ∩
        minimumLayerExternalNeighborFinset
          G (secondOrderDefectGraph G) c₀ u := by
      rw [hr]
      exact Finset.mem_singleton_self r
    exact ⟨(Finset.mem_inter.mp hrmem).2,
      (G.mem_neighborFinset z r).mp (Finset.mem_inter.mp hrmem).1⟩
  · intro q hq
    have hqmem : q ∈ G.neighborFinset z ∩
        minimumLayerExternalNeighborFinset
          G (secondOrderDefectGraph G) c₀ u :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z q).mpr hq.2, hq.1⟩
    rw [hr] at hqmem
    exact Finset.mem_singleton.mp hqmem

/-- The first permutation-lift coherence constraint: a four-step chain of
exterior matching blocks cannot close when opposite owner rows are distinct.
In permutation language, the corresponding fourfold product has no fixed
point. -/
theorem minimumLayer_externalBlock_no_closed_fourStep
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (u₀ u₁ u₂ u₃ : minimumLayerVertex (secondOrderDefectGraph G) c₀)
    (hu₀₂ : u₀ ≠ u₂) (hu₁₃ : u₁ ≠ u₃)
    {z₀ z₁ z₂ z₃ : V}
    (hz₀ : z₀ ∈ minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀ u₀)
    (hz₁ : z₁ ∈ minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀ u₁)
    (hz₂ : z₂ ∈ minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀ u₂)
    (hz₃ : z₃ ∈ minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀ u₃)
    (h₀₁ : G.Adj z₀ z₁) (h₁₂ : G.Adj z₁ z₂)
    (h₂₃ : G.Adj z₂ z₃) (h₃₀ : G.Adj z₃ z₀) : False := by
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  have hpair := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree hd heven hmin hcard c₀ hregChild hcardChild
  have hz₀₂ : z₀ ≠ z₂ := by
    intro h
    subst z₂
    have hdisj := hpair (Finset.mem_univ u₀) (Finset.mem_univ u₂) hu₀₂
    exact Finset.disjoint_left.mp hdisj hz₀ hz₂
  have hz₁₃ : z₁ ≠ z₃ := by
    intro h
    subst z₃
    have hdisj := hpair (Finset.mem_univ u₁) (Finset.mem_univ u₃) hu₁₃
    exact Finset.disjoint_left.mp hdisj hz₁ hz₃
  exact hfree (containsC4_of_two_common hz₀₂ hz₁₃
    h₀₁.symm h₁₂ h₃₀ h₂₃.symm)

end

end Erdos85
