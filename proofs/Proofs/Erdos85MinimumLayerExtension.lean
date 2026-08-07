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

end

end Erdos85
