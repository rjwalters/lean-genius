import Proofs.Erdos85BinarySquareMuThreeExteriorRowHit
import Proofs.Erdos85BinarySquareTriangleFreeEdgeCongruence
import Proofs.Erdos85MuThreeKSymmetryCapstone

/-!
# Assembling the order-64 mu=3 exterior as a mixed grid

This file supplies the type-level relabeling used by the graph-facing mu=3
constructor.  An injective exterior label into the positive/negative sign
shores determines the missing-cell relation `K`; its complement is exactly
the image of the 48 exterior vertices.  Consequently the exterior graph can
be transported canonically to `muThreeMixedCell K`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem muThree_signedFlip_of_degree_two_neighborSum
    {W : Type*} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj]
    (hdeg : ∀ x, J.degree x = 2)
    (t : W → ℤ) (hsign : ∀ x, t x = -1 ∨ t x = 1)
    (hsum : ∀ x, ∑ y ∈ J.neighborFinset x, t y = -2 * t x) :
    ∀ ⦃x y⦄, J.Adj x y → t x = -t y := by
  intro x y hxy
  have hcard : (J.neighborFinset x).card = 2 := by
    rw [J.card_neighborFinset_eq_degree, hdeg]
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hcard
  have hy : y ∈ J.neighborFinset x := by simpa using hxy
  rw [hset] at hy
  have hsumx := hsum x
  rw [hset, Finset.sum_pair hab] at hsumx
  have hxsign := hsign x
  have hasign := hsign a
  have hbsign := hsign b
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl <;>
    rcases hxsign with hx | hx <;>
    rcases hasign with ha | ha <;>
    rcases hbsign with hb | hb <;>
    omega

theorem muThree_adjMatrix_mulVec_eq_induce_mulVec_of_support_int
    {W : Type*} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (S : Set W) [Fintype S]
    (t : W → ℤ) (ht : ∀ y, y ∉ S → t y = 0) (x : S) :
    (J.adjMatrix ℤ).mulVec t x.1 =
      ((J.induce S).adjMatrix ℤ).mulVec (fun y : S => t y.1) x := by
  classical
  rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
  calc
    (∑ y : W, J.adjMatrix ℤ x.1 y * t y) =
        ∑ y : W, if y ∈ S then J.adjMatrix ℤ x.1 y * t y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y ∈ S
      · simp [hy]
      · simp [hy, ht y hy]
    _ = ∑ y ∈ (Finset.univ : Finset W).filter (fun y => y ∈ S),
        J.adjMatrix ℤ x.1 y * t y := by rw [← Finset.sum_filter]
    _ = ∑ y : S, J.adjMatrix ℤ x.1 y.1 * t y.1 := by
      simpa using (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset W)) (p := fun y => y ∈ S)
        (fun y => J.adjMatrix ℤ x.1 y * t y)).symm
    _ = ∑ y : S, (J.induce S).adjMatrix ℤ x y * t y.1 := by
      apply Finset.sum_congr rfl
      intro y _
      simp only [SimpleGraph.adjMatrix_apply]
      rfl

abbrev muThreePositiveShore
    {V : Type*} (cSupp : Set V) (s : V → ℤ) :=
  {x : V // x ∈ cSupp ∧ s x = 1}

abbrev muThreeNegativeShore
    {V : Type*} (cSupp : Set V) (s : V → ℤ) :=
  {y : V // y ∈ cSupp ∧ s y = -1}

abbrev muThreeExterior
    {V : Type*} (cSupp : Set V) :=
  {u : V // u ∉ cSupp}

/-- A grid position is a hole precisely when no exterior vertex has that
signed coordinate pair. -/
def orderSixtyFourMuThreeHole
    {V : Type*} {cSupp : Set V} {s : V → ℤ}
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s) :
    muThreePositiveShore cSupp s → muThreeNegativeShore cSupp s → Prop :=
  fun x y => ¬ ∃ u, label u = (x, y)

instance orderSixtyFourMuThreeHole_decidable
    {V : Type*} [Fintype V] [DecidableEq V]
    {cSupp : Set V} {s : V → ℤ}
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s) :
    DecidableRel (orderSixtyFourMuThreeHole label) := by
  classical
  intro x y
  unfold orderSixtyFourMuThreeHole
  infer_instance

/-- The injective exterior label is an equivalence onto the occupied cells
of the grid whose holes are the pairs with no label preimage. -/
noncomputable def orderSixtyFourMuThreeExteriorCellEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    {cSupp : Set V} {s : V → ℤ}
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (hinj : Function.Injective label) :
    muThreeExterior cSupp ≃ muThreeMixedCell (orderSixtyFourMuThreeHole label) := by
  let f : muThreeExterior cSupp →
      muThreeMixedCell (orderSixtyFourMuThreeHole label) := fun u =>
    ⟨label u, by
      simp only [orderSixtyFourMuThreeHole, not_not]
      exact ⟨u, rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro u v huv
    apply hinj
    exact congrArg (fun p => p.1) huv
  · intro p
    have hp : ∃ u, label u = p.1 := by
      simpa only [orderSixtyFourMuThreeHole, not_not] using p.2
    obtain ⟨u, hu⟩ := hp
    refine ⟨u, ?_⟩
    apply Subtype.ext
    exact hu

/-- Transport the induced exterior graph through the occupied-cell
equivalence. -/
def orderSixtyFourMuThreeExteriorCellGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {cSupp : Set V} {s : V → ℤ}
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (hinj : Function.Injective label) :
    SimpleGraph (muThreeMixedCell (orderSixtyFourMuThreeHole label)) :=
  SimpleGraph.comap
    (orderSixtyFourMuThreeExteriorCellEquiv label hinj).symm
    (G.induce {u | u ∉ cSupp})

noncomputable instance orderSixtyFourMuThreeExteriorCellGraph_decidable
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {cSupp : Set V} {s : V → ℤ}
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (hinj : Function.Injective label) :
    DecidableRel (orderSixtyFourMuThreeExteriorCellGraph G label hinj).Adj := by
  intro u v
  unfold orderSixtyFourMuThreeExteriorCellGraph
  infer_instance

theorem orderSixtyFourMuThreeExteriorCellGraph_adj_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {cSupp : Set V} {s : V → ℤ}
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (hinj : Function.Injective label)
    (u v : muThreeExterior cSupp) :
    (orderSixtyFourMuThreeExteriorCellGraph G label hinj).Adj
        (orderSixtyFourMuThreeExteriorCellEquiv label hinj u)
        (orderSixtyFourMuThreeExteriorCellEquiv label hinj v) ↔
      G.Adj u.1 v.1 := by
  simp only [orderSixtyFourMuThreeExteriorCellGraph, SimpleGraph.comap_adj,
    Equiv.symm_apply_apply]
  rfl

theorem orderSixtyFourMuThreeExteriorCellGraph_c4Free
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {cSupp : Set V} {s : V → ℤ}
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (hinj : Function.Injective label) :
    ¬ containsC4 _ (orderSixtyFourMuThreeExteriorCellGraph G label hinj) := by
  rintro ⟨f, hf, hadj⟩
  apply hfree
  let e := orderSixtyFourMuThreeExteriorCellEquiv label hinj
  refine ⟨fun i => ((e.symm (f i)) : muThreeExterior cSupp).1, ?_, ?_⟩
  · intro i j hij
    apply hf
    apply e.symm.injective
    apply Subtype.ext
    exact hij
  · intro i j hij
    exact hadj i j hij

/-- Fixing a row, occupied columns are equivalent to exterior vertices whose
positive label coordinate is that row. -/
noncomputable def orderSixtyFourMuThreeOccupiedRowEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    {cSupp : Set V} {s : V → ℤ}
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (hinj : Function.Injective label) (x : muThreePositiveShore cSupp s) :
    {y : muThreeNegativeShore cSupp s //
      ¬ orderSixtyFourMuThreeHole label x y} ≃
    {u : muThreeExterior cSupp // (label u).1 = x} := by
  let e := orderSixtyFourMuThreeExteriorCellEquiv label hinj
  let f : {y : muThreeNegativeShore cSupp s //
      ¬ orderSixtyFourMuThreeHole label x y} →
      {u : muThreeExterior cSupp // (label u).1 = x} := fun y =>
    ⟨e.symm ⟨(x, y.1), y.2⟩, by
      have h := congrArg (fun p => p.1.1)
        (e.apply_symm_apply ⟨(x, y.1), y.2⟩)
      exact h⟩
  let g : {u : muThreeExterior cSupp // (label u).1 = x} →
      {y : muThreeNegativeShore cSupp s //
        ¬ orderSixtyFourMuThreeHole label x y} := fun u =>
    ⟨(label u.1).2, by
      simp only [orderSixtyFourMuThreeHole, not_not]
      exact ⟨u.1, Prod.ext u.2 rfl⟩⟩
  refine ⟨f, g, ?_, ?_⟩
  · intro y
    apply Subtype.ext
    change (label (e.symm ⟨(x, y.1), y.2⟩)).2 = y.1
    exact congrArg (fun p => p.1.2)
      (e.apply_symm_apply ⟨(x, y.1), y.2⟩)
  · intro u
    apply Subtype.ext
    dsimp [f, g]
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    exact Prod.ext u.2.symm rfl

/-- Column-dual occupied-fiber equivalence. -/
noncomputable def orderSixtyFourMuThreeOccupiedColumnEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    {cSupp : Set V} {s : V → ℤ}
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (hinj : Function.Injective label) (y : muThreeNegativeShore cSupp s) :
    {x : muThreePositiveShore cSupp s //
      ¬ orderSixtyFourMuThreeHole label x y} ≃
    {u : muThreeExterior cSupp // (label u).2 = y} := by
  let e := orderSixtyFourMuThreeExteriorCellEquiv label hinj
  let f : {x : muThreePositiveShore cSupp s //
      ¬ orderSixtyFourMuThreeHole label x y} →
      {u : muThreeExterior cSupp // (label u).2 = y} := fun x =>
    ⟨e.symm ⟨(x.1, y), x.2⟩, by
      exact congrArg (fun p => p.1.2)
        (e.apply_symm_apply ⟨(x.1, y), x.2⟩)⟩
  let g : {u : muThreeExterior cSupp // (label u).2 = y} →
      {x : muThreePositiveShore cSupp s //
        ¬ orderSixtyFourMuThreeHole label x y} := fun u =>
    ⟨(label u.1).1, by
      simp only [orderSixtyFourMuThreeHole, not_not]
      exact ⟨u.1, Prod.ext rfl u.2⟩⟩
  refine ⟨f, g, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    exact congrArg (fun p => p.1.1)
      (e.apply_symm_apply ⟨(x.1, y), x.2⟩)
  · intro u
    apply Subtype.ext
    dsimp [f, g]
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    exact Prod.ext rfl u.2.symm

/-- Six occupied positions in every row and column of an eight-by-eight grid
make the missing-cell relation two-regular. -/
theorem orderSixtyFourMuThreeHole_twoRegular
    {V : Type*} [Fintype V] [DecidableEq V]
    {cSupp : Set V} {s : V → ℤ}
    [Fintype (muThreePositiveShore cSupp s)]
    [Fintype (muThreeNegativeShore cSupp s)]
    [Fintype (muThreeExterior cSupp)]
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (hinj : Function.Injective label)
    (hP : Fintype.card (muThreePositiveShore cSupp s) = 8)
    (hN : Fintype.card (muThreeNegativeShore cSupp s) = 8)
    (hrow : ∀ x, Fintype.card
      {u : muThreeExterior cSupp // (label u).1 = x} = 6)
    (hcolumn : ∀ y, Fintype.card
      {u : muThreeExterior cSupp // (label u).2 = y} = 6) :
    RelationTwoRegular (orderSixtyFourMuThreeHole label) := by
  classical
  constructor
  · intro x
    rw [← Fintype.card_subtype]
    have hocc : Fintype.card
        {y : muThreeNegativeShore cSupp s //
          ¬ orderSixtyFourMuThreeHole label x y} = 6 := by
      rw [Fintype.card_congr
        (orderSixtyFourMuThreeOccupiedRowEquiv label hinj x)]
      exact hrow x
    have hcompl := Fintype.card_subtype_compl
      (fun y : muThreeNegativeShore cSupp s =>
        orderSixtyFourMuThreeHole label x y)
    rw [hN] at hcompl
    omega
  · intro y
    rw [← Fintype.card_subtype]
    have hocc : Fintype.card
        {x : muThreePositiveShore cSupp s //
          ¬ orderSixtyFourMuThreeHole label x y} = 6 := by
      rw [Fintype.card_congr
        (orderSixtyFourMuThreeOccupiedColumnEquiv label hinj y)]
      exact hcolumn y
    have hcompl := Fintype.card_subtype_compl
      (fun x : muThreePositiveShore cSupp s =>
        orderSixtyFourMuThreeHole label x y)
    rw [hP] at hcompl
    omega

/-- The internal bipartite relation between positive and negative sign
shores. -/
def orderSixtyFourMuThreeInternalRel
    {V : Type*} (G : SimpleGraph V) {cSupp : Set V} {s : V → ℤ} :
    muThreePositiveShore cSupp s → muThreeNegativeShore cSupp s → Prop :=
  fun x y => G.Adj x.1 y.1

instance orderSixtyFourMuThreeInternalRel_decidable
    {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    {cSupp : Set V} {s : V → ℤ} :
    DecidableRel (orderSixtyFourMuThreeInternalRel G
      (cSupp := cSupp) (s := s)) := by
  intro x y
  unfold orderSixtyFourMuThreeInternalRel
  infer_instance

/-- An occupied signed cell is exactly an exterior common neighbour of its
two coordinates. -/
theorem orderSixtyFourMuThree_not_hole_iff_exterior_commonNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {cSupp : Set V} {s : V → ℤ}
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (hadj : ∀ u, G.Adj u.1 (label u).1.1 ∧ G.Adj u.1 (label u).2.1)
    (huniqueP : ∀ u p, G.Adj u.1 p.1 → (label u).1 = p)
    (huniqueN : ∀ u n, G.Adj u.1 n.1 → (label u).2 = n)
    (x : muThreePositiveShore cSupp s)
    (y : muThreeNegativeShore cSupp s) :
    ¬ orderSixtyFourMuThreeHole label x y ↔
      ∃ u : muThreeExterior cSupp, G.Adj u.1 x.1 ∧ G.Adj u.1 y.1 := by
  classical
  simp only [orderSixtyFourMuThreeHole, not_not]
  constructor
  · rintro ⟨u, hu⟩
    have hxy : (label u).1 = x ∧ (label u).2 = y := by
      exact ⟨congrArg Prod.fst hu, congrArg Prod.snd hu⟩
    exact ⟨u, hxy.1 ▸ (hadj u).1, hxy.2 ▸ (hadj u).2⟩
  · rintro ⟨u, hux, huy⟩
    refine ⟨u, Prod.ext (huniqueP u x hux) (huniqueN u y huy)⟩

/-- A common neighbour of an internal positive-negative edge cannot itself
lie in the signed component. -/
theorem orderSixtyFourMuThree_internalEdge_commonNeighbor_not_mem
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {cSupp : Set V} {s : V → ℤ}
    (hflip : ∀ {x y : {z : V // z ∈ cSupp}},
      (G.induce cSupp).Adj x y → s x.1 = -s y.1)
    (x : muThreePositiveShore cSupp s)
    (y : muThreeNegativeShore cSupp s) (z : V)
    (hxz : G.Adj x.1 z) (hyz : G.Adj y.1 z) : z ∉ cSupp := by
  intro hz
  have hpx := hflip (x := ⟨x.1, x.2.1⟩) (y := ⟨z, hz⟩) hxz
  have hny := hflip (x := ⟨y.1, y.2.1⟩) (y := ⟨z, hz⟩) hyz
  change s x.1 = -s z at hpx
  change s y.1 = -s z at hny
  have hxs : s x.1 = 1 := x.2.2
  have hys : s y.1 = -1 := y.2.2
  omega

/-- On an internal signed edge, being a missing cell is equivalent to being
an ambient triangle-free edge. -/
theorem orderSixtyFourMuThree_hole_iff_triangleFreeEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {cSupp : Set V} {s : V → ℤ}
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (hadj : ∀ u, G.Adj u.1 (label u).1.1 ∧ G.Adj u.1 (label u).2.1)
    (huniqueP : ∀ u p, G.Adj u.1 p.1 → (label u).1 = p)
    (huniqueN : ∀ u n, G.Adj u.1 n.1 → (label u).2 = n)
    (hflip : ∀ {x y : {z : V // z ∈ cSupp}},
      (G.induce cSupp).Adj x y → s x.1 = -s y.1)
    (x : muThreePositiveShore cSupp s)
    (y : muThreeNegativeShore cSupp s)
    (hxy : orderSixtyFourMuThreeInternalRel G x y) :
    orderSixtyFourMuThreeHole label x y ↔
      (triangleFreeEdgeGraph G).Adj x.1 y.1 := by
  rw [triangleFreeEdgeGraph_adj, mem_triangleFreeNeighbors]
  refine ⟨fun hhole => ⟨hxy, ?_⟩, fun htf => ?_⟩
  · by_contra hcard
    have hnon : (G.neighborFinset x.1 ∩ G.neighborFinset y.1).Nonempty :=
      Finset.card_ne_zero.mp hcard
    obtain ⟨z, hz⟩ := hnon
    have hxz : G.Adj x.1 z := by
      exact (G.mem_neighborFinset x.1 z).mp (Finset.mem_inter.mp hz).1
    have hyz : G.Adj y.1 z := by
      exact (G.mem_neighborFinset y.1 z).mp (Finset.mem_inter.mp hz).2
    have hzout := orderSixtyFourMuThree_internalEdge_commonNeighbor_not_mem
      G hflip x y z hxz hyz
    have hnot := (orderSixtyFourMuThree_not_hole_iff_exterior_commonNeighbor
      G label hadj huniqueP huniqueN x y).2 ⟨⟨z, hzout⟩, hxz.symm, hyz.symm⟩
    exact hnot hhole
  · by_contra hnotHole
    obtain ⟨u, hux, huy⟩ :=
      (orderSixtyFourMuThree_not_hole_iff_exterior_commonNeighbor
        G label hadj huniqueP huniqueN x y).1 hnotHole
    have huMem : u.1 ∈ G.neighborFinset x.1 ∩ G.neighborFinset y.1 := by
      simp only [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hux.symm, huy.symm⟩
    have : (G.neighborFinset x.1 ∩ G.neighborFinset y.1).card ≠ 0 := by
      rw [Finset.card_ne_zero]
      exact ⟨u.1, huMem⟩
    exact this htf.2

/-- Forget the shore tag on the bipartite presentation of the internal
signed graph. -/
def orderSixtyFourMuThreeInternalBipartiteHom
    {V : Type*} (G : SimpleGraph V) {cSupp : Set V} {s : V → ℤ} :
    relationBipartiteGraph (orderSixtyFourMuThreeInternalRel G
      (cSupp := cSupp) (s := s)) →g G.induce cSupp where
  toFun
    | Sum.inl x => ⟨x.1, x.2.1⟩
    | Sum.inr y => ⟨y.1, y.2.1⟩
  map_rel' := by
    intro a b hab
    cases a <;> cases b <;>
      simp only [relationBipartiteGraph, orderSixtyFourMuThreeInternalRel] at hab ⊢
    · exact hab
    · exact hab.symm

/-- If the ambient triangle-free degree is two at a vertex of a size-two
component, then each of its two internal ambient edges is triangle-free. -/
theorem orderSixtyFourMuThree_triangleFreeEdge_of_degree_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hdeg : ∀ x : c.supp, (G.induce c.supp).degree x = 2)
    (x y : c.supp) (hxy : (G.induce c.supp).Adj x y)
    (htwo : (triangleFreeEdgeGraph G).degree x.1 = 2) :
    (triangleFreeEdgeGraph G).Adj x.1 y.1 := by
  classical
  let I : Finset V := ((G.induce c.supp).neighborFinset x).map
    ⟨Subtype.val, Subtype.val_injective⟩
  have hIcard : I.card = 2 := by
    simp only [I, Finset.card_map,
      (G.induce c.supp).card_neighborFinset_eq_degree, hdeg]
  have hsub : (triangleFreeEdgeGraph G).neighborFinset x.1 ⊆ I := by
    intro z hz
    have htf : (triangleFreeEdgeGraph G).Adj x.1 z :=
      ((triangleFreeEdgeGraph G).mem_neighborFinset x.1 z).mp hz
    have hD : (secondOrderDefectGraph G).Adj x.1 z := by
      exact Or.inr htf
    have hzSupp : z ∈ c.supp := by
      rw [ConnectedComponent.mem_supp_iff]
      exact (ConnectedComponent.connectedComponentMk_eq_of_adj hD).symm.trans
        ((ConnectedComponent.mem_supp_iff c x.1).mp x.2)
    simp only [I, Finset.mem_map]
    refine ⟨⟨z, hzSupp⟩, ?_, rfl⟩
    exact ((G.induce c.supp).mem_neighborFinset x ⟨z, hzSupp⟩).mpr
      ((mem_triangleFreeNeighbors G x.1 z).mp htf).1
  have hTFcard : ((triangleFreeEdgeGraph G).neighborFinset x.1).card = 2 := by
    rw [(triangleFreeEdgeGraph G).card_neighborFinset_eq_degree, htwo]
  have heq : (triangleFreeEdgeGraph G).neighborFinset x.1 = I :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  apply ((triangleFreeEdgeGraph G).mem_neighborFinset x.1 y.1).mp
  rw [heq]
  simp only [I, Finset.mem_map]
  exact ⟨y, ((G.induce c.supp).mem_neighborFinset x y).mpr hxy, rfl⟩

/-- The canonical missing-cell factor is constant on every cycle of the
internal ambient two-factor. -/
theorem orderSixtyFourMuThree_cycleCompatible
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcardV : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (label : muThreeExterior c.supp →
      muThreePositiveShore c.supp s × muThreeNegativeShore c.supp s)
    (hadj : ∀ u, G.Adj u.1 (label u).1.1 ∧ G.Adj u.1 (label u).2.1)
    (huniqueP : ∀ u p, G.Adj u.1 p.1 → (label u).1 = p)
    (huniqueN : ∀ u n, G.Adj u.1 n.1 → (label u).2 = n)
    (hflip : ∀ {x y : {z : V // z ∈ c.supp}},
      (G.induce c.supp).Adj x y → s x.1 = -s y.1)
    (hdeg : ∀ x : c.supp, (G.induce c.supp).degree x = 2) :
    RelationFactorCycleCompatible
      (orderSixtyFourMuThreeInternalRel G)
      (orderSixtyFourMuThreeHole label) := by
  classical
  intro d
  by_cases hex : ∃ x y,
      orderSixtyFourMuThreeInternalRel G x y ∧
      Sum.inl x ∈ d.supp ∧ orderSixtyFourMuThreeHole label x y
  · left
    obtain ⟨x₀, y₀, hx₀y₀, hx₀d, hk₀⟩ := hex
    have htf₀ : (triangleFreeEdgeGraph G).Adj x₀.1 y₀.1 :=
      (orderSixtyFourMuThree_hole_iff_triangleFreeEdge
        G label hadj huniqueP huniqueN hflip x₀ y₀ hx₀y₀).mp hk₀
    let x₀i : c.supp := ⟨x₀.1, x₀.2.1⟩
    have hdegTf₀ : (triangleFreeEdgeGraph G).degree x₀.1 = 2 := by
      rcases binarySquare_regular_sizeTwoPart_triangleFree_degree_eq_zero_or_two
          G hfree (q := 8) (by omega) (by decide) hreg hcardV c hc x₀i with hzero | htwo
      · have hpos := htf₀.degree_pos_left
        change (triangleFreeEdgeGraph G).degree x₀.1 = 0 at hzero
        omega
      · exact htwo
    intro x y hxy hxd
    let xi : c.supp := ⟨x.1, x.2.1⟩
    have hreachB :
        (relationBipartiteGraph (orderSixtyFourMuThreeInternalRel G)).Reachable
          (Sum.inl x₀) (Sum.inl x) := by
      apply ConnectedComponent.exact
      exact ((ConnectedComponent.mem_supp_iff d (Sum.inl x₀)).mp hx₀d).trans
        ((ConnectedComponent.mem_supp_iff d (Sum.inl x)).mp hxd).symm
    have hreachI : (G.induce c.supp).Reachable x₀i xi := by
      exact hreachB.map (orderSixtyFourMuThreeInternalBipartiteHom G)
    have hdegTfx : (triangleFreeEdgeGraph G).degree x.1 = 2 :=
      (binarySquare_regular_sizeTwoPart_triangleFree_degree_two_iff_of_reachable
        G hfree (q := 8) (by omega) (by decide) hreg hcardV c hc x₀i xi hreachI).mp
          hdegTf₀
    have htfxy : (triangleFreeEdgeGraph G).Adj x.1 y.1 :=
      orderSixtyFourMuThree_triangleFreeEdge_of_degree_two G c hdeg xi
        ⟨y.1, y.2.1⟩ hxy hdegTfx
    exact (orderSixtyFourMuThree_hole_iff_triangleFreeEdge
      G label hadj huniqueP huniqueN hflip x y hxy).mpr htfxy
  · right
    intro x y hxy hxd hk
    exact hex ⟨x, y, hxy, hxd, hk⟩

/-- A positive-shore relation fiber is the full induced-graph neighbor
fiber, because every internal edge flips the sign. -/
def orderSixtyFourMuThreePositiveNeighborEquiv
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {cSupp : Set V} {s : V → ℤ}
    (hflip : ∀ ⦃x y : {z : V // z ∈ cSupp}⦄,
      (G.induce cSupp).Adj x y → s x.1 = -s y.1)
    (x : muThreePositiveShore cSupp s) :
    {y : muThreeNegativeShore cSupp s // G.Adj x.1 y.1} ≃
      {z : {z : V // z ∈ cSupp} //
        (G.induce cSupp).Adj ⟨x.1, x.2.1⟩ z} where
  toFun y := ⟨⟨y.1.1, y.1.2.1⟩, y.2⟩
  invFun z := ⟨⟨z.1.1, z.1.2, by
    have h := hflip z.2
    have hx : s x.1 = 1 := x.2.2
    have h' : (1 : ℤ) = -s z.1.1 := by simpa only [hx] using h
    omega⟩, z.2⟩
  left_inv y := by rfl
  right_inv z := by rfl

/-- Column-dual identification of a negative-shore relation fiber with the
full internal neighbor fiber. -/
def orderSixtyFourMuThreeNegativeNeighborEquiv
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {cSupp : Set V} {s : V → ℤ}
    (hflip : ∀ ⦃x y : {z : V // z ∈ cSupp}⦄,
      (G.induce cSupp).Adj x y → s x.1 = -s y.1)
    (y : muThreeNegativeShore cSupp s) :
    {x : muThreePositiveShore cSupp s // G.Adj x.1 y.1} ≃
      {z : {z : V // z ∈ cSupp} //
        (G.induce cSupp).Adj ⟨y.1, y.2.1⟩ z} where
  toFun x := ⟨⟨x.1.1, x.1.2.1⟩, (G.adj_comm _ _).mp x.2⟩
  invFun z := ⟨⟨z.1.1, z.1.2, by
    have h := hflip z.2
    have hy : s y.1 = -1 := y.2.2
    have h' : (-1 : ℤ) = -s z.1.1 := by simpa only [hy] using h
    omega⟩, (G.adj_comm _ _).mpr z.2⟩
  left_inv x := by rfl
  right_inv z := by rfl

/-- A two-regular signed internal component whose edges flip sign gives a
two-regular bipartite relation on its sign shores. -/
theorem orderSixtyFourMuThreeInternalRel_twoRegular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {cSupp : Set V} {s : V → ℤ}
    [Fintype {z : V // z ∈ cSupp}]
    [Fintype (muThreePositiveShore cSupp s)]
    [Fintype (muThreeNegativeShore cSupp s)]
    (hdeg : ∀ z : {z : V // z ∈ cSupp},
      (G.induce cSupp).degree z = 2)
    (hflip : ∀ ⦃x y : {z : V // z ∈ cSupp}⦄,
      (G.induce cSupp).Adj x y → s x.1 = -s y.1) :
    RelationTwoRegular (orderSixtyFourMuThreeInternalRel G
      (cSupp := cSupp) (s := s)) := by
  classical
  constructor
  · intro x
    change ((Finset.univ : Finset (muThreeNegativeShore cSupp s)).filter
      fun y => G.Adj x.1 y.1).card = 2
    rw [← Fintype.card_subtype,
      Fintype.card_congr
        (orderSixtyFourMuThreePositiveNeighborEquiv G hflip x),
      Fintype.card_subtype]
    change ((Finset.univ : Finset {z : V // z ∈ cSupp}).filter fun z =>
      (G.induce cSupp).Adj ⟨x.1, x.2.1⟩ z).card = 2
    rw [show ((Finset.univ : Finset {z : V // z ∈ cSupp}).filter fun z =>
        (G.induce cSupp).Adj ⟨x.1, x.2.1⟩ z) =
        (G.induce cSupp).neighborFinset ⟨x.1, x.2.1⟩ by
      ext z
      simp [SimpleGraph.mem_neighborFinset]]
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using
      hdeg ⟨x.1, x.2.1⟩
  · intro y
    change ((Finset.univ : Finset (muThreePositiveShore cSupp s)).filter
      fun x => G.Adj x.1 y.1).card = 2
    rw [← Fintype.card_subtype,
      Fintype.card_congr
        (orderSixtyFourMuThreeNegativeNeighborEquiv G hflip y),
      Fintype.card_subtype]
    change ((Finset.univ : Finset {z : V // z ∈ cSupp}).filter fun z =>
      (G.induce cSupp).Adj ⟨y.1, y.2.1⟩ z).card = 2
    rw [show ((Finset.univ : Finset {z : V // z ∈ cSupp}).filter fun z =>
        (G.induce cSupp).Adj ⟨y.1, y.2.1⟩ z) =
        (G.induce cSupp).neighborFinset ⟨y.1, y.2.1⟩ by
      ext z
      simp [SimpleGraph.mem_neighborFinset]]
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using
      hdeg ⟨y.1, y.2.1⟩

/-- The transported exterior graph satisfies the mixed-grid rook law. -/
theorem orderSixtyFourMuThreeExteriorCellGraph_rook
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {cSupp : Set V} {s : V → ℤ}
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (hinj : Function.Injective label)
    (hadj : ∀ u, G.Adj u.1 (label u).1.1 ∧
      G.Adj u.1 (label u).2.1) :
    let C := orderSixtyFourMuThreeExteriorCellGraph G label hinj
    ∀ u v w, C.Adj u v → C.Adj u w → v ≠ w →
      v.1.1 ≠ w.1.1 ∧ v.1.2 ≠ w.1.2 := by
  dsimp
  intro u v w huv huw hvw
  let e := orderSixtyFourMuThreeExteriorCellEquiv label hinj
  let u' := e.symm u
  let v' := e.symm v
  let w' := e.symm w
  have huv' : G.Adj u'.1 v'.1 := by
    exact huv
  have huw' : G.Adj u'.1 w'.1 := by
    exact huw
  have hvw' : v' ≠ w' := by
    intro h
    exact hvw (e.symm.injective h)
  have hposinj : Function.Injective
      (fun z : {z : muThreeExterior cSupp // G.Adj u'.1 z.1} =>
        (label z.1).1) := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    let p := (label a.1).1
    have hpu : p.1 ≠ u'.1 := by
      intro h
      exact u'.2 (h ▸ p.2.1)
    apply c4Free_commonNeighborPair_injective G hfree hpu
    · exact (hadj a.1).1.symm
    · change G.Adj (label a.1).1.1 b.1.1
      have habv : (label a.1).1.1 = (label b.1).1.1 :=
        congrArg (fun z => z.1) hab
      rw [habv]
      exact (hadj b.1).1.symm
    · exact a.2
    · exact b.2
  have hneginj : Function.Injective
      (fun z : {z : muThreeExterior cSupp // G.Adj u'.1 z.1} =>
        (label z.1).2) := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    let n := (label a.1).2
    have hnu : n.1 ≠ u'.1 := by
      intro h
      exact u'.2 (h ▸ n.2.1)
    apply c4Free_commonNeighborPair_injective G hfree hnu
    · exact (hadj a.1).2.symm
    · change G.Adj (label a.1).2.1 b.1.1
      have habv : (label a.1).2.1 = (label b.1).2.1 :=
        congrArg (fun z => z.1) hab
      rw [habv]
      exact (hadj b.1).2.symm
    · exact a.2
    · exact b.2
  have hlabel_v : label v' = v.1 := by
    exact congrArg (fun p => p.1) (e.apply_symm_apply v)
  have hlabel_w : label w' = w.1 := by
    exact congrArg (fun p => p.1) (e.apply_symm_apply w)
  constructor
  · intro hcoord
    let vv : {z : muThreeExterior cSupp // G.Adj u'.1 z.1} := ⟨v', huv'⟩
    let ww : {z : muThreeExterior cSupp // G.Adj u'.1 z.1} := ⟨w', huw'⟩
    have heq : (label vv.1).1 = (label ww.1).1 := by
      simpa [vv, ww, hlabel_v, hlabel_w] using hcoord
    have := hposinj heq
    exact hvw' (congrArg (fun z => z.1) this)
  · intro hcoord
    let vv : {z : muThreeExterior cSupp // G.Adj u'.1 z.1} := ⟨v', huv'⟩
    let ww : {z : muThreeExterior cSupp // G.Adj u'.1 z.1} := ⟨w', huw'⟩
    have heq : (label vv.1).2 = (label ww.1).2 := by
      simpa [vv, ww, hlabel_v, hlabel_w] using hcoord
    have := hneginj heq
    exact hvw' (congrArg (fun z => z.1) this)

/-- Assembly boundary for the graph-facing constructor.  All type transport,
two-regularity, rook separation, and C4-freeness are discharged here.  The
three remaining hypotheses are precisely the graph-specific sector
propagation and exact row/column hit counts. -/
theorem orderSixtyFourMuThree_mixedGridCode_of_hitLaws
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {cSupp : Set V} {s : V → ℤ}
    [Fintype {z : V // z ∈ cSupp}]
    [Fintype (muThreePositiveShore cSupp s)]
    [Fintype (muThreeNegativeShore cSupp s)]
    [Fintype (muThreeExterior cSupp)]
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (hinj : Function.Injective label)
    (hadj : ∀ u, G.Adj u.1 (label u).1.1 ∧
      G.Adj u.1 (label u).2.1)
    (hP : Fintype.card (muThreePositiveShore cSupp s) = 8)
    (hN : Fintype.card (muThreeNegativeShore cSupp s) = 8)
    (hdeg : ∀ z : {z : V // z ∈ cSupp},
      (G.induce cSupp).degree z = 2)
    (hflip : ∀ ⦃x y : {z : V // z ∈ cSupp}⦄,
      (G.induce cSupp).Adj x y → s x.1 = -s y.1)
    (hrowFiber : ∀ x, Fintype.card
      {u : muThreeExterior cSupp // (label u).1 = x} = 6)
    (hcolumnFiber : ∀ y, Fintype.card
      {u : muThreeExterior cSupp // (label u).2 = y} = 6)
    (hcycle : RelationFactorCycleCompatible
      (orderSixtyFourMuThreeInternalRel G (cSupp := cSupp) (s := s))
      (orderSixtyFourMuThreeHole label))
    (hrowHit : ∀
      (u : muThreeMixedCell (orderSixtyFourMuThreeHole label))
      (x : muThreePositiveShore cSupp s),
      (((orderSixtyFourMuThreeExteriorCellGraph G label hinj).neighborFinset u).filter
        fun v => v.1.1 = x).card =
          if orderSixtyFourMuThreeInternalRel G x u.1.2 then 0 else 1)
    (hcolumnHit : ∀
      (u : muThreeMixedCell (orderSixtyFourMuThreeHole label))
      (y : muThreeNegativeShore cSupp s),
      (((orderSixtyFourMuThreeExteriorCellGraph G label hinj).neighborFinset u).filter
        fun v => v.1.2 = y).card =
          if orderSixtyFourMuThreeInternalRel G u.1.1 y then 0 else 1) :
    MuThreeMixedGridCode
      (orderSixtyFourMuThreeInternalRel G (cSupp := cSupp) (s := s))
      (orderSixtyFourMuThreeHole label)
      (orderSixtyFourMuThreeExteriorCellGraph G label hinj) where
  card_left := hP
  card_right := hN
  H_twoRegular := orderSixtyFourMuThreeInternalRel_twoRegular G hdeg hflip
  K_twoRegular := orderSixtyFourMuThreeHole_twoRegular label hinj hP hN
    hrowFiber hcolumnFiber
  cycle_compatible := hcycle
  row_hit := hrowHit
  column_hit := hcolumnHit
  rook := orderSixtyFourMuThreeExteriorCellGraph_rook
    G hfree label hinj hadj
  c4Free := orderSixtyFourMuThreeExteriorCellGraph_c4Free
    G hfree label hinj

/-- Uniqueness of the positive signed internal neighbor identifies any such
neighbor with the positive label coordinate. -/
theorem orderSixtyFourMuThree_label_positive_eq_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {cSupp : Set V} {s : V → ℤ}
    [DecidablePred (fun z : V => z ∈ cSupp)]
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (hadj : ∀ u, G.Adj u.1 (label u).1.1 ∧
      G.Adj u.1 (label u).2.1)
    (hone : ∀ u : muThreeExterior cSupp,
      ((G.neighborFinset u.1).filter fun z => z ∈ cSupp ∧ s z = 1).card = 1)
    (u : muThreeExterior cSupp) (p : muThreePositiveShore cSupp s)
    (hup : G.Adj u.1 p.1) : (label u).1 = p := by
  let A := (G.neighborFinset u.1).filter fun z => z ∈ cSupp ∧ s z = 1
  apply Subtype.ext
  have hle : A.card ≤ 1 := by rw [show A.card = 1 by simpa [A] using hone u]
  apply Finset.card_le_one.mp hle
  · exact Finset.mem_filter.mpr
      ⟨(G.mem_neighborFinset u.1 (label u).1.1).mpr (hadj u).1,
        (label u).1.2⟩
  · exact Finset.mem_filter.mpr
      ⟨(G.mem_neighborFinset u.1 p.1).mpr hup, p.2⟩

/-- Negative-coordinate dual of
`orderSixtyFourMuThree_label_positive_eq_of_adj`. -/
theorem orderSixtyFourMuThree_label_negative_eq_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {cSupp : Set V} {s : V → ℤ}
    [DecidablePred (fun z : V => z ∈ cSupp)]
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (hadj : ∀ u, G.Adj u.1 (label u).1.1 ∧
      G.Adj u.1 (label u).2.1)
    (hone : ∀ u : muThreeExterior cSupp,
      ((G.neighborFinset u.1).filter fun z => z ∈ cSupp ∧ s z = -1).card = 1)
    (u : muThreeExterior cSupp) (n : muThreeNegativeShore cSupp s)
    (hun : G.Adj u.1 n.1) : (label u).2 = n := by
  let A := (G.neighborFinset u.1).filter fun z => z ∈ cSupp ∧ s z = -1
  apply Subtype.ext
  have hle : A.card ≤ 1 := by rw [show A.card = 1 by simpa [A] using hone u]
  apply Finset.card_le_one.mp hle
  · exact Finset.mem_filter.mpr
      ⟨(G.mem_neighborFinset u.1 (label u).2.1).mpr (hadj u).2,
        (label u).2.2⟩
  · exact Finset.mem_filter.mpr
      ⟨(G.mem_neighborFinset u.1 n.1).mpr hun, n.2⟩

/-- A label row fiber is the same set as the exterior neighbor fiber of its
internal positive vertex. -/
def orderSixtyFourMuThreeLabelRowFiberEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {cSupp : Set V} {s : V → ℤ}
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (hadj : ∀ u, G.Adj u.1 (label u).1.1 ∧
      G.Adj u.1 (label u).2.1)
    (hunique : ∀ u p, G.Adj u.1 p.1 → (label u).1 = p)
    (p : muThreePositiveShore cSupp s) :
    {u : muThreeExterior cSupp // (label u).1 = p} ≃
      {u : muThreeExterior cSupp // G.Adj p.1 u.1} where
  toFun u := ⟨u.1, by
    convert (hadj u.1).1.symm using 1
    exact (congrArg (fun z => z.1) u.2).symm⟩
  invFun u := ⟨u.1, hunique u.1 p ((G.adj_comm _ _).mp u.2)⟩
  left_inv u := by rfl
  right_inv u := by rfl

/-- Column-dual label fiber equivalence. -/
def orderSixtyFourMuThreeLabelColumnFiberEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {cSupp : Set V} {s : V → ℤ}
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (hadj : ∀ u, G.Adj u.1 (label u).1.1 ∧
      G.Adj u.1 (label u).2.1)
    (hunique : ∀ u n, G.Adj u.1 n.1 → (label u).2 = n)
    (n : muThreeNegativeShore cSupp s) :
    {u : muThreeExterior cSupp // (label u).2 = n} ≃
      {u : muThreeExterior cSupp // G.Adj n.1 u.1} where
  toFun u := ⟨u.1, by
    convert (hadj u.1).2.symm using 1
    exact (congrArg (fun z => z.1) u.2).symm⟩
  invFun u := ⟨u.1, hunique u.1 n ((G.adj_comm _ _).mp u.2)⟩
  left_inv u := by rfl
  right_inv u := by rfl

def orderSixtyFourMuThreeOutsideNeighborEquiv
    {V : Type*} (G : SimpleGraph V) (cSupp : Set V) (z : V) :
    {u : muThreeExterior cSupp // G.Adj z u.1} ≃
      {u : V // G.Adj z u ∧ u ∉ cSupp} where
  toFun u := ⟨u.1.1, u.2, u.1.2⟩
  invFun u := ⟨⟨u.1, u.2.2⟩, u.2.1⟩
  left_inv u := by rfl
  right_inv u := by rfl

/-- The ambient exterior-neighbor count supplies the required six-element
positive label fiber. -/
theorem orderSixtyFourMuThreeLabelRowFiber_card_eq_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {cSupp : Set V} {s : V → ℤ}
    [DecidablePred (fun z : V => z ∈ cSupp)]
    [Fintype (muThreeExterior cSupp)]
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (hadj : ∀ u, G.Adj u.1 (label u).1.1 ∧
      G.Adj u.1 (label u).2.1)
    (hunique : ∀ u p, G.Adj u.1 p.1 → (label u).1 = p)
    (p : muThreePositiveShore cSupp s)
    (hout : ((G.neighborFinset p.1).filter fun u => u ∉ cSupp).card = 6) :
    Fintype.card {u : muThreeExterior cSupp // (label u).1 = p} = 6 := by
  rw [Fintype.card_congr
      (orderSixtyFourMuThreeLabelRowFiberEquiv G label hadj hunique p),
    Fintype.card_congr
      (orderSixtyFourMuThreeOutsideNeighborEquiv G cSupp p.1),
    Fintype.card_subtype]
  change ((Finset.univ : Finset V).filter fun u =>
    G.Adj p.1 u ∧ u ∉ cSupp).card = 6
  rw [show ((Finset.univ : Finset V).filter fun u =>
      G.Adj p.1 u ∧ u ∉ cSupp) =
      (G.neighborFinset p.1).filter (fun u => u ∉ cSupp) by
    ext u
    simp [SimpleGraph.mem_neighborFinset, G.adj_comm]]
  exact hout

/-- Column-dual six-element label fiber. -/
theorem orderSixtyFourMuThreeLabelColumnFiber_card_eq_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {cSupp : Set V} {s : V → ℤ}
    [DecidablePred (fun z : V => z ∈ cSupp)]
    [Fintype (muThreeExterior cSupp)]
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (hadj : ∀ u, G.Adj u.1 (label u).1.1 ∧
      G.Adj u.1 (label u).2.1)
    (hunique : ∀ u n, G.Adj u.1 n.1 → (label u).2 = n)
    (n : muThreeNegativeShore cSupp s)
    (hout : ((G.neighborFinset n.1).filter fun u => u ∉ cSupp).card = 6) :
    Fintype.card {u : muThreeExterior cSupp // (label u).2 = n} = 6 := by
  rw [Fintype.card_congr
      (orderSixtyFourMuThreeLabelColumnFiberEquiv G label hadj hunique n),
    Fintype.card_congr
      (orderSixtyFourMuThreeOutsideNeighborEquiv G cSupp n.1),
    Fintype.card_subtype]
  change ((Finset.univ : Finset V).filter fun u =>
    G.Adj n.1 u ∧ u ∉ cSupp).card = 6
  rw [show ((Finset.univ : Finset V).filter fun u =>
      G.Adj n.1 u ∧ u ∉ cSupp) =
      (G.neighborFinset n.1).filter (fun u => u ∉ cSupp) by
    ext u
    simp [SimpleGraph.mem_neighborFinset, G.adj_comm]]
  exact hout

/-- An exact coordinate-image formula plus rook injectivity turns into the
literal zero/one row-hit count used by `MuThreeMixedGridCode`. -/
theorem orderSixtyFourMuThree_exteriorLabelRowHit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {cSupp : Set V} {s : V → ℤ}
    [Fintype (muThreeExterior cSupp)]
    [Fintype (muThreePositiveShore cSupp s)]
    (H : muThreePositiveShore cSupp s →
      muThreeNegativeShore cSupp s → Prop) [DecidableRel H]
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (u : muThreeExterior cSupp)
    (hinj : Set.InjOn (fun v => (label v).1)
      ((Finset.univ.filter fun v : muThreeExterior cSupp =>
        G.Adj u.1 v.1) : Set _))
    (himage : (Finset.univ.filter fun v : muThreeExterior cSupp =>
        G.Adj u.1 v.1).image (fun v => (label v).1) =
      Finset.univ.filter fun x => ¬ H x (label u).2)
    (x : muThreePositiveShore cSupp s) :
    ((Finset.univ.filter fun v : muThreeExterior cSupp =>
      G.Adj u.1 v.1).filter fun v => (label v).1 = x).card =
        if H x (label u).2 then 0 else 1 := by
  classical
  let L := Finset.univ.filter fun v : muThreeExterior cSupp => G.Adj u.1 v.1
  let A := L.filter fun v => (label v).1 = x
  have hAle : A.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro v hv w hw
    apply hinj (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hw).1
    exact (Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm
  by_cases hx : H x (label u).2
  · rw [if_pos hx]
    change A.card = 0
    rw [Finset.card_eq_zero]
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hnonempty
    obtain ⟨v, hv⟩ := hnonempty
    have hximage : x ∈ L.image (fun z => (label z).1) :=
      Finset.mem_image.mpr ⟨v, (Finset.mem_filter.mp hv).1,
        (Finset.mem_filter.mp hv).2⟩
    rw [himage] at hximage
    exact (Finset.mem_filter.mp hximage).2 hx
  · rw [if_neg hx]
    change A.card = 1
    have hxrhs : x ∈ Finset.univ.filter fun z => ¬ H z (label u).2 := by
      simp [hx]
    rw [← himage] at hxrhs
    obtain ⟨v, hvL, hvx⟩ := Finset.mem_image.mp hxrhs
    have hnonempty : A.Nonempty :=
      ⟨v, Finset.mem_filter.mpr ⟨hvL, hvx⟩⟩
    have hApos : 0 < A.card := Finset.card_pos.mpr hnonempty
    omega

/-- Column-dual exterior zero/one hit count. -/
theorem orderSixtyFourMuThree_exteriorLabelColumnHit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {cSupp : Set V} {s : V → ℤ}
    [Fintype (muThreeExterior cSupp)]
    [Fintype (muThreeNegativeShore cSupp s)]
    (H : muThreePositiveShore cSupp s →
      muThreeNegativeShore cSupp s → Prop) [DecidableRel H]
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (u : muThreeExterior cSupp)
    (hinj : Set.InjOn (fun v => (label v).2)
      ((Finset.univ.filter fun v : muThreeExterior cSupp =>
        G.Adj u.1 v.1) : Set _))
    (himage : (Finset.univ.filter fun v : muThreeExterior cSupp =>
        G.Adj u.1 v.1).image (fun v => (label v).2) =
      Finset.univ.filter fun y => ¬ H (label u).1 y)
    (y : muThreeNegativeShore cSupp s) :
    ((Finset.univ.filter fun v : muThreeExterior cSupp =>
      G.Adj u.1 v.1).filter fun v => (label v).2 = y).card =
        if H (label u).1 y then 0 else 1 := by
  classical
  let L := Finset.univ.filter fun v : muThreeExterior cSupp => G.Adj u.1 v.1
  let A := L.filter fun v => (label v).2 = y
  have hAle : A.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro v hv w hw
    apply hinj (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hw).1
    exact (Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm
  by_cases hy : H (label u).1 y
  · rw [if_pos hy]
    change A.card = 0
    rw [Finset.card_eq_zero]
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hnonempty
    obtain ⟨v, hv⟩ := hnonempty
    have hyimage : y ∈ L.image (fun z => (label z).2) :=
      Finset.mem_image.mpr ⟨v, (Finset.mem_filter.mp hv).1,
        (Finset.mem_filter.mp hv).2⟩
    rw [himage] at hyimage
    exact (Finset.mem_filter.mp hyimage).2 hy
  · rw [if_neg hy]
    change A.card = 1
    have hyrhs : y ∈ Finset.univ.filter fun z => ¬ H (label u).1 z := by
      simp [hy]
    rw [← himage] at hyrhs
    obtain ⟨v, hvL, hvy⟩ := Finset.mem_image.mp hyrhs
    have hnonempty : A.Nonempty :=
      ⟨v, Finset.mem_filter.mpr ⟨hvL, hvy⟩⟩
    have hApos : 0 < A.card := Finset.card_pos.mpr hnonempty
    omega

/-- Relabel the row-constrained neighbor fiber of an occupied cell back to
the corresponding exterior-label fiber. -/
def orderSixtyFourMuThreeCellRowNeighborEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {cSupp : Set V} {s : V → ℤ}
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (hinj : Function.Injective label)
    (u : muThreeMixedCell (orderSixtyFourMuThreeHole label))
    (x : muThreePositiveShore cSupp s) :
    {v : muThreeMixedCell (orderSixtyFourMuThreeHole label) //
      (orderSixtyFourMuThreeExteriorCellGraph G label hinj).Adj u v ∧
        v.1.1 = x} ≃
    {v : muThreeExterior cSupp //
      G.Adj ((orderSixtyFourMuThreeExteriorCellEquiv label hinj).symm u).1 v.1 ∧
        (label v).1 = x} where
  toFun v := ⟨(orderSixtyFourMuThreeExteriorCellEquiv label hinj).symm v.1,
    v.2.1, by
      have h := congrArg (fun p => p.1.1)
        ((orderSixtyFourMuThreeExteriorCellEquiv label hinj).apply_symm_apply v.1)
      exact h.trans v.2.2⟩
  invFun v := ⟨orderSixtyFourMuThreeExteriorCellEquiv label hinj v.1,
    by
      change G.Adj
        ((orderSixtyFourMuThreeExteriorCellEquiv label hinj).symm u).1
        ((orderSixtyFourMuThreeExteriorCellEquiv label hinj).symm
          (orderSixtyFourMuThreeExteriorCellEquiv label hinj v.1)).1
      simpa using v.2.1,
    by exact v.2.2⟩
  left_inv v := by
    apply Subtype.ext
    exact (orderSixtyFourMuThreeExteriorCellEquiv label hinj).apply_symm_apply v.1
  right_inv v := by
    apply Subtype.ext
    exact (orderSixtyFourMuThreeExteriorCellEquiv label hinj).symm_apply_apply v.1

/-- Column-dual constrained-neighbor relabeling. -/
def orderSixtyFourMuThreeCellColumnNeighborEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {cSupp : Set V} {s : V → ℤ}
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (hinj : Function.Injective label)
    (u : muThreeMixedCell (orderSixtyFourMuThreeHole label))
    (y : muThreeNegativeShore cSupp s) :
    {v : muThreeMixedCell (orderSixtyFourMuThreeHole label) //
      (orderSixtyFourMuThreeExteriorCellGraph G label hinj).Adj u v ∧
        v.1.2 = y} ≃
    {v : muThreeExterior cSupp //
      G.Adj ((orderSixtyFourMuThreeExteriorCellEquiv label hinj).symm u).1 v.1 ∧
        (label v).2 = y} where
  toFun v := ⟨(orderSixtyFourMuThreeExteriorCellEquiv label hinj).symm v.1,
    v.2.1, by
      have h := congrArg (fun p => p.1.2)
        ((orderSixtyFourMuThreeExteriorCellEquiv label hinj).apply_symm_apply v.1)
      exact h.trans v.2.2⟩
  invFun v := ⟨orderSixtyFourMuThreeExteriorCellEquiv label hinj v.1,
    by
      change G.Adj
        ((orderSixtyFourMuThreeExteriorCellEquiv label hinj).symm u).1
        ((orderSixtyFourMuThreeExteriorCellEquiv label hinj).symm
          (orderSixtyFourMuThreeExteriorCellEquiv label hinj v.1)).1
      simpa using v.2.1,
    by exact v.2.2⟩
  left_inv v := by
    apply Subtype.ext
    exact (orderSixtyFourMuThreeExteriorCellEquiv label hinj).apply_symm_apply v.1
  right_inv v := by
    apply Subtype.ext
    exact (orderSixtyFourMuThreeExteriorCellEquiv label hinj).symm_apply_apply v.1

/-- Transport exterior zero/one row counts to the occupied-cell graph. -/
theorem orderSixtyFourMuThreeExteriorCellGraph_rowHit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {cSupp : Set V} {s : V → ℤ}
    [Fintype (muThreeExterior cSupp)]
    [Fintype (muThreePositiveShore cSupp s)]
    [Fintype (muThreeNegativeShore cSupp s)]
    (H : muThreePositiveShore cSupp s →
      muThreeNegativeShore cSupp s → Prop) [DecidableRel H]
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (hinj : Function.Injective label)
    (hext : ∀ (u : muThreeExterior cSupp) x,
      ((Finset.univ.filter fun v : muThreeExterior cSupp =>
        G.Adj u.1 v.1).filter fun v => (label v).1 = x).card =
          if H x (label u).2 then 0 else 1) :
    ∀ (u : muThreeMixedCell (orderSixtyFourMuThreeHole label)) x,
      (((orderSixtyFourMuThreeExteriorCellGraph G label hinj).neighborFinset u).filter
        fun v => v.1.1 = x).card = if H x u.1.2 then 0 else 1 := by
  intro u x
  have hcard :
      (((orderSixtyFourMuThreeExteriorCellGraph G label hinj).neighborFinset u).filter
        fun v => v.1.1 = x).card =
      Fintype.card {v //
        (orderSixtyFourMuThreeExteriorCellGraph G label hinj).Adj u v ∧
          v.1.1 = x} := by
    rw [Fintype.card_subtype]
    congr 1
    ext v
    simp [SimpleGraph.mem_neighborFinset]
  rw [hcard]
  rw [Fintype.card_congr
    (orderSixtyFourMuThreeCellRowNeighborEquiv G label hinj u x),
    Fintype.card_subtype]
  change ((Finset.univ : Finset (muThreeExterior cSupp)).filter fun v =>
    G.Adj ((orderSixtyFourMuThreeExteriorCellEquiv label hinj).symm u).1 v.1 ∧
      (label v).1 = x).card = _
  rw [show ((Finset.univ : Finset (muThreeExterior cSupp)).filter fun v =>
      G.Adj ((orderSixtyFourMuThreeExteriorCellEquiv label hinj).symm u).1 v.1 ∧
        (label v).1 = x) =
      (Finset.univ.filter fun v : muThreeExterior cSupp =>
        G.Adj ((orderSixtyFourMuThreeExteriorCellEquiv label hinj).symm u).1 v.1).filter
          (fun v => (label v).1 = x) by ext v; simp]
  have h := hext ((orderSixtyFourMuThreeExteriorCellEquiv label hinj).symm u) x
  have hu := congrArg (fun p => p.1.2)
    ((orderSixtyFourMuThreeExteriorCellEquiv label hinj).apply_symm_apply u)
  rw [← hu]
  exact h

/-- Column-dual transport of exterior zero/one counts. -/
theorem orderSixtyFourMuThreeExteriorCellGraph_columnHit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {cSupp : Set V} {s : V → ℤ}
    [Fintype (muThreeExterior cSupp)]
    [Fintype (muThreePositiveShore cSupp s)]
    [Fintype (muThreeNegativeShore cSupp s)]
    (H : muThreePositiveShore cSupp s →
      muThreeNegativeShore cSupp s → Prop) [DecidableRel H]
    (label : muThreeExterior cSupp →
      muThreePositiveShore cSupp s × muThreeNegativeShore cSupp s)
    (hinj : Function.Injective label)
    (hext : ∀ (u : muThreeExterior cSupp) y,
      ((Finset.univ.filter fun v : muThreeExterior cSupp =>
        G.Adj u.1 v.1).filter fun v => (label v).2 = y).card =
          if H (label u).1 y then 0 else 1) :
    ∀ (u : muThreeMixedCell (orderSixtyFourMuThreeHole label)) y,
      (((orderSixtyFourMuThreeExteriorCellGraph G label hinj).neighborFinset u).filter
        fun v => v.1.2 = y).card = if H u.1.1 y then 0 else 1 := by
  intro u y
  have hcard :
      (((orderSixtyFourMuThreeExteriorCellGraph G label hinj).neighborFinset u).filter
        fun v => v.1.2 = y).card =
      Fintype.card {v //
        (orderSixtyFourMuThreeExteriorCellGraph G label hinj).Adj u v ∧
          v.1.2 = y} := by
    rw [Fintype.card_subtype]
    congr 1
    ext v
    simp [SimpleGraph.mem_neighborFinset]
  rw [hcard]
  rw [Fintype.card_congr
    (orderSixtyFourMuThreeCellColumnNeighborEquiv G label hinj u y),
    Fintype.card_subtype]
  change ((Finset.univ : Finset (muThreeExterior cSupp)).filter fun v =>
    G.Adj ((orderSixtyFourMuThreeExteriorCellEquiv label hinj).symm u).1 v.1 ∧
      (label v).2 = y).card = _
  rw [show ((Finset.univ : Finset (muThreeExterior cSupp)).filter fun v =>
      G.Adj ((orderSixtyFourMuThreeExteriorCellEquiv label hinj).symm u).1 v.1 ∧
        (label v).2 = y) =
      (Finset.univ.filter fun v : muThreeExterior cSupp =>
        G.Adj ((orderSixtyFourMuThreeExteriorCellEquiv label hinj).symm u).1 v.1).filter
          (fun v => (label v).2 = y) by ext v; simp]
  have h := hext ((orderSixtyFourMuThreeExteriorCellEquiv label hinj).symm u) y
  have hu := congrArg (fun p => p.1.1)
    ((orderSixtyFourMuThreeExteriorCellEquiv label hinj).apply_symm_apply u)
  rw [← hu]
  exact h

/-- Graph-facing constructor with only cycle compatibility left explicit.
All cardinality, sign-fiber, exact-hit, rook, and C4 fields are derived from
the signed order-64 mu=3 data and the chosen canonical exterior label. -/
theorem orderSixtyFour_muThree_mixedGridCode_of_label
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcardV : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hsum : ∑ x, s x = 0)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x,
      s y = 3 * s x)
    (hA_in : ∀ x, x ∈ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 * s x)
    (hA_out : ∀ x, x ∉ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 ∨
      (G.adjMatrix ℤ).mulVec s x = 0 ∨
      (G.adjMatrix ℤ).mulVec s x = 2)
    (label : muThreeExterior c.supp →
      muThreePositiveShore c.supp s × muThreeNegativeShore c.supp s)
    (hinj : Function.Injective label)
    (hadj : ∀ u, G.Adj u.1 (label u).1.1 ∧
      G.Adj u.1 (label u).2.1) :
    MuThreeMixedGridCode
      (orderSixtyFourMuThreeInternalRel G (cSupp := c.supp) (s := s))
      (orderSixtyFourMuThreeHole label)
      (orderSixtyFourMuThreeExteriorCellGraph G label hinj) := by
  classical
  let H := G.induce c.supp
  let t : c.supp → ℤ := fun x => s x.1
  have hdeg : ∀ x, H.degree x = 2 := by
    intro x
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcardV c hc x
  have hsign : ∀ x, t x = -1 ∨ t x = 1 := by
    intro x
    exact hs_in x.1 x.2
  have hneighborSum : ∀ x, ∑ y ∈ H.neighborFinset x, t y = -2 * t x := by
    intro x
    rw [← SimpleGraph.adjMatrix_mulVec_apply]
    rw [← muThree_adjMatrix_mulVec_eq_induce_mulVec_of_support_int
      G c.supp s hs_out x]
    exact hA_in x.1 x.2
  have hflip : ∀ ⦃x y⦄, H.Adj x y → t x = -t y :=
    muThree_signedFlip_of_degree_two_neighborSum H hdeg t hsign hneighborSum
  have hcards := orderSixtyFour_signedSizeTwo_signClass_cards
    G c hc s hs_in hs_out hsum
  have hP : Fintype.card (muThreePositiveShore c.supp s) = 8 := by
    rw [Fintype.card_subtype]
    rw [show (Finset.univ.filter fun x : V => x ∈ c.supp ∧ s x = 1) =
        (Finset.univ.filter fun x : V => x ∈ c.supp).filter
          (fun x => s x = 1) by ext x; simp]
    exact hcards.1
  have hN : Fintype.card (muThreeNegativeShore c.supp s) = 8 := by
    rw [Fintype.card_subtype]
    rw [show (Finset.univ.filter fun x : V => x ∈ c.supp ∧ s x = -1) =
        (Finset.univ.filter fun x : V => x ∈ c.supp).filter
          (fun x => s x = -1) by ext x; simp]
    exact hcards.2
  have hbalanced := fun u : muThreeExterior c.supp =>
    orderSixtyFour_signedSizeTwo_muThree_exterior_balancedPair
      G hfree hreg hcardV c hc s hs_in hs_out hsum hDs hA_in hA_out u.1 u.2
  have honeP : ∀ u : muThreeExterior c.supp,
      ((G.neighborFinset u.1).filter fun z => z ∈ c.supp ∧ s z = 1).card = 1 := by
    intro u
    rw [show ((G.neighborFinset u.1).filter fun z => z ∈ c.supp ∧ s z = 1) =
        ((G.neighborFinset u.1).filter fun z =>
          (secondOrderDefectGraph G).connectedComponentMk z = c).filter
            (fun z => s z = 1) by
      ext z
      simp [ConnectedComponent.mem_supp_iff, and_assoc]]
    exact (hbalanced u).1
  have honeN : ∀ u : muThreeExterior c.supp,
      ((G.neighborFinset u.1).filter fun z => z ∈ c.supp ∧ s z = -1).card = 1 := by
    intro u
    rw [show ((G.neighborFinset u.1).filter fun z => z ∈ c.supp ∧ s z = -1) =
        ((G.neighborFinset u.1).filter fun z =>
          (secondOrderDefectGraph G).connectedComponentMk z = c).filter
            (fun z => s z = -1) by
      ext z
      simp [ConnectedComponent.mem_supp_iff, and_assoc]]
    exact (hbalanced u).2
  have huniqueP : ∀ u p, G.Adj u.1 p.1 → (label u).1 = p :=
    fun u p hup => orderSixtyFourMuThree_label_positive_eq_of_adj
      G label hadj honeP u p hup
  have huniqueN : ∀ u n, G.Adj u.1 n.1 → (label u).2 = n :=
    fun u n hun => orderSixtyFourMuThree_label_negative_eq_of_adj
      G label hadj honeN u n hun
  have hcycle : RelationFactorCycleCompatible
      (orderSixtyFourMuThreeInternalRel G)
      (orderSixtyFourMuThreeHole label) := by
    exact orderSixtyFourMuThree_cycleCompatible
      G hfree hreg hcardV c hc s label hadj huniqueP huniqueN
        (fun {_ _} h => hflip h) hdeg
  have hrowFiber : ∀ p, Fintype.card
      {u : muThreeExterior c.supp // (label u).1 = p} = 6 := by
    intro p
    apply orderSixtyFourMuThreeLabelRowFiber_card_eq_six G label hadj huniqueP p
    simpa [ConnectedComponent.mem_supp_iff] using
      orderSixtyFour_sizeTwoComponent_exteriorNeighborCard_six
        G hfree hreg hcardV c hc ⟨p.1, p.2.1⟩
  have hcolumnFiber : ∀ n, Fintype.card
      {u : muThreeExterior c.supp // (label u).2 = n} = 6 := by
    intro n
    apply orderSixtyFourMuThreeLabelColumnFiber_card_eq_six G label hadj huniqueN n
    simpa [ConnectedComponent.mem_supp_iff] using
      orderSixtyFour_sizeTwoComponent_exteriorNeighborCard_six
        G hfree hreg hcardV c hc ⟨n.1, n.2.1⟩
  have hout : ∀ u : muThreeExterior c.supp,
      (Finset.univ.filter fun v : muThreeExterior c.supp =>
        G.Adj u.1 v.1).card = 6 := by
    intro u
    rw [← Fintype.card_subtype,
      Fintype.card_congr
        (orderSixtyFourMuThreeOutsideNeighborEquiv G c.supp u.1),
      Fintype.card_subtype]
    change ((Finset.univ : Finset V).filter fun v =>
      G.Adj u.1 v ∧ v ∉ c.supp).card = 6
    rw [show ((Finset.univ : Finset V).filter fun v =>
        G.Adj u.1 v ∧ v ∉ c.supp) =
        (G.neighborFinset u.1).filter (fun v => v ∉ c.supp) by
      ext v
      simp [SimpleGraph.mem_neighborFinset, G.adj_comm]]
    exact orderSixtyFour_sizeTwoComponent_outsideNeighborCard_six
      G hfree hreg hcardV c hc u.1 u.2
  have hextRow : ∀ (u : muThreeExterior c.supp) x,
      ((Finset.univ.filter fun v : muThreeExterior c.supp =>
        G.Adj u.1 v.1).filter fun v => (label v).1 = x).card =
          if orderSixtyFourMuThreeInternalRel G x (label u).2 then 0 else 1 := by
    intro u x
    apply orderSixtyFourMuThree_exteriorLabelRowHit G _ label u
    · intro v hv w hw hvw
      let vv : {z : muThreeExterior c.supp // G.Adj u.1 z.1} :=
        ⟨v, (Finset.mem_filter.mp hv).2⟩
      let ww : {z : muThreeExterior c.supp // G.Adj u.1 z.1} :=
        ⟨w, (Finset.mem_filter.mp hw).2⟩
      have heq := (c4Free_exteriorGridLabel_neighbor_coordinate_injective
        G hfree c s label hadj u).1 (show (label vv.1).1 = (label ww.1).1 by
          exact hvw)
      exact congrArg (fun z => z.1) heq
    · apply c4Free_exteriorGridLabel_positiveHit_image
        G hfree c s label hadj u (hout u) hP
      exact orderSixtyFour_signedSizeTwo_negative_positiveNeighborCard_two
        G hfree hreg hcardV c hc s hs_in hs_out hA_in
          (label u).2.1 (label u).2.2.1 (label u).2.2.2
  have hextColumn : ∀ (u : muThreeExterior c.supp) y,
      ((Finset.univ.filter fun v : muThreeExterior c.supp =>
        G.Adj u.1 v.1).filter fun v => (label v).2 = y).card =
          if orderSixtyFourMuThreeInternalRel G (label u).1 y then 0 else 1 := by
    intro u y
    apply orderSixtyFourMuThree_exteriorLabelColumnHit G _ label u
    · intro v hv w hw hvw
      let vv : {z : muThreeExterior c.supp // G.Adj u.1 z.1} :=
        ⟨v, (Finset.mem_filter.mp hv).2⟩
      let ww : {z : muThreeExterior c.supp // G.Adj u.1 z.1} :=
        ⟨w, (Finset.mem_filter.mp hw).2⟩
      have heq := (c4Free_exteriorGridLabel_neighbor_coordinate_injective
        G hfree c s label hadj u).2 (show (label vv.1).2 = (label ww.1).2 by
          exact hvw)
      exact congrArg (fun z => z.1) heq
    · have hi := c4Free_exteriorGridLabel_negativeHit_image
        G hfree c s label hadj u (hout u) hN
          (orderSixtyFour_signedSizeTwo_positive_negativeNeighborCard_two
            G hfree hreg hcardV c hc s hs_in hs_out hA_in
              (label u).1.1 (label u).1.2.1 (label u).1.2.2)
      simpa [orderSixtyFourMuThreeInternalRel, G.adj_comm] using hi
  apply orderSixtyFourMuThree_mixedGridCode_of_hitLaws
    G hfree label hinj hadj hP hN hdeg hflip hrowFiber hcolumnFiber hcycle
  · exact orderSixtyFourMuThreeExteriorCellGraph_rowHit
      G _ label hinj hextRow
  · exact orderSixtyFourMuThreeExteriorCellGraph_columnHit
      G _ label hinj hextColumn

/-- Full graph-facing assembly: the order-64 signed size-two `μ = 3` data
canonically supplies a mixed-grid code, with no additional combinatorial
hypothesis. -/
theorem orderSixtyFour_muThree_exists_mixedGridCode
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcardV : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hsum : ∑ x, s x = 0)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x,
      s y = 3 * s x)
    (hA_in : ∀ x, x ∈ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 * s x)
    (hA_out : ∀ x, x ∉ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 ∨
      (G.adjMatrix ℤ).mulVec s x = 0 ∨
      (G.adjMatrix ℤ).mulVec s x = 2) :
    ∃ (label : muThreeExterior c.supp →
          muThreePositiveShore c.supp s × muThreeNegativeShore c.supp s)
      (hinj : Function.Injective label),
      MuThreeMixedGridCode
        (orderSixtyFourMuThreeInternalRel G)
        (orderSixtyFourMuThreeHole label)
        (orderSixtyFourMuThreeExteriorCellGraph G label hinj) := by
  obtain ⟨label, hinj, hadj⟩ :=
    orderSixtyFour_signedSizeTwo_muThree_exterior_gridEmbedding
      G hfree hreg hcardV c hc s hs_in hs_out hsum hDs hA_in hA_out
  exact ⟨label, hinj,
    orderSixtyFour_muThree_mixedGridCode_of_label
      G hfree hreg hcardV c hc s hs_in hs_out hsum hDs hA_in hA_out
        label hinj hadj⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFourMuThreeExteriorCellEquiv
#print axioms Erdos85.orderSixtyFourMuThreeExteriorCellGraph_c4Free
#print axioms Erdos85.orderSixtyFourMuThreeHole_twoRegular
#print axioms Erdos85.orderSixtyFourMuThreeInternalRel_twoRegular
#print axioms Erdos85.orderSixtyFourMuThreeExteriorCellGraph_rook
#print axioms Erdos85.orderSixtyFourMuThree_mixedGridCode_of_hitLaws
#print axioms Erdos85.orderSixtyFourMuThree_label_positive_eq_of_adj
#print axioms Erdos85.orderSixtyFourMuThreeLabelRowFiberEquiv
#print axioms Erdos85.orderSixtyFourMuThreeLabelRowFiber_card_eq_six
#print axioms Erdos85.orderSixtyFourMuThree_exteriorLabelRowHit
#print axioms Erdos85.orderSixtyFourMuThreeExteriorCellGraph_rowHit
#print axioms Erdos85.orderSixtyFour_muThree_mixedGridCode_of_label
