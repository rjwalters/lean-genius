import Proofs.Erdos85BinarySquareMuThreeExteriorRowHit
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

end

end Erdos85

#print axioms Erdos85.orderSixtyFourMuThreeExteriorCellEquiv
#print axioms Erdos85.orderSixtyFourMuThreeExteriorCellGraph_c4Free
#print axioms Erdos85.orderSixtyFourMuThreeHole_twoRegular
#print axioms Erdos85.orderSixtyFourMuThreeInternalRel_twoRegular
#print axioms Erdos85.orderSixtyFourMuThreeExteriorCellGraph_rook
