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

end

end Erdos85

#print axioms Erdos85.orderSixtyFourMuThreeExteriorCellEquiv
#print axioms Erdos85.orderSixtyFourMuThreeExteriorCellGraph_c4Free
#print axioms Erdos85.orderSixtyFourMuThreeHole_twoRegular
