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

end

end Erdos85

#print axioms Erdos85.orderSixtyFourMuThreeExteriorCellEquiv
#print axioms Erdos85.orderSixtyFourMuThreeExteriorCellGraph_c4Free
