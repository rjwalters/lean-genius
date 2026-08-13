import Proofs.Erdos85ComponentCompactNormalForm
import Proofs.Erdos85ManufacturedCliquePivot
import Proofs.Erdos85ManufacturedDefectClique

/-!
# A manufactured-clique surgery bound for minimal plateau cores

The connected compact normal form supplies arbitrarily sized tight deletion
sets below half the order.  If a delete-`k`/add-`k+1` repair uses subsets of
the surviving neighborhoods of deleted pivots, the selector support is
automatic.  The manufactured-clique pivot inequality then gives the sharp
numerical obstruction `d ≤ choose(k+1,2) + 2|E(F)|`.
-/

namespace Erdos85

open SimpleGraph

/-- **Plateau surgery pivot.** Every order-minimal plateau core has a
connected representative on which tight deletion sets of every admissible
size enforce the manufactured-clique numerical obstruction for all
compatible gadgets. -/
theorem OrderMinimalC4PlateauCore.exists_connected_surgeryPivot
    {m d : ℕ} (hm : 4 ≤ m) (hd : 4 ≤ d)
    (hminimal : OrderMinimalC4PlateauCore m d) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
      G.minDegree = d ∧
      ¬ containsC4 (Fin m) G ∧
      Fintype.card G.ConnectedComponent = 1 ∧
      ∀ k, 2 * k < m →
        ∃ D : Finset (Fin m), D.card = k ∧
          (∀ x ∈ D, G.degree x = d) ∧
          ∀ (W : Type) [Fintype W] [DecidableEq W]
            (F : SimpleGraph W) [DecidableRel F.Adj]
            (A : W → Finset {v : Fin m // v ∉ D})
            (pivot : W → Fin m),
            Fintype.card W = k + 1 →
            (∀ w, pivot w ∈ D) →
            (∀ w, A w ⊆ survivingNeighborSelector G D (pivot w)) →
            GadgetAttachmentCompatible (deleteVertexSetGraph G D) F A →
            (∀ w, d ≤ (A w).card + F.degree w) →
            d ≤ (k + 1).choose 2 + 2 * F.edgeFinset.card := by
  obtain ⟨G, hdec, hmin, hfree, _hcover, _hnext, hconnected,
    _horder, _hupper, _hoddUpper, _hind, _hconflict, _hthreshold,
    _hexcess, hreservoir⟩ :=
      hminimal.exists_connected_compact_normalForm hm hd
  letI : DecidableRel G.Adj := hdec
  refine ⟨G, hdec, hmin, hfree, hconnected, ?_⟩
  intro k hk
  obtain ⟨D, hDcard, hDtight⟩ := hreservoir k hk
  refine ⟨D, hDcard, hDtight, ?_⟩
  intro W _ _ F _ A pivot hWcard hpivot hA hcompat hnew
  apply degree_le_choose_add_twice_gadgetEdges_of_deleted_support
    G D F A hDcard hWcard hDtight hcompat hnew
  exact selectorFamily_deleted_support_of_subset_survivingNeighborSelector
    G D pivot hpivot A hA

end Erdos85
