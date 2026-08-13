import Proofs.Erdos85ComponentCompactNormalForm
import Proofs.Erdos85ManufacturedCliquePivot
import Proofs.Erdos85ManufacturedDefectClique
import Proofs.Erdos85ManufacturedSelectorCompatibility

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

/-- **Split-pivot repair contradiction.** These are the exact remaining
construction obligations after the automatic old--old budget has been
discharged.  Any such delete-`k`/add-`k+1` split-pivot repair contradicts
one-step nonextension. -/
theorem false_of_splitPivotRepair_of_no_witness_succ
    {m d k : ℕ}
    (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin m) G)
    (hnext : ¬ C4FreeMinDegreeWitness (m + 1) d)
    (D : Finset (Fin m)) (hDcard : D.card = k)
    {W : Type} [Fintype W] [DecidableEq W]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (hWcard : Fintype.card W = k + 1)
    (pivot : W → Fin m) (hpivot : ∀ w, pivot w ∈ D)
    (A : W → Finset {v : Fin m // v ∉ D})
    (hsub : ∀ w, A w ⊆ survivingNeighborSelector G D (pivot w))
    (hfiber : ∀ u w, u ≠ w → pivot u = pivot w →
      (A u ∩ A w).card ≤ 1)
    (hnewNew : ∀ u w : W, u ≠ w →
      (A u ∩ A w).card +
        (F.neighborFinset u ∩ F.neighborFinset w).card ≤ 1)
    (hmixed : ∀ x : {v : Fin m // v ∉ D}, ∀ w : W,
      ((deleteVertexSetGraph G D).neighborFinset x ∩ A w).card +
        (F.neighborFinset w |>.filter fun u => x ∈ A u).card ≤ 1)
    (hcomp : ∀ v : {v : Fin m // v ∉ D},
      d + (G.neighborFinset v.1 ∩ D).card ≤ G.degree v.1 +
        (Finset.univ.filter fun w => v ∈ A w).card)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w) : False := by
  have hcompat :
      GadgetAttachmentCompatible (deleteVertexSetGraph G D) F A :=
    (pivotSubselectors_compatible_iff
      G D hfree F pivot hpivot A hsub hfiber).2 ⟨hnewNew, hmixed⟩
  apply hnext
  exact c4FreeMinDegreeWitness_succ_of_delete_set_add_gadget
    G D F A (by simp) hDcard hWcard hcompat hcomp hnew

end Erdos85
