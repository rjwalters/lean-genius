import Proofs.Erdos85BoundedReplacementObstruction
import Proofs.Erdos85SelectorBonferroni

/-!
# The manufactured-clique counting pivot

The sharp counting step behind a delete-`k`/add-`k+1` repair is independent
of the particular surgery used to manufacture it.  If every old vertex used
by a selector lost at least one neighbour to the deleted set, then the union
of all selectors has size at most the cut incidence, hence at most `k*d` when
the deleted vertices have degree `d`.  Bonferroni and the handshake identity
then leave only one uncancelled copy of `d`.

The support hypothesis is essential: compatibility alone does not force it.
This file isolates the exact geometric input still required from a pivot or
manufactured-clique construction.
-/

open SimpleGraph

namespace Erdos85

/-- A family supported on vertices damaged by deleting `D` has union size at
most the total deleted-neighbour loss. -/
theorem card_selectorUnion_le_sum_deletedNeighborLoss_of_support
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (A : W → Finset {v : V // v ∉ D})
    (hsupport : ∀ ⦃v⦄, v ∈ Finset.univ.biUnion A →
      1 ≤ (G.neighborFinset v.1 ∩ D).card) :
    (Finset.univ.biUnion A).card ≤
      ∑ v : {v : V // v ∉ D}, (G.neighborFinset v.1 ∩ D).card := by
  classical
  calc
    (Finset.univ.biUnion A).card =
        ∑ v ∈ Finset.univ.biUnion A, 1 := by simp
    _ ≤ ∑ v ∈ Finset.univ.biUnion A,
        (G.neighborFinset v.1 ∩ D).card :=
      Finset.sum_le_sum fun v hv ↦ hsupport hv
    _ ≤ ∑ v : {v : V // v ∉ D},
        (G.neighborFinset v.1 ∩ D).card := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ ↦ Nat.zero_le _)

/-- **Manufactured-clique pivot inequality.**  In a compatible
delete-`k`/add-`k+1` attachment, if every selected survivor is incident to
the deleted set and each deleted vertex has degree `d`, then

`d ≤ choose(k+1,2) + 2 * |E(F)|`.

Consequently any independent extremal bound on the `C₄`-free gadget `F`
immediately gives `d ≤ choose(k+1,2) + 2 ex(k+1,C₄)`. -/
theorem degree_le_choose_add_twice_gadgetEdges_of_deleted_support
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D}) {d k : ℕ}
    (hDcard : D.card = k) (hWcard : Fintype.card W = k + 1)
    (hDtight : ∀ x ∈ D, G.degree x = d)
    (hcompat : GadgetAttachmentCompatible (deleteVertexSetGraph G D) F A)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hsupport : ∀ ⦃v⦄, v ∈ Finset.univ.biUnion A →
      1 ≤ (G.neighborFinset v.1 ∩ D).card) :
    d ≤ (k + 1).choose 2 + 2 * F.edgeFinset.card := by
  have hdegree : Fintype.card W * d ≤
      (∑ w : W, (A w).card) + ∑ w : W, F.degree w := by
    calc
      Fintype.card W * d = ∑ _w : W, d := by simp
      _ ≤ ∑ w : W, ((A w).card + F.degree w) :=
        Finset.sum_le_sum fun w _ ↦ hnew w
      _ = (∑ w : W, (A w).card) + ∑ w : W, F.degree w := by
        rw [Finset.sum_add_distrib]
  have hunion : (Finset.univ.biUnion A).card ≤ k * d :=
    (card_selectorUnion_le_sum_deletedNeighborLoss_of_support G D A hsupport).trans
      (sum_deletedNeighborLoss_le_card_mul_degree_of_tight_set
        G D hDcard hDtight)
  have hselectors : (∑ w : W, (A w).card) ≤
      k * d + (k + 1).choose 2 := by
    calc
      (∑ w : W, (A w).card) ≤
          (Finset.univ.biUnion A).card + (Fintype.card W).choose 2 :=
        hcompat.sum_card_selector_le_union_add_choose
          (deleteVertexSetGraph G D) F A
      _ ≤ k * d + (k + 1).choose 2 := by
        rw [hWcard]
        exact Nat.add_le_add_right hunion _
  have hhandshake : ∑ w : W, F.degree w = 2 * F.edgeFinset.card :=
    F.sum_degrees_eq_twice_card_edges
  rw [hWcard, hhandshake] at hdegree
  simp only [Nat.add_mul, one_mul] at hdegree
  omega

/-- Extremal-edge-bound form of the pivot inequality. -/
theorem degree_le_choose_add_twice_edgeBound_of_deleted_support
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D}) {d k q : ℕ}
    (hDcard : D.card = k) (hWcard : Fintype.card W = k + 1)
    (hDtight : ∀ x ∈ D, G.degree x = d)
    (hcompat : GadgetAttachmentCompatible (deleteVertexSetGraph G D) F A)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hsupport : ∀ ⦃v⦄, v ∈ Finset.univ.biUnion A →
      1 ≤ (G.neighborFinset v.1 ∩ D).card)
    (hedges : F.edgeFinset.card ≤ q) :
    d ≤ (k + 1).choose 2 + 2 * q := by
  exact (degree_le_choose_add_twice_gadgetEdges_of_deleted_support
    G D F A hDcard hWcard hDtight hcompat hnew hsupport).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hedges) _)

end Erdos85
