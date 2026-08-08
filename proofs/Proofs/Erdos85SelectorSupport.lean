import Proofs.Erdos85DefectDegreeBound
import Proofs.Erdos85GadgetExtension

/-!
# The selector support lemma

In any gadget attachment to an induced subgraph of a `C4`-free graph, a
selector containing a vertex whose `G`-neighborhood survives intact is
trapped: all its other members are genuine defect partners of that
vertex in the ambient graph, because a surviving common neighbor would
violate compatibility and a deleted one is unavailable.  With the
regularity-free defect-degree bound this caps the selector at `e + 3` —
far below the degree demand `d - k`, which is the engine of the
plateau-order surgery obstruction.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Selector support.**  If a compatible selector contains a vertex
all of whose ambient neighbors survive in `s`, then every other member
of that selector is an ambient defect partner of it. -/
theorem selector_subset_defectPartners_of_neighbors_mem
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)]
    {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset s)
    (hcompat : GadgetAttachmentCompatible (G.induce s) F A)
    (w : W) (a : s) (ha : a ∈ A w)
    (hN : ∀ z, G.Adj a.1 z → z ∈ s) :
    ∀ ⦃b : s⦄, b ∈ A w → b ≠ a → b.1 ∈ defectPartners G a.1 := by
  intro b hb hba
  rw [mem_defectPartners]
  refine ⟨fun h ↦ hba (Subtype.ext h), ?_⟩
  have hcount := GadgetAttachmentCompatible.selector_safe
    (G.induce s) F A hcompat w hb ha hba
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hcount
  rw [Finset.eq_empty_iff_forall_notMem]
  intro z hz
  rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset] at hz
  have hzs : z ∈ s := hN z hz.2
  apply hcount (⟨z, hzs⟩ : s)
  rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
  exact ⟨hz.1, hz.2⟩

/-- **Selector cap.**  At plateau order, a compatible selector through a
vertex with intact surviving neighborhood has at most `e + 3`
members. -/
theorem selector_card_le_of_neighbors_mem
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V ≤ d * (d - 1) + 3 + e)
    (s : Set V) [DecidablePred (· ∈ s)]
    {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset s)
    (hcompat : GadgetAttachmentCompatible (G.induce s) F A)
    (w : W) (a : s) (ha : a ∈ A w)
    (hN : ∀ z, G.Adj a.1 z → z ∈ s) :
    (A w).card ≤ e + 3 := by
  classical
  have hsub := selector_subset_defectPartners_of_neighbors_mem
    G s F A hcompat w a ha hN
  have hinj : ((A w).erase a).card ≤ (defectPartners G a.1).card := by
    apply Finset.card_le_card_of_injOn (fun b ↦ b.1)
    · intro b hb
      exact hsub (Finset.mem_of_mem_erase hb)
        (Finset.ne_of_mem_erase hb)
    · intro x _ y _ hxy
      exact Subtype.ext hxy
  have hbound := defectPartners_card_le_of_plateau_order
    G hfree hmin hcard a.1
  have herase : ((A w).erase a).card + 1 = (A w).card :=
    Finset.card_erase_add_one ha
  omega

end

end Erdos85
