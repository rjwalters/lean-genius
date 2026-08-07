import Proofs.Erdos85GadgetMultiplicity

/-!
# Bonferroni aggregation for gadget selectors

Compatibility bounds every pair of distinct selectors to meet in at most
one old vertex.  This file packages the resulting first Bonferroni bound in
the form needed by plateau surgery: total selector incidence is at most the
size of the selector union plus one unit for every pair of gadget vertices.
-/

namespace Erdos85

open SimpleGraph

/-- Total compatible-selector incidence is bounded by the size of the union
plus `choose(|W|,2)`.  This is the selector-family Bonferroni inequality;
unlike the cruder ambient-cardinality bound, it can be combined with a
support estimate for the actual union. -/
theorem GadgetAttachmentCompatible.sum_card_selector_le_union_add_choose
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) (hcompat : GadgetAttachmentCompatible G F A) :
    (∑ w : W, (A w).card) ≤
      (Finset.univ.biUnion A).card + (Fintype.card W).choose 2 := by
  classical
  let U : Finset V := Finset.univ.biUnion A
  have hdouble : (∑ w : W, (A w).card) =
      ∑ x : V, attachmentMultiplicity A x := by
    calc
      (∑ w : W, (A w).card) =
          ∑ w : W, ∑ _x ∈ A w, 1 := by simp
      _ = ∑ x : V, 1 * attachmentMultiplicity A x :=
        sum_sum_weight_eq_sum_weight_mul_attachmentMultiplicity A
          (fun _ ↦ 1)
      _ = ∑ x : V, attachmentMultiplicity A x := by simp
  have hout : ∀ x ∉ U, attachmentMultiplicity A x = 0 := by
    intro x hx
    rw [attachmentMultiplicity, attachmentIndices, Finset.card_eq_zero,
      Finset.eq_empty_iff_forall_notMem]
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    apply hx
    change x ∈ Finset.univ.biUnion A
    rw [Finset.mem_biUnion]
    exact ⟨w, Finset.mem_univ w, hw⟩
  have hrestrict : (∑ x : V, attachmentMultiplicity A x) =
      ∑ x ∈ U, attachmentMultiplicity A x := by
    symm
    apply Finset.sum_subset (Finset.subset_univ U)
    intro x _ hx
    exact hout x hx
  rw [hdouble, hrestrict]
  exact hcompat.sum_attachmentMultiplicity_le_card_add_choose G F A U

/-- Ambient-cardinality corollary.  In a compatible attachment on `V`, the
sum of all selector sizes is at most `|V| + choose(|W|,2)`. -/
theorem GadgetAttachmentCompatible.sum_card_selector_le_card_add_choose
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) (hcompat : GadgetAttachmentCompatible G F A) :
    (∑ w : W, (A w).card) ≤
      Fintype.card V + (Fintype.card W).choose 2 := by
  refine (hcompat.sum_card_selector_le_union_add_choose G F A).trans ?_
  apply Nat.add_le_add_right
  rw [← Finset.card_univ]
  exact Finset.card_le_card (Finset.subset_univ _)

end Erdos85
