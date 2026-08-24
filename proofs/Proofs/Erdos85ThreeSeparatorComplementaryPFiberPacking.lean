import Proofs.Erdos85C4FreeCommonNeighborUnique
import Proofs.Erdos85ThreeSeparatorPResidualBudget

/-!
# Packing in a complementary P-fiber

The exceptional points in the complementary Y-fiber are common A-neighbors
of the distinct centers `p_w` and `c`.  C4-freeness allows at most one such
point.  Removing it from the `(b-1)`-point fiber leaves at least `b-2`
ordinary points, the packing statement (B44) that drives the B45 injection.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- C4-free common-neighbor packing core of B44. -/
theorem commonNeighbor_subfiber_card_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (p c : V) (H : Finset V)
    (hpc : p ≠ c)
    (hH : H ⊆ A.neighborFinset p ∩ A.neighborFinset c) :
    H.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro y hy y' hy'
  have hyCommon := Finset.mem_inter.mp (hH hy)
  have hy'Common := Finset.mem_inter.mp (hH hy')
  exact commonNeighbor_unique_of_c4Free hfree hpc
    ((A.mem_neighborFinset p y).mp hyCommon.1)
    ((A.mem_neighborFinset c y).mp hyCommon.2)
    ((A.mem_neighborFinset p y').mp hy'Common.1)
    ((A.mem_neighborFinset c y').mp hy'Common.2)

/-- Removing an at-most-one exceptional subset from a `(b-1)`-point fiber
leaves at least `b-2` points. -/
theorem complementary_Pfiber_ordinary_card_ge_b_sub_two
    {V : Type*} [DecidableEq V]
    (G H : Finset V) (b : ℕ)
    (hHG : H ⊆ G)
    (hGcard : G.card = b - 1)
    (hHcard : H.card ≤ 1) :
    b - 2 ≤ (G \ H).card := by
  rw [Finset.card_sdiff_of_subset hHG, hGcard]
  omega

/-- Combined B44 consumer. -/
theorem c4Free_complementary_Pfiber_packing
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (p c : V) (G H : Finset V) (b : ℕ)
    (hpc : p ≠ c)
    (hHG : H ⊆ G)
    (hHcommon : H ⊆ A.neighborFinset p ∩ A.neighborFinset c)
    (hGcard : G.card = b - 1) :
    H.card ≤ 1 ∧ b - 2 ≤ (G \ H).card := by
  have hle := commonNeighbor_subfiber_card_le_one A hfree p c H hpc hHcommon
  exact ⟨hle, complementary_Pfiber_ordinary_card_ge_b_sub_two
    G H b hHG hGcard hle⟩

end


end Erdos85

#print axioms Erdos85.commonNeighbor_subfiber_card_le_one
#print axioms Erdos85.complementary_Pfiber_ordinary_card_ge_b_sub_two
#print axioms Erdos85.c4Free_complementary_Pfiber_packing
