import Proofs.Erdos85GadgetCounting
import Proofs.Erdos85Problem

/-! # Off-diagonal common-neighbor support in regular C4-free graphs -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Vertices other than `a` sharing at least one graph neighbor with `a`. -/
def offDiagonalCommonNeighborSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) : Finset V :=
  (Finset.univ.erase a).filter fun b ↦
    (G.neighborFinset b ∩ G.neighborFinset a).Nonempty

/-- In a `d`-regular C4-free graph, exactly `d(d-1)` other vertices share
a neighbor with a fixed vertex.  C4-freeness turns the ordinary two-walk
mass identity into an exact support census. -/
theorem offDiagonalCommonNeighborSupport_card_of_regular_not_containsC4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (d : ℕ)
    (hreg : ∀ x, G.degree x = d) (a : V) :
    (offDiagonalCommonNeighborSupport G a).card = d * (d - 1) := by
  classical
  let f := fun b : V ↦
    (G.neighborFinset b ∩ G.neighborFinset a).card
  have htotal : (∑ b : V, f b) = d * d := by
    have h := sum_card_neighbor_inter_eq_sum_degree G (G.neighborFinset a)
    rw [h]
    simp_rw [hreg]
    simp [G.card_neighborFinset_eq_degree, hreg]
  have hdiag : f a = d := by
    simp [f, G.card_neighborFinset_eq_degree, hreg]
  have hoff : (∑ b ∈ Finset.univ.erase a, f b) =
      (offDiagonalCommonNeighborSupport G a).card := by
    rw [offDiagonalCommonNeighborSupport, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro b hb
    have hba : b ≠ a := (Finset.mem_erase.mp hb).1
    have hle : f b ≤ 1 := by
      exact common_le_one_of_not_containsC4 hfree b a hba
    by_cases hn : (G.neighborFinset b ∩ G.neighborFinset a).Nonempty
    · have hpos : 0 < f b := by
        simpa [f, Finset.card_pos] using hn
      simp [hn]
      omega
    · have hz : f b = 0 := by
        simpa [f, Finset.not_nonempty_iff_eq_empty,
          Finset.card_eq_zero] using hn
      simp [hn, hz]
  have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset V))
    (f := f) (Finset.mem_univ a)
  rw [hoff, hdiag, htotal] at hsplit
  cases d with
  | zero => simpa using hsplit
  | succ n =>
      simp only [Nat.succ_sub_one]
      nlinarith

/-- Weighted refinement: the full common-neighbor mass is the diagonal
contribution `d·w(a)` plus one copy of the weight on each off-diagonal
support vertex. -/
theorem sum_commonNeighbor_card_mul_weight_eq_diag_add_support
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (d : ℕ)
    (hreg : ∀ x, G.degree x = d) (a : V) (w : V → ℕ) :
    (∑ b : V,
      (G.neighborFinset b ∩ G.neighborFinset a).card * w b) =
      d * w a + ∑ b ∈ offDiagonalCommonNeighborSupport G a, w b := by
  classical
  let c := fun b : V ↦
    (G.neighborFinset b ∩ G.neighborFinset a).card
  have hdiag : c a = d := by
    simp [c, G.card_neighborFinset_eq_degree, hreg]
  have hoff : (∑ b ∈ Finset.univ.erase a, c b * w b) =
      ∑ b ∈ offDiagonalCommonNeighborSupport G a, w b := by
    rw [offDiagonalCommonNeighborSupport, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b hb
    have hba : b ≠ a := (Finset.mem_erase.mp hb).1
    have hle : c b ≤ 1 :=
      common_le_one_of_not_containsC4 hfree b a hba
    by_cases hn : (G.neighborFinset b ∩ G.neighborFinset a).Nonempty
    · have hpos : 0 < c b := by
        simpa [c, Finset.card_pos] using hn
      have hc : c b = 1 := by omega
      simp [hn, hc]
    · have hz : c b = 0 := by
        simpa [c, Finset.not_nonempty_iff_eq_empty,
          Finset.card_eq_zero] using hn
      simp [hn, hz]
  have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset V))
    (f := fun b ↦ c b * w b) (Finset.mem_univ a)
  rw [hoff, hdiag] at hsplit
  simpa [c, add_comm] using hsplit.symm

end

end Erdos85

#print axioms
  Erdos85.offDiagonalCommonNeighborSupport_card_of_regular_not_containsC4
#print axioms
  Erdos85.sum_commonNeighbor_card_mul_weight_eq_diag_add_support
