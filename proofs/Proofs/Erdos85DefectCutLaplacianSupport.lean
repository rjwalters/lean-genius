import Proofs.Erdos85C4FreeDefectCutIdentity

/-!
# Support of a defect-cut Laplacian vector

For a vertex shore `S`, the graph-Laplacian vector `L_D 1_S` vanishes away
from endpoints of the cut `δ_D(S)`.  Each cut edge contributes at most two
endpoints, so the support has cardinality at most twice the oriented cut size.
This is the upper half of the support sandwich in the maximal-connectivity
argument for `NONBIP-CONNECTED [q]`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Oriented cut size, counted from the shore. -/
def finsetGraphCutSize {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (S : Finset V) : ℕ :=
  ∑ x ∈ S, (D.neighborFinset x \ S).card

/-- Counting a cut from the complement gives the same size. -/
theorem sum_outside_inter_eq_finsetGraphCutSize
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (S : Finset V) :
    (∑ y ∈ Finset.univ \ S, (D.neighborFinset y ∩ S).card) =
      finsetGraphCutSize D S := by
  have h := sum_subset_neighbor_weight_eq_sum_inter_card_mul D S
    (fun y => if y ∈ Finset.univ \ S then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at h
  have hleft :
      (∑ y ∈ Finset.univ \ S, (D.neighborFinset y ∩ S).card) =
        ∑ y : V, if y ∉ S then (D.neighborFinset y ∩ S).card else 0 := by
    have hout : Finset.univ \ S =
        Finset.univ.filter (fun y => y ∉ S) := by ext y; simp
    rw [hout, Finset.sum_filter]
  have hright :
      (∑ x ∈ S, ∑ w ∈ D.neighborFinset x, if w ∉ S then 1 else 0) =
        finsetGraphCutSize D S := by
    rw [finsetGraphCutSize]
    apply Finset.sum_congr rfl
    intro x hx
    have hout : D.neighborFinset x \ S =
        (D.neighborFinset x).filter (fun w => w ∉ S) := by ext w; simp
    rw [hout, Finset.card_filter]
  exact hleft.trans (h.symm.trans hright)

/-- The union of the two shores' active cut endpoints. -/
def finsetGraphCutEndpoints {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (S : Finset V) : Finset V :=
  (S.filter fun x => (D.neighborFinset x \ S).Nonempty) ∪
    ((Finset.univ \ S).filter fun y => (D.neighborFinset y ∩ S).Nonempty)

/-- A cut of size `δ` has at most `2δ` distinct endpoints. -/
theorem card_finsetGraphCutEndpoints_le_two_mul_cutSize
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (S : Finset V) :
    (finsetGraphCutEndpoints D S).card ≤ 2 * finsetGraphCutSize D S := by
  let L := S.filter fun x => (D.neighborFinset x \ S).Nonempty
  let R := (Finset.univ \ S).filter fun y => (D.neighborFinset y ∩ S).Nonempty
  have hL : L.card ≤ finsetGraphCutSize D S := by
    calc
      L.card = ∑ x ∈ S, if (D.neighborFinset x \ S).Nonempty then 1 else 0 := by
        simp [L]
      _ ≤ ∑ x ∈ S, (D.neighborFinset x \ S).card := by
        apply Finset.sum_le_sum
        intro x hx
        split
        · exact Finset.one_le_card.mpr ‹_›
        · exact Nat.zero_le _
      _ = finsetGraphCutSize D S := rfl
  have hR : R.card ≤ finsetGraphCutSize D S := by
    calc
      R.card = ∑ y ∈ Finset.univ \ S,
          if (D.neighborFinset y ∩ S).Nonempty then 1 else 0 := by simp [R]
      _ ≤ ∑ y ∈ Finset.univ \ S, (D.neighborFinset y ∩ S).card := by
        apply Finset.sum_le_sum
        intro y hy
        split
        · exact Finset.one_le_card.mpr ‹_›
        · exact Nat.zero_le _
      _ = finsetGraphCutSize D S := sum_outside_inter_eq_finsetGraphCutSize D S
  calc
    (finsetGraphCutEndpoints D S).card ≤ L.card + R.card := by
      exact Finset.card_union_le L R
    _ ≤ finsetGraphCutSize D S + finsetGraphCutSize D S := Nat.add_le_add hL hR
    _ = 2 * finsetGraphCutSize D S := by omega

/-- Entrywise form of `L_D 1_S`. -/
def finsetGraphLaplacianIndicator {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (S : Finset V) (x : V) : ℤ :=
  (D.degree x : ℤ) * (if x ∈ S then 1 else 0) -
    ((D.neighborFinset x ∩ S).card : ℤ)

/-- The Laplacian indicator is supported only at cut endpoints. -/
theorem support_finsetGraphLaplacianIndicator_subset_cutEndpoints
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (S : Finset V) :
    (Finset.univ.filter fun x => finsetGraphLaplacianIndicator D S x ≠ 0) ⊆
      finsetGraphCutEndpoints D S := by
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  by_cases hxS : x ∈ S
  · have hout : (D.neighborFinset x \ S).Nonempty := by
      by_contra hempty
      have hsub : D.neighborFinset x ⊆ S := by
        intro y hy
        by_contra hyS
        exact hempty ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyS⟩⟩
      have hinter : D.neighborFinset x ∩ S = D.neighborFinset x :=
        Finset.inter_eq_left.mpr hsub
      apply hx
      simp [finsetGraphLaplacianIndicator, hxS, hinter,
        D.card_neighborFinset_eq_degree]
    simp [finsetGraphCutEndpoints, hxS, hout]
  · have hin : (D.neighborFinset x ∩ S).Nonempty := by
      by_contra hempty
      apply hx
      have hz : D.neighborFinset x ∩ S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
      simp [finsetGraphLaplacianIndicator, hxS, hz]
    simp [finsetGraphCutEndpoints, hxS, hin]

/-- The support of `L_D 1_S` has size at most twice the cut. -/
theorem card_support_finsetGraphLaplacianIndicator_le_two_mul_cutSize
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (S : Finset V) :
    (Finset.univ.filter fun x => finsetGraphLaplacianIndicator D S x ≠ 0).card ≤
      2 * finsetGraphCutSize D S :=
  (Finset.card_le_card
    (support_finsetGraphLaplacianIndicator_subset_cutEndpoints D S)).trans
      (card_finsetGraphCutEndpoints_le_two_mul_cutSize D S)

#print axioms sum_outside_inter_eq_finsetGraphCutSize
#print axioms card_finsetGraphCutEndpoints_le_two_mul_cutSize
#print axioms support_finsetGraphLaplacianIndicator_subset_cutEndpoints
#print axioms card_support_finsetGraphLaplacianIndicator_le_two_mul_cutSize

end

end Erdos85
