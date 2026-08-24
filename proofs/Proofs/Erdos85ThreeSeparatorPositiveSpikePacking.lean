import Proofs.Erdos85C4FreeCommonNeighborUnique
import Proofs.Erdos85ThreeSeparatorDualProfileClassification

/-!
# Positive-spike three-separator packing

This formalizes the C4-free packing step behind equation (B9).  Vertices in
one shore are all adjacent to the exceptional point and each use two points
of the spike set.  Those two-point fibers are pairwise disjoint, since a
shared point would give two common neighbors together with the exceptional
point.
-/

open Finset SimpleGraph

namespace Erdos85

/-- C4-free two-incidence packing: fibers inside `R` belonging to distinct
neighbors of `c` cannot overlap. -/
theorem two_mul_card_le_of_c4Free_common_center_two_incidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (c : V) (X R : Finset V)
    (hX : X ⊆ G.neighborFinset c) (hcR : c ∉ R)
    (htwo : ∀ x ∈ X, (G.neighborFinset x ∩ R).card = 2) :
    2 * X.card ≤ R.card := by
  let F : V → Finset V := fun x => G.neighborFinset x ∩ R
  have hdisj : (X : Set V).PairwiseDisjoint F := by
    intro x hx y hy hxy
    apply Finset.disjoint_left.mpr
    intro r hrx hry
    have hxc : G.Adj x c := by
      exact ((G.mem_neighborFinset c x).mp (hX hx)).symm
    have hyc : G.Adj y c := by
      exact ((G.mem_neighborFinset c y).mp (hX hy)).symm
    have hxr : G.Adj x r :=
      (G.mem_neighborFinset x r).mp (Finset.mem_inter.mp hrx).1
    have hyr : G.Adj y r :=
      (G.mem_neighborFinset y r).mp (Finset.mem_inter.mp hry).1
    have hcr : c ≠ r := by
      intro h
      subst r
      exact hcR (Finset.mem_inter.mp hrx).2
    have := commonNeighbor_unique_of_c4Free hfree hxy hxc hyc hxr hyr
    exact hcr this
  have hUnionSub : X.biUnion F ⊆ R := by
    intro r hr
    simp only [Finset.mem_biUnion, F] at hr
    obtain ⟨x, -, hr⟩ := hr
    exact (Finset.mem_inter.mp hr).2
  have hFtwo : ∀ x ∈ X, (F x).card = 2 := by
    simpa [F] using htwo
  calc
    2 * X.card = ∑ x ∈ X, (F x).card := by
      symm
      calc
        ∑ x ∈ X, (F x).card = ∑ _x ∈ X, 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hFtwo x hx
        _ = 2 * X.card := by simp [Nat.mul_comm]
    _ = (X.biUnion F).card := (Finset.card_biUnion hdisj).symm
    _ ≤ R.card := Finset.card_le_card hUnionSub

/-- Numerical B9 endpoint: the packing inequality `2a ≤ q+1` implies the
integer half bound when `q` is even. -/
theorem le_half_of_even_of_two_mul_le_succ
    {a q : ℕ} (hq : Even q) (h : 2 * a ≤ q + 1) :
    a ≤ q / 2 := by
  obtain ⟨k, rfl⟩ := hq
  omega

#print axioms two_mul_card_le_of_c4Free_common_center_two_incidence
#print axioms le_half_of_even_of_two_mul_le_succ

end Erdos85
