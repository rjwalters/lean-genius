import Proofs.Erdos85ThreeSeparatorComplementaryPFiberInjection

/-!
# Exact opposite-shore fiber partitions

Let `Z ⊆ N_A(c)` be centers routing a shore `X`.  If every point of X is
adjacent to some center in Z and `c ∉ X`, then the fibers
`F_z=N_A(z)∩X` cover X.  They are pairwise disjoint: an overlap point,
together with c, would be two common neighbors of two distinct centers.
This is the common structural core of the normal forms (B47Y) and (B47X).
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- C4-free opposite-shore fibers form an exact partition. -/
theorem c4Free_oppositeShore_fibers_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (c : V) (X Z : Finset V)
    (hcX : c ∉ X)
    (hZc : Z ⊆ A.neighborFinset c)
    (hcover : ∀ x ∈ X, ∃ z ∈ Z, A.Adj z x) :
    ((Z : Set V).PairwiseDisjoint (fun z ↦ A.neighborFinset z ∩ X)) ∧
      Z.biUnion (fun z ↦ A.neighborFinset z ∩ X) = X := by
  have hdisj : (Z : Set V).PairwiseDisjoint
      (fun z ↦ A.neighborFinset z ∩ X) := by
    intro z hz z' hz' hzz'
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    have hzc : A.Adj z c :=
      ((A.mem_neighborFinset c z).mp (hZc hz)).symm
    have hz'c : A.Adj z' c :=
      ((A.mem_neighborFinset c z').mp (hZc hz')).symm
    have hzx : A.Adj z x :=
      (A.mem_neighborFinset z x).mp (Finset.mem_inter.mp hx).1
    have hz'x : A.Adj z' x :=
      (A.mem_neighborFinset z' x).mp (Finset.mem_inter.mp hx').1
    have hcx := commonNeighbor_unique_of_c4Free
      hfree hzz' hzc hz'c hzx hz'x
    subst x
    exact hcX (Finset.mem_inter.mp hx).2
  refine ⟨hdisj, ?_⟩
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [Finset.mem_biUnion] at hx
    obtain ⟨z, -, hx⟩ := hx
    exact (Finset.mem_inter.mp hx).2
  · intro x hx
    obtain ⟨z, hzZ, hzx⟩ := hcover x hx
    apply Finset.mem_biUnion.mpr
    exact ⟨z, hzZ, Finset.mem_inter.mpr
      ⟨(A.mem_neighborFinset z x).mpr hzx, hx⟩⟩

/-- Cardinal form of the B47 partition. -/
theorem c4Free_oppositeShore_sum_fiber_cards
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (c : V) (X Z : Finset V)
    (hcX : c ∉ X)
    (hZc : Z ⊆ A.neighborFinset c)
    (hcover : ∀ x ∈ X, ∃ z ∈ Z, A.Adj z x) :
    ∑ z ∈ Z, (A.neighborFinset z ∩ X).card = X.card := by
  have hpart := c4Free_oppositeShore_fibers_partition
    A hfree c X Z hcX hZc hcover
  calc
    ∑ z ∈ Z, (A.neighborFinset z ∩ X).card =
        (Z.biUnion (fun z ↦ A.neighborFinset z ∩ X)).card :=
      (Finset.card_biUnion hpart.1).symm
    _ = X.card := congrArg Finset.card hpart.2

end


end Erdos85

#print axioms Erdos85.c4Free_oppositeShore_fibers_partition
#print axioms Erdos85.c4Free_oppositeShore_sum_fiber_cards
