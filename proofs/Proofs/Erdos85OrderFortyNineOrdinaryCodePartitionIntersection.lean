import Proofs.Erdos85OrderFortyNineOrdinaryAdjacencyMoments

/-!
# Intersections of ordinary open-code partitions

Each high neighborhood is an efficient open dominating code in the ordinary
graph: every ordinary vertex has exactly one neighbor in the code.  This file
packages the resulting neighborhood partitions and their C4-free intersection
bound.  It is the abstract interface behind the seven-by-seven holonomy grid.
-/

open SimpleGraph

namespace Erdos85

/-- Every vertex has a unique adjacent owner in `A`. -/
def IsOpenCode {V : Type*} (H : SimpleGraph V) (A : Set V) : Prop :=
  ∀ z, ∃! a, a ∈ A ∧ H.Adj z a

theorem IsOpenCode.exists_unique_cell
    {V : Type*} {H : SimpleGraph V} {A : Set V}
    (hA : IsOpenCode H A) (z : V) :
    ∃! a, a ∈ A ∧ z ∈ H.neighborSet a := by
  simpa [SimpleGraph.mem_neighborSet, H.adj_comm] using hA z

/-- Distinct owners in one open code have disjoint open neighborhoods. -/
theorem IsOpenCode.disjoint_neighborSet
    {V : Type*} {H : SimpleGraph V} {A : Set V}
    (hA : IsOpenCode H A) {a a' : V}
    (ha : a ∈ A) (ha' : a' ∈ A) (hne : a ≠ a') :
    Disjoint (H.neighborSet a) (H.neighborSet a') := by
  rw [Set.disjoint_left]
  intro z hza hza'
  obtain ⟨owner, howner, hunique⟩ := hA z
  have hea : a = owner := hunique a ⟨ha, (H.adj_comm a z).mp hza⟩
  have hea' : a' = owner := hunique a' ⟨ha', (H.adj_comm a' z).mp hza'⟩
  exact hne (hea.trans hea'.symm)

/-- The open neighborhoods of the owners cover every vertex. -/
theorem IsOpenCode.mem_some_neighborSet
    {V : Type*} {H : SimpleGraph V} {A : Set V}
    (hA : IsOpenCode H A) (z : V) :
    ∃ a ∈ A, z ∈ H.neighborSet a := by
  obtain ⟨a, ha, _⟩ := hA.exists_unique_cell z
  exact ⟨a, ha.1, ha.2⟩

/-- If two open codes share an owner `r`, every vertex in `r`'s cell has
owner `r` in both partitions. -/
theorem IsOpenCode.shared_owner_of_mem_neighborSet
    {V : Type*} {H : SimpleGraph V} {A B : Set V}
    (hA : IsOpenCode H A) (hB : IsOpenCode H B)
    {r z : V} (hrA : r ∈ A) (hrB : r ∈ B)
    (hzr : z ∈ H.neighborSet r) :
    (∀ a, a ∈ A ∧ z ∈ H.neighborSet a → a = r) ∧
    (∀ b, b ∈ B ∧ z ∈ H.neighborSet b → b = r) := by
  constructor
  · intro a ha
    obtain ⟨owner, howner, hunique⟩ := hA.exists_unique_cell z
    have hr : r = owner := hunique r ⟨hrA, hzr⟩
    have haowner : a = owner := hunique a ha
    exact haowner.trans hr.symm
  · intro b hb
    obtain ⟨owner, howner, hunique⟩ := hB.exists_unique_cell z
    have hr : r = owner := hunique r ⟨hrB, hzr⟩
    have hbowner : b = owner := hunique b hb
    exact hbowner.trans hr.symm

/-- Consequently the central cell has empty off-block intersections in both
directions of the two partition-intersection grid. -/
theorem IsOpenCode.shared_owner_offblock_disjoint
    {V : Type*} {H : SimpleGraph V} {A B : Set V}
    (hA : IsOpenCode H A) (hB : IsOpenCode H B)
    {r a b : V} (hrA : r ∈ A) (hrB : r ∈ B)
    (ha : a ∈ A) (hb : b ∈ B) (har : a ≠ r) (hbr : b ≠ r) :
    Disjoint (H.neighborSet r) (H.neighborSet b) ∧
      Disjoint (H.neighborSet a) (H.neighborSet r) := by
  constructor
  · exact hB.disjoint_neighborSet hrB hb (Ne.symm hbr)
  · exact hA.disjoint_neighborSet ha hrA har

/-- Away from the shared central cell, every entry of the intersection grid
has size at most one in a C4-free graph. -/
theorem openCode_neighborFinset_inter_card_le_one_of_not_containsC4
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hfree : ¬ containsC4 V H) {a b : V} (hab : a ≠ b) :
    (H.neighborFinset a ∩ H.neighborFinset b).card ≤ 1 :=
  common_le_one_of_not_containsC4 hfree a b hab

end Erdos85

#print axioms Erdos85.IsOpenCode.disjoint_neighborSet
#print axioms Erdos85.IsOpenCode.shared_owner_offblock_disjoint
#print axioms Erdos85.openCode_neighborFinset_inter_card_le_one_of_not_containsC4
