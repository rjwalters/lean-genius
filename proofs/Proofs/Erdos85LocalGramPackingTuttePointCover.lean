import Proofs.Erdos85LocalGramPackingPointCoverFinset
import Mathlib.Combinatorics.SimpleGraph.Tutte

/-!
# Tutte matching bridge for B.3 block collisions

This file turns a perfect matching of the block-intersection graph into the
pair groups consumed by the grouped point-cover contradiction.
-/

namespace Erdos85

variable {V P : Type*}

/-- Rows are adjacent exactly when they are distinct and their point blocks
intersect. -/
def blockCollisionGraph [DecidableEq P] (B : V → Finset P) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ¬ Disjoint (B x) (B y)
  symm.symm x y h := ⟨h.1.symm, by simpa [disjoint_comm] using h.2⟩
  loopless.irrefl x h := h.1 rfl

@[simp] theorem blockCollisionGraph_adj [DecidableEq P] (B : V → Finset P)
    (x y : V) :
    (blockCollisionGraph B).Adj x y ↔
      x ≠ y ∧ ¬ Disjoint (B x) (B y) := Iff.rfl

/-- The edges of a perfect collision matching, viewed as two-row finsets,
cover every row and each have a common block point. -/
theorem exists_pairGroups_of_collisionGraph_perfectMatching
    [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
    (B : V → Finset P)
    (M : (blockCollisionGraph B).Subgraph)
    [Fintype M.spanningCoe.edgeSet]
    (hM : M.IsPerfectMatching) :
    ∃ groups : Finset (Finset V),
      groups.card ≤ M.spanningCoe.edgeFinset.card ∧
      (∀ S ∈ groups, ∃ p, ∀ x ∈ S, p ∈ B x) ∧
      ∀ x, ∃ S ∈ groups, x ∈ S := by
  classical
  let groups : Finset (Finset V) :=
    M.spanningCoe.edgeFinset.image Sym2.toFinset
  refine ⟨groups, Finset.card_image_le, ?_, ?_⟩
  · intro S hS
    rcases Finset.mem_image.mp hS with ⟨e, he, rfl⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hMxy : M.Adj x y := by simpa using he
        have hGxy : (blockCollisionGraph B).Adj x y := M.adj_sub hMxy
        rcases Finset.not_disjoint_iff.mp hGxy.2 with ⟨p, hpx, hpy⟩
        refine ⟨p, ?_⟩
        intro z hz
        rw [Sym2.toFinset_mk_eq] at hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hpx
        · exact hpy
  · intro x
    obtain ⟨y, hMxy, _⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM) x
    refine ⟨s(x, y).toFinset, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨s(x, y), by simpa using hMxy, rfl⟩
    · simp

#print axioms exists_pairGroups_of_collisionGraph_perfectMatching

/-- A perfect matching has exactly half as many edges as vertices.  This is the
cardinality identity needed to turn the matching groups into the numerical
budget used by the local Gram-packing contradiction. -/
theorem twice_card_edges_eq_card_of_isPerfectMatching
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    (M : G.Subgraph)
    (hM : M.IsPerfectMatching) :
    2 * M.spanningCoe.edgeSet.ncard = Fintype.card V := by
  classical
  letI : Fintype M.spanningCoe.edgeSet := M.spanningCoe.fintypeEdgeSet
  have hedgeCard : M.spanningCoe.edgeFinset.card =
      M.spanningCoe.edgeSet.ncard := by
    rw [M.spanningCoe.edgeFinset_card]
    exact Set.fintypeCard_eq_ncard _
  calc
    2 * M.spanningCoe.edgeSet.ncard =
        2 * M.spanningCoe.edgeFinset.card := by
      rw [hedgeCard]
    _ = ∑ v, M.spanningCoe.degree v :=
      M.spanningCoe.sum_degrees_eq_twice_card_edges.symm
    _ = ∑ v, M.degree v := by
      apply Finset.sum_congr rfl
      intro v _
      exact M.degree_spanningCoe v
    _ = ∑ _v : V, 1 := by
      apply Finset.sum_congr rfl
      intro v _
      exact (SimpleGraph.Subgraph.isPerfectMatching_iff_forall_degree.mp hM v)
    _ = Fintype.card V := by simp

/-- Tutte's condition on the collision graph directly supplies pair groups
covering every row, with twice the group count bounded by the number of rows. -/
theorem exists_pairGroups_of_collisionGraph_of_noTutteViolator
    [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
    (B : V → Finset P)
    (hTutte : ∀ u : Set V, ¬(blockCollisionGraph B).IsTutteViolator u) :
    ∃ groups : Finset (Finset V),
      2 * groups.card ≤ Fintype.card V ∧
      (∀ S ∈ groups, ∃ p, ∀ x ∈ S, p ∈ B x) ∧
      ∀ x, ∃ S ∈ groups, x ∈ S := by
  classical
  obtain ⟨M, hM⟩ := SimpleGraph.tutte.mpr hTutte
  letI : Fintype M.spanningCoe.edgeSet := M.spanningCoe.edgeSet.toFinite.fintype
  obtain ⟨groups, hgroupsCard, hgroupsPoint, hgroupsCover⟩ :=
    exists_pairGroups_of_collisionGraph_perfectMatching B M hM
  have hedgeCard : M.spanningCoe.edgeFinset.card =
      M.spanningCoe.edgeSet.ncard := by
    rw [M.spanningCoe.edgeFinset_card]
    exact Set.fintypeCard_eq_ncard _
  refine ⟨groups, ?_, hgroupsPoint, hgroupsCover⟩
  calc
    2 * groups.card ≤ 2 * M.spanningCoe.edgeFinset.card :=
      Nat.mul_le_mul_left 2 hgroupsCard
    _ = 2 * M.spanningCoe.edgeSet.ncard := congrArg (2 * ·) hedgeCard
    _ = Fintype.card V := twice_card_edges_eq_card_of_isPerfectMatching M hM

#print axioms twice_card_edges_eq_card_of_isPerfectMatching
#print axioms exists_pairGroups_of_collisionGraph_of_noTutteViolator

end Erdos85
