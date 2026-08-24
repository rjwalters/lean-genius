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

end Erdos85
