import Mathlib

/-! # Marked-edge matching forced by cubic equality -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- If every vertex of a four-set lies on exactly one marked edge, and every
marked edge has both endpoints in that set, then there are exactly two marked
edges.  This is the incidence-counting core of the cubic-fiber equality case:
the four exceptional coordinates must be paired by two value-five edges. -/
theorem four_vertices_unique_markedEdge_card_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (X : Finset V) (M : Finset R.edgeFinset)
    (hX : X.card = 4)
    (hinside : ∀ e ∈ M, e.1.toFinset ⊆ X)
    (hunique : ∀ x ∈ X, ∃! e : R.edgeFinset,
      e ∈ M ∧ x ∈ e.1.toFinset) :
    M.card = 2 := by
  classical
  let I : ℕ := ∑ x ∈ X, ∑ e ∈ M,
    if x ∈ e.1.toFinset then 1 else 0
  have hIvertex : I = 4 := by
    calc
      I = ∑ _x ∈ X, 1 := by
        apply Finset.sum_congr rfl
        intro x hx
        obtain ⟨e, ⟨heM, hxe⟩, heuniq⟩ := hunique x hx
        rw [Finset.sum_boole]
        apply Finset.card_eq_one.mpr
        refine ⟨e, ?_⟩
        ext f
        simp only [Finset.mem_filter]
        constructor
        · intro hf
          exact Finset.mem_singleton.mpr (heuniq f ⟨hf.1, hf.2⟩)
        · intro hf
          have hfe : f = e := Finset.mem_singleton.mp hf
          subst f
          exact ⟨heM, hxe⟩
      _ = 4 := by simp [hX]
  have hIedge : I = 2 * M.card := by
    calc
      I = ∑ e ∈ M, ∑ x ∈ X,
          if x ∈ e.1.toFinset then 1 else 0 := by
            simp only [I]
            rw [Finset.sum_comm]
      _ = ∑ _e ∈ M, 2 := by
        apply Finset.sum_congr rfl
        intro e he
        rw [Finset.sum_boole]
        have hinter : X.filter (· ∈ e.1.toFinset) = e.1.toFinset := by
          ext x
          simp only [Finset.mem_filter]
          constructor
          · exact fun hx => hx.2
          · intro hx
            exact ⟨hinside e he hx, hx⟩
        rw [hinter]
        norm_num [R.card_toFinset_mem_edgeFinset e]
      _ = 2 * M.card := by simp [mul_comm]
  omega

end

end Erdos85

#print axioms Erdos85.four_vertices_unique_markedEdge_card_two
