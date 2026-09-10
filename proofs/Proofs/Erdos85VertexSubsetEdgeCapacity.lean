import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Vertex-subset certificates for edge-capacity obstructions

For a graph X contained in an allowed graph F, count edges touching U by
their degree incidences on U and all other edges by the allowed edges
outside U. This is the generic inequality used in the H7 singleton cuts.
-/
namespace Erdos85
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every edge touching U consumes at least one degree unit in U; the
remaining edges are among allowed edges avoiding U. -/
theorem vertex_subset_edge_capacity_bound
    (X F : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel F.Adj]
    (U : Finset V) (capacity : V → ℕ)
    (hsub : X ≤ F) (hcap : ∀ v ∈ U, X.degree v ≤ capacity v) :
    X.edgeFinset.card ≤ (∑ v ∈ U, capacity v) +
      (F.edgeFinset.filter (fun e => ∀ v ∈ U, v ∉ e)).card := by
  classical
  let outside := F.edgeFinset.filter (fun e => ∀ v ∈ U, v ∉ e)
  have hcover : X.edgeFinset ⊆ U.biUnion (fun v => X.incidenceFinset v) ∪ outside := by
    intro e he
    by_cases h : ∃ v ∈ U, v ∈ e
    · obtain ⟨v, hv, hve⟩ := h
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨v, hv, ?_⟩
      rw [X.incidenceFinset_eq_filter]
      exact Finset.mem_filter.mpr ⟨he, hve⟩
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨SimpleGraph.edgeFinset_mono hsub he, ?_⟩
      intro v hv hve
      exact h ⟨v, hv, hve⟩
  calc
    X.edgeFinset.card ≤ (U.biUnion (fun v => X.incidenceFinset v) ∪ outside).card :=
      Finset.card_le_card hcover
    _ ≤ (U.biUnion (fun v => X.incidenceFinset v)).card + outside.card := Finset.card_union_le _ _
    _ ≤ (∑ v ∈ U, (X.incidenceFinset v).card) + outside.card :=
      Nat.add_le_add_right Finset.card_biUnion_le _
    _ ≤ (∑ v ∈ U, capacity v) + outside.card := by
      apply Nat.add_le_add_right
      apply Finset.sum_le_sum
      intro v hv
      simpa using hcap v hv

/-- A lower edge bound exceeding a vertex-subset capacity certificate is
impossible. No C4, triangle, or spectrum hypothesis is needed. -/
theorem not_exists_graph_of_vertex_subset_capacity_cut
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (U : Finset V) (capacity : V → ℕ) (lower : ℕ)
    (hcut : (∑ v ∈ U, capacity v) +
      (F.edgeFinset.filter (fun e => ∀ v ∈ U, v ∉ e)).card < lower)
    (X : SimpleGraph V) [DecidableRel X.Adj]
    (hsub : X ≤ F) (hcap : ∀ v ∈ U, X.degree v ≤ capacity v)
    (hlower : lower ≤ X.edgeFinset.card) : False := by
  have h := vertex_subset_edge_capacity_bound X F U capacity hsub hcap
  omega

end Erdos85
#print axioms Erdos85.vertex_subset_edge_capacity_bound
#print axioms Erdos85.not_exists_graph_of_vertex_subset_capacity_cut
