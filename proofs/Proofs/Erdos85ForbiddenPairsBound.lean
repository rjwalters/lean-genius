import Proofs.Erdos85EdgesAvoidingSubsetBound

/-! A finite family of forbidden pairs improves the complement edge bound. -/
namespace Erdos85
open SimpleGraph

theorem edges_avoiding_subset_add_forbidden_card_le_choose
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (B : Finset (Sym2 V))
    (hB : ∀ e ∈ B, ¬ e.IsDiag ∧ e ∉ G.edgeFinset ∧ ∀ v ∈ U, v ∉ e) :
    (G.edgeFinset.filter (fun e => ∀ v ∈ U, v ∉ e)).card + B.card ≤
      (Fintype.card V - U.card).choose 2 := by
  classical
  let A := G.edgeFinset.filter (fun e => ∀ v ∈ U, v ∉ e)
  let T := (⊤ : SimpleGraph V).edgeFinset.filter (fun e => ∀ v ∈ U, v ∉ e)
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro e heA heB
    exact (hB e heB).2.1 (Finset.mem_filter.mp heA).1
  have hsub : A ∪ B ⊆ T := by
    intro e he
    rcases Finset.mem_union.mp he with heA | heB
    · have h := Finset.mem_filter.mp heA
      exact Finset.mem_filter.mpr ⟨SimpleGraph.edgeFinset_mono le_top h.1, h.2⟩
    · have h := hB e heB
      apply Finset.mem_filter.mpr
      exact ⟨by simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top] using h.1, h.2.2⟩
  calc
    A.card + B.card = (A ∪ B).card := (Finset.card_union_of_disjoint hdis).symm
    _ ≤ T.card := Finset.card_le_card hsub
    _ ≤ (Fintype.card V - U.card).choose 2 :=
      edges_avoiding_subset_card_le_choose (⊤ : SimpleGraph V) U

end Erdos85
#print axioms Erdos85.edges_avoiding_subset_add_forbidden_card_le_choose
