import Proofs.Erdos85EdgesAvoidingSubsetBound

/-! Two forbidden pairs improve the complement edge bound by two. -/
namespace Erdos85
open SimpleGraph

theorem edges_avoiding_subset_add_two_le_choose
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (e f : Sym2 V) (hef : e ≠ f)
    (he : ¬ e.IsDiag) (hf : ¬ f.IsDiag)
    (heG : e ∉ G.edgeFinset) (hfG : f ∉ G.edgeFinset)
    (heU : ∀ v ∈ U, v ∉ e) (hfU : ∀ v ∈ U, v ∉ f) :
    (G.edgeFinset.filter (fun p => ∀ v ∈ U, v ∉ p)).card + 2 ≤
      (Fintype.card V - U.card).choose 2 := by
  classical
  let A := G.edgeFinset.filter (fun p => ∀ v ∈ U, v ∉ p)
  let T := (⊤ : SimpleGraph V).edgeFinset.filter (fun p => ∀ v ∈ U, v ∉ p)
  have heT : e ∈ T := by
    apply Finset.mem_filter.mpr
    exact ⟨by simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top] using he, heU⟩
  have hfT : f ∈ T := by
    apply Finset.mem_filter.mpr
    exact ⟨by simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top] using hf, hfU⟩
  have hdis : Disjoint A {e, f} := by
    apply Finset.disjoint_left.mpr
    intro p hp hpair
    have hpG := (Finset.mem_filter.mp hp).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpair
    rcases hpair with rfl | rfl
    · exact heG hpG
    · exact hfG hpG
  have hsub : A ∪ {e, f} ⊆ T := by
    intro p hp
    rcases Finset.mem_union.mp hp with ha | hpair
    · have h := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨SimpleGraph.edgeFinset_mono le_top h.1, h.2⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpair
      rcases hpair with rfl | rfl
      · exact heT
      · exact hfT
  have hcard : (A ∪ {e, f}).card = A.card + 2 := by
    rw [Finset.card_union_of_disjoint hdis]
    simp [hef]
  have h := (Finset.card_le_card hsub).trans
    (edges_avoiding_subset_card_le_choose (⊤ : SimpleGraph V) U)
  rwa [hcard] at h

end Erdos85
#print axioms Erdos85.edges_avoiding_subset_add_two_le_choose
