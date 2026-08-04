import Proofs.Erdos85MinimalWitness

/-!
# Layered top witnesses for Erdős Problem 85
-/

open SimpleGraph

namespace Erdos85

theorem card_tightVertices_add_card_aboveMinVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hdegree : G.minDegree = d) :
    (tightVertices G d).card + (aboveMinVertices G d).card =
      Fintype.card V := by
  have hdisjoint : Disjoint (tightVertices G d) (aboveMinVertices G d) := by
    rw [Finset.disjoint_left]
    intro v hvT hvU
    have hvEq : G.degree v = d := by simpa [tightVertices] using hvT
    have hvLt : d < G.degree v := by simpa [aboveMinVertices] using hvU
    omega
  have hunion : tightVertices G d ∪ aboveMinVertices G d = Finset.univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    have hv : d ≤ G.degree v := by
      rw [← hdegree]
      exact G.minDegree_le_degree v
    simp only [tightVertices, aboveMinVertices, Finset.mem_filter,
      Finset.mem_univ, true_and]
    omega
  rw [← Finset.card_union_of_disjoint hdisjoint, hunion,
    Finset.card_univ]

/-- **Layered threshold normal form.** At every order n at least four, a top
C4-free witness may be chosen with tight vertices covering every edge. Its
high-degree vertices form an independent layer whose large neighborhoods pack
linearly into the tight layer. -/
theorem exists_top_layered_witness {n : ℕ} (hn : 4 ≤ n) :
    let d := minDegreeForC4 n - 1
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.minDegree = d ∧
      ¬ containsC4 (Fin n) G ∧
      (∀ ⦃u v⦄, G.Adj u v →
        G.degree u = d ∨ G.degree v = d) ∧
      (tightVertices G d).card + (aboveMinVertices G d).card = n ∧
      (aboveMinVertices G d).card * (d + 1).choose 2 ≤
        (tightVertices G d).card.choose 2 := by
  dsimp
  obtain ⟨G, hdec, hdegree, hfree, hcover⟩ :=
    exists_top_edgeCovered_exact_minDegree hn
  letI : DecidableRel G.Adj := hdec
  refine ⟨G, hdec, hdegree, hfree, hcover, ?_, ?_⟩
  · simpa using card_tightVertices_add_card_aboveMinVertices G hdegree
  · exact card_aboveMin_mul_choose_succ_le_choose_card_tight
      G hfree hcover

end Erdos85
