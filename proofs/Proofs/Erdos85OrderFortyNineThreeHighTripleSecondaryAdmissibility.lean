import Proofs.Erdos85OrderFortyNineThreeHighTripleSecondaryParameters
import Proofs.Erdos85EncodedC4Filter

/-! Necessary finite checks for every actual secondary parameter tuple. -/
namespace Erdos85
open SimpleGraph
noncomputable section

def encodedEdgeCount {W : Type*} [Fintype W] (B : W → W → Bool) : ℕ :=
  (∑ p, (Finset.univ.filter fun q => B p q).card) / 2

private theorem encodedEdgeCount_eq_graph
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (B : W → W → Bool)
    (hB : ∀ p q, decide (H.Adj p q) = B p q) : encodedEdgeCount B = H.edgeFinset.card := by
  classical
  have hrow (p : W) : (Finset.univ.filter fun q => B p q) = H.neighborFinset p := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
    rw [← hB]
    simp
  unfold encodedEdgeCount
  simp_rw [hrow, SimpleGraph.card_neighborFinset_eq_degree]
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
  simp

theorem threeHigh_triple_secondary_admissible_parameters
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z) :
    let N := G.neighborFinset u ∩ threeHighTripleEmptySet G
    let R := threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)
    let m := (G.induce (↑N : Set (Fin 49))).edgeFinset.card
    ∃ (l : Fin 8 ≃ (↑R : Set (Fin 49))) (choice : Fin 2 → Option (Fin 6)) (ε : Bool),
      (∀ i : Fin 6, (l (Fin.castAdd 2 i)).val ∈ N) ∧
      (∀ a : Fin 2, (l (Fin.natAdd 6 a)).val ∈ R \ N) ∧
      (∀ p q, decide (G.Adj (l p).val (l q).val) = threeHighSecondaryAdj m choice ε p q) ∧
      encodedC4Free (threeHighSecondaryAdj m choice ε) = true ∧
      (encodedEdgeCount (threeHighSecondaryAdj m choice ε) = 3 ∨
        encodedEdgeCount (threeHighSecondaryAdj m choice ε) = 4) ∧
      ∀ a, choice a ≠ none ∨ ε = true := by
  classical
  let N := G.neighborFinset u ∩ threeHighTripleEmptySet G
  let R := threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)
  let m := (G.induce (↑N : Set (Fin 49))).edgeFinset.card
  obtain ⟨l, choice, ε, hlN, hlT, henc⟩ := threeHigh_triple_secondary_parameterization
    G hfree hmin hHigh hone z hz hu huz
  have hinj : Function.Injective (fun p => (l p).val) := by
    intro p q hpq
    exact l.injective (Subtype.ext hpq)
  have hC4 := encodedC4Free_of_injective_graph G hfree (fun p => (l p).val) hinj
    (threeHighSecondaryAdj m choice ε) henc
  let H := SimpleGraph.comap l (G.induce (↑R : Set (Fin 49)))
  have hcnt : encodedEdgeCount (threeHighSecondaryAdj m choice ε) =
      (G.induce (↑R : Set (Fin 49))).edgeFinset.card := by
    have he := encodedEdgeCount_eq_graph H (threeHighSecondaryAdj m choice ε) henc
    exact he.trans (SimpleGraph.Iso.comap l (G.induce (↑R : Set (Fin 49)))).card_edgeFinset_eq
  have hr := threeHigh_triple_secondary_edges_three_or_four G hfree hmin hHigh hone z hz hu huz
  refine ⟨l, choice, ε, hlN, hlT, henc, hC4, ?_, ?_⟩
  · rw [hcnt]
    exact hr
  · intro a
    by_cases heps : ε = true
    · exact Or.inr heps
    by_cases hnone : choice a = none
    · have hzero (q : Fin 8) : threeHighSecondaryAdj m choice ε (Fin.natAdd 6 a) q = false := by
        refine Fin.addCases (m := 6) (n := 2) (fun i => ?_) (fun b => ?_) q
        · simp only [threeHighSecondaryAdj, finSumFinEquiv_symm_apply_natAdd,
            finSumFinEquiv_symm_apply_castAdd]
          simp [hnone]
        · simp only [threeHighSecondaryAdj, finSumFinEquiv_symm_apply_natAdd]
          simp [heps]
      obtain ⟨w, hw, hvw⟩ := threeHigh_triple_far_vertex_has_secondary_neighbor
        G hfree hmin hHigh hone z hz hu huz (hlT a)
      let q := l.symm ⟨w, hw⟩
      have hq : (l q).val = w := congrArg Subtype.val (l.apply_symm_apply ⟨w, hw⟩)
      have hadj : G.Adj (l (Fin.natAdd 6 a)).val (l q).val := by rw [hq]; exact hvw
      have hb := (henc (Fin.natAdd 6 a) q).symm.trans (decide_eq_true hadj)
      rw [hzero] at hb
      cases hb
    · exact Or.inl hnone

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_secondary_admissible_parameters
