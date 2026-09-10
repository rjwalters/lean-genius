import Proofs.Erdos85OrderFortyNineThreeHighTripleSecondaryAdmissibility

/-! The exact finite domain of labeled secondary parameter tuples. -/
namespace Erdos85
open SimpleGraph

abbrev ThreeHighSecondaryTuple := Fin 3 × (Fin 2 → Option (Fin 6)) × Bool

def threeHighSecondaryTupleAdj (t : ThreeHighSecondaryTuple) : Fin 8 → Fin 8 → Bool :=
  threeHighSecondaryAdj (t.1.val + 1) t.2.1 t.2.2

def threeHighSecondaryDomain : Finset ThreeHighSecondaryTuple :=
  Finset.univ.filter fun t =>
    encodedC4Free (threeHighSecondaryTupleAdj t) = true ∧
    (encodedEdgeCount (threeHighSecondaryTupleAdj t) = 3 ∨
      encodedEdgeCount (threeHighSecondaryTupleAdj t) = 4) ∧
    ∀ a, t.2.1 a ≠ none ∨ t.2.2 = true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighSecondaryDomain_card : threeHighSecondaryDomain.card = 132 := by
  decide

noncomputable section

theorem threeHigh_triple_secondary_domain_cover
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
    ∃ t ∈ threeHighSecondaryDomain, ∃ l : Fin 8 ≃ (↑R : Set (Fin 49)),
      m = t.1.val + 1 ∧
      (∀ i : Fin 6, (l (Fin.castAdd 2 i)).val ∈ N) ∧
      (∀ a : Fin 2, (l (Fin.natAdd 6 a)).val ∈ R \ N) ∧
      ∀ p q, decide (G.Adj (l p).val (l q).val) = threeHighSecondaryTupleAdj t p q := by
  classical
  let N := G.neighborFinset u ∩ threeHighTripleEmptySet G
  let R := threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)
  let m := (G.induce (↑N : Set (Fin 49))).edgeFinset.card
  obtain ⟨l, choice, ε, hlN, hlT, henc, hC4, hcount, hfar⟩ :=
    threeHigh_triple_secondary_admissible_parameters G hfree hmin hHigh hone z hz hu huz
  have hm := threeHigh_triple_secondary_matching_edge_bounds G hfree hmin hHigh hone z hz hu huz
  change 1 ≤ m ∧ m ≤ 3 at hm
  let i : Fin 3 := ⟨m - 1, by omega⟩
  have hi : i.val + 1 = m := by dsimp [i]; omega
  let t : ThreeHighSecondaryTuple := ⟨i, choice, ε⟩
  have ht : t ∈ threeHighSecondaryDomain := by
    simp only [threeHighSecondaryDomain, Finset.mem_filter, Finset.mem_univ, true_and]
    change encodedC4Free (threeHighSecondaryAdj (i.val + 1) choice ε) = true ∧
      (encodedEdgeCount (threeHighSecondaryAdj (i.val + 1) choice ε) = 3 ∨
        encodedEdgeCount (threeHighSecondaryAdj (i.val + 1) choice ε) = 4) ∧ _
    rw [hi]
    exact ⟨hC4, hcount, hfar⟩
  refine ⟨t, ht, l, hi.symm, hlN, hlT, ?_⟩
  intro p q
  change decide (G.Adj (l p).val (l q).val) = threeHighSecondaryAdj (i.val + 1) choice ε p q
  rw [hi]
  exact henc p q

end
end Erdos85
#print axioms Erdos85.threeHighSecondaryDomain_card
#print axioms Erdos85.threeHigh_triple_secondary_domain_cover
