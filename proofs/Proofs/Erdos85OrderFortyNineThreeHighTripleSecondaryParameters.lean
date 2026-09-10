import Proofs.Erdos85OrderFortyNineThreeHighTripleSecondaryCoordinates

/-! Exact finite parameters for the labeled secondary graph. -/
namespace Erdos85
open SimpleGraph
noncomputable section

private theorem optional_index_of_unique {n : ℕ} (P : Fin n → Prop)
    (huniq : ∀ i j, P i → P j → i = j) :
    ∃ o : Option (Fin n), ∀ i, P i ↔ o = some i := by
  classical
  by_cases h : ∃ i, P i
  · obtain ⟨i, hi⟩ := h
    refine ⟨some i, ?_⟩
    intro j
    constructor
    · intro hj
      exact congrArg some (huniq i j hi hj)
    · intro he
      have hij := Option.some.inj he
      simpa only [← hij] using hi
  · refine ⟨none, ?_⟩
    intro i
    constructor
    · intro hi
      exact (h ⟨i, hi⟩).elim
    · intro hi
      cases hi

def threeHighSecondaryAdj (m : ℕ) (choice : Fin 2 → Option (Fin 6)) (ε : Bool)
    (p q : Fin 8) : Bool :=
  match (finSumFinEquiv.symm p : Fin 6 ⊕ Fin 2), (finSumFinEquiv.symm q : Fin 6 ⊕ Fin 2) with
  | Sum.inl i, Sum.inl j => decide (matchingFinSixAdj m i j)
  | Sum.inr a, Sum.inl i => decide (choice a = some i)
  | Sum.inl i, Sum.inr a => decide (choice a = some i)
  | Sum.inr a, Sum.inr b => decide (a ≠ b ∧ ε = true)

theorem threeHigh_triple_secondary_parameterization
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
      ∀ p q, decide (G.Adj (l p).val (l q).val) = threeHighSecondaryAdj m choice ε p q := by
  classical
  let N := G.neighborFinset u ∩ threeHighTripleEmptySet G
  let R := threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)
  let m := (G.induce (↑N : Set (Fin 49))).edgeFinset.card
  obtain ⟨l, hlN, hlT, hlM⟩ := threeHigh_triple_secondary_coordinates G hfree hmin hHigh hone z hz hu huz
  have huniq (a : Fin 2) (i j : Fin 6)
      (hi : G.Adj (l (Fin.natAdd 6 a)).val (l (Fin.castAdd 2 i)).val)
      (hj : G.Adj (l (Fin.natAdd 6 a)).val (l (Fin.castAdd 2 j)).val) : i = j := by
    have hc := threeHigh_triple_secondary_vertex_neighbor_bound G hfree hmin hHigh hone z u
      (l (Fin.natAdd 6 a)).property
    have he := Finset.card_le_one.mp hc (l (Fin.castAdd 2 i)).val
      (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hi, hlN i⟩)
      (l (Fin.castAdd 2 j)).val
      (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hj, hlN j⟩)
    have hlabel := l.injective (Subtype.ext he)
    apply Fin.ext
    exact congrArg (fun x : Fin 8 => x.val) hlabel
  have hex (a : Fin 2) : ∃ o : Option (Fin 6), ∀ i,
      G.Adj (l (Fin.natAdd 6 a)).val (l (Fin.castAdd 2 i)).val ↔ o = some i :=
    optional_index_of_unique _ (huniq a)
  choose choice hchoice using hex
  let ε : Bool := decide (G.Adj (l (Fin.natAdd 6 (0 : Fin 2))).val (l (Fin.natAdd 6 (1 : Fin 2))).val)
  have hfar (a b : Fin 2) :
      G.Adj (l (Fin.natAdd 6 a)).val (l (Fin.natAdd 6 b)).val ↔ a ≠ b ∧ ε = true := by
    fin_cases a <;> fin_cases b <;> simp [ε, G.adj_comm]
  refine ⟨l, choice, ε, hlN, hlT, ?_⟩
  intro p q
  refine Fin.addCases (m := 6) (n := 2) (fun i => ?_) (fun a => ?_) p
  · refine Fin.addCases (m := 6) (n := 2) (fun j => ?_) (fun b => ?_) q
    · simpa only [threeHighSecondaryAdj, finSumFinEquiv_symm_apply_castAdd] using Bool.decide_congr (hlM i j)
    · simpa only [threeHighSecondaryAdj, finSumFinEquiv_symm_apply_castAdd,
        finSumFinEquiv_symm_apply_natAdd] using Bool.decide_congr ((G.adj_comm _ _).trans (hchoice b i))
  · refine Fin.addCases (m := 6) (n := 2) (fun j => ?_) (fun b => ?_) q
    · simpa only [threeHighSecondaryAdj, finSumFinEquiv_symm_apply_castAdd,
        finSumFinEquiv_symm_apply_natAdd] using Bool.decide_congr (hchoice a j)
    · simpa only [threeHighSecondaryAdj, finSumFinEquiv_symm_apply_natAdd] using Bool.decide_congr (hfar a b)

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_secondary_parameterization
