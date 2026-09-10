import Proofs.Erdos85OneHighCanonicalMate

/-! Standard-axiom five-point matching normalization, independent of the legacy
native-evaluation classification proofs. Reuses only their definitions. -/
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
namespace Erdos85
noncomputable section
theorem oneHighBranchEdgeIndex_lt_kernel (i j : Fin 5) (hij : i ≠ j) :
    oneHighBranchEdgeIndex i j < 10 := by
  decide +revert

theorem oneHighBranchEdgeIndex_eq_iff_kernel
    (i j k l : Fin 5) (hij : i ≠ j) (hkl : k ≠ l) :
    oneHighBranchEdgeIndex i j = oneHighBranchEdgeIndex k l ↔
      (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  decide +revert

theorem oneHighBranchBitAdj_graphEdges_kernel
    (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] (i j : Fin 5) :
    oneHighBranchBitAdj (oneHighBranchGraphEdges G) i j =
      decide (G.Adj i j) := by
  by_cases hij : i = j
  · subst j
    simp [oneHighBranchBitAdj]
  · have hlt := oneHighBranchEdgeIndex_lt_kernel i j hij
    simp only [oneHighBranchBitAdj, hij, if_false, oneHighBranchGraphEdges,
      BitVec.getLsbD_ofFnLE]
    rw [dif_pos hlt]
    apply Bool.decide_congr
    constructor
    · rintro ⟨k, l, hkl, hindex, hadj⟩
      rcases (oneHighBranchEdgeIndex_eq_iff_kernel k l i j hkl hij).mp hindex with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hadj
      · exact (G.adj_comm _ _).mp hadj
    · intro hadj
      exact ⟨i, j, hij, rfl, hadj⟩


theorem finFive_matchingBits_canonical_kernel
    (edges : BitVec 10) (twoEdges : Bool)
    (hdegree : ∀ i : Fin 5,
      (Finset.univ.filter fun j => oneHighBranchBitAdj edges i j).card ≤ 1)
    (hmatched : (Finset.univ.filter fun i =>
      (Finset.univ.filter fun j => oneHighBranchBitAdj edges i j).card = 1).card =
        if twoEdges then 4 else 2) :
    ∃ σ : Equiv.Perm (Fin 5), ∀ i j,
      oneHighBranchBitAdj edges i j =
        oneHighCanonicalBranchAdj twoEdges (σ i) (σ j) := by
  decide +revert

theorem exists_equiv_finFive_canonical_matching_kernel
    {P : Type*} [Fintype P] [DecidableEq P]
    (H : SimpleGraph P) [DecidableRel H.Adj]
    (hcard : Fintype.card P = 5)
    (hdegree : ∀ x : P, H.degree x ≤ 1)
    (hmatched : ((Finset.univ : Finset P).filter fun x =>
      H.degree x = 1).card = 2 ∨
      ((Finset.univ : Finset P).filter fun x => H.degree x = 1).card = 4) :
    ∃ (twoEdges : Bool) (e : P ≃ Fin 5),
      ((twoEdges = false ∧
          ((Finset.univ : Finset P).filter fun x => H.degree x = 1).card = 2) ∨
        (twoEdges = true ∧
          ((Finset.univ : Finset P).filter fun x => H.degree x = 1).card = 4)) ∧
      ∀ x y, decide (H.Adj x y) =
        oneHighCanonicalBranchAdj twoEdges (e x) (e y) := by
  classical
  let e₀ : P ≃ Fin 5 := Fintype.equivFinOfCardEq hcard
  let R : SimpleGraph (Fin 5) := SimpleGraph.comap e₀.symm H
  letI : DecidableRel R.Adj := Classical.decRel R.Adj
  have hRdegree : ∀ i : Fin 5, R.degree i = H.degree (e₀.symm i) := by
    intro i
    exact (SimpleGraph.Iso.comap e₀.symm H).degree_eq i |>.symm
  have hmatchedEq :
      ((Finset.univ : Finset (Fin 5)).filter fun i => R.degree i = 1).card =
        ((Finset.univ : Finset P).filter fun x => H.degree x = 1).card := by
    apply Finset.card_bij (fun i _ => e₀.symm i)
    · intro i hi
      have hi1 := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hRdegree] using hi1⟩
    · intro i _ j _ hij
      exact e₀.symm.injective hij
    · intro x hx
      refine ⟨e₀ x, ?_, by simp⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rw [hRdegree]
        rw [e₀.symm_apply_apply]
        exact (Finset.mem_filter.mp hx).2⟩
  have hbitDegree : ∀ i : Fin 5,
      (Finset.univ.filter fun j =>
        oneHighBranchBitAdj (oneHighBranchGraphEdges R) i j).card ≤ 1 := by
    intro i
    have hi := hdegree (e₀.symm i)
    rw [← hRdegree] at hi
    have heq : (Finset.univ.filter fun j =>
        oneHighBranchBitAdj (oneHighBranchGraphEdges R) i j) =
        R.neighborFinset i := by
      ext j
      simp [oneHighBranchBitAdj_graphEdges_kernel,
        SimpleGraph.mem_neighborFinset, decide_eq_true_eq]
    rw [heq, R.card_neighborFinset_eq_degree]
    exact hi
  rcases hmatched with hm2 | hm4
  · have hbitMatched : (Finset.univ.filter fun i =>
        (Finset.univ.filter fun j =>
          oneHighBranchBitAdj (oneHighBranchGraphEdges R) i j).card = 1).card = 2 := by
      have heq : (Finset.univ.filter fun i =>
          (Finset.univ.filter fun j =>
            oneHighBranchBitAdj (oneHighBranchGraphEdges R) i j).card = 1) =
          Finset.univ.filter fun i => R.degree i = 1 := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hrow : (Finset.univ.filter fun j =>
            oneHighBranchBitAdj (oneHighBranchGraphEdges R) i j) =
            R.neighborFinset i := by
          ext j
          simp [oneHighBranchBitAdj_graphEdges_kernel,
            SimpleGraph.mem_neighborFinset, decide_eq_true_eq]
        rw [hrow, R.card_neighborFinset_eq_degree]
      rw [heq, hmatchedEq, hm2]
    obtain ⟨σ, hσ⟩ := finFive_matchingBits_canonical_kernel
      (oneHighBranchGraphEdges R) false hbitDegree (by simpa using hbitMatched)
    refine ⟨false, e₀.trans σ, Or.inl ⟨rfl, hm2⟩, ?_⟩
    intro x y
    have hh := hσ (e₀ x) (e₀ y)
    rw [oneHighBranchBitAdj_graphEdges_kernel] at hh
    simpa [R] using hh
  · have hbitMatched : (Finset.univ.filter fun i =>
        (Finset.univ.filter fun j =>
          oneHighBranchBitAdj (oneHighBranchGraphEdges R) i j).card = 1).card = 4 := by
      have heq : (Finset.univ.filter fun i =>
          (Finset.univ.filter fun j =>
            oneHighBranchBitAdj (oneHighBranchGraphEdges R) i j).card = 1) =
          Finset.univ.filter fun i => R.degree i = 1 := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hrow : (Finset.univ.filter fun j =>
            oneHighBranchBitAdj (oneHighBranchGraphEdges R) i j) =
            R.neighborFinset i := by
          ext j
          simp [oneHighBranchBitAdj_graphEdges_kernel,
            SimpleGraph.mem_neighborFinset, decide_eq_true_eq]
        rw [hrow, R.card_neighborFinset_eq_degree]
      rw [heq, hmatchedEq, hm4]
    obtain ⟨σ, hσ⟩ := finFive_matchingBits_canonical_kernel
      (oneHighBranchGraphEdges R) true hbitDegree (by simpa using hbitMatched)
    refine ⟨true, e₀.trans σ, Or.inr ⟨rfl, hm4⟩, ?_⟩
    intro x y
    have hh := hσ (e₀ x) (e₀ y)
    rw [oneHighBranchBitAdj_graphEdges_kernel] at hh
    simpa [R] using hh


/-- Two edges in a five-vertex graph of maximum degree one admit exactly the
canonical two-edge matching labels. -/
theorem exists_equiv_finFive_two_edge_matching
    {P : Type*} [Fintype P] [DecidableEq P]
    (H : SimpleGraph P) [DecidableRel H.Adj]
    (hcard : Fintype.card P = 5)
    (hdegree : ∀ x : P, H.degree x ≤ 1)
    (hedges : H.edgeFinset.card = 2) :
    ∃ e : P ≃ Fin 5, ∀ x y,
      decide (H.Adj x y) = oneHighCanonicalBranchAdj true (e x) (e y) := by
  classical
  have hsum : (∑ x : P, H.degree x) =
      ((Finset.univ : Finset P).filter fun x => H.degree x = 1).card := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro x _
    have hd := hdegree x
    split_ifs <;> omega
  have hm : ((Finset.univ : Finset P).filter fun x => H.degree x = 1).card = 4 := by
    rw [← hsum, SimpleGraph.sum_degrees_eq_twice_card_edges, hedges]
  obtain ⟨b,e,hb,he⟩ := exists_equiv_finFive_canonical_matching_kernel
    H hcard hdegree (Or.inr hm)
  rcases hb with hb | hb
  · omega
  · rcases hb with ⟨rfl,_⟩
    exact ⟨e,he⟩

end
end Erdos85
#print axioms Erdos85.exists_equiv_finFive_canonical_matching_kernel

#print axioms Erdos85.exists_equiv_finFive_two_edge_matching
