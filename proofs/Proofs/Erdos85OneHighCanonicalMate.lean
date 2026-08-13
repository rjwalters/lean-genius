import Proofs.Erdos85PairedBlockRigidity

/-!
# Canonical labeling of the one-high mate involution

The family CNFs number the eight branches so that mate pairs are
`0↔1, 2↔3, 4↔5, 6↔7`.  This file supplies the finite conjugacy theorem which
turns the graph's intrinsic fixed-point-free involution into that convention.
-/

namespace Erdos85

noncomputable section

/-- The standard four-pair involution used by the family encoders. -/
def oneHighStandardMate : Equiv.Perm (Fin 8) :=
  Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 * Equiv.swap 6 7

theorem oneHighStandardMate_involutive :
    Function.Involutive oneHighStandardMate := by
  intro i
  native_decide +revert

theorem oneHighStandardMate_ne (i : Fin 8) : oneHighStandardMate i ≠ i := by
  native_decide +revert

/-- Every fixed-point-free involution of eight points is conjugate to the
standard four-pair involution.  This is a closed finite classification over
the `8!` permutations, checked by native evaluation. -/
theorem finEight_fixedPointFreeInvolution_conjugate_standard
    (p : Equiv.Perm (Fin 8))
    (hinv : ∀ i, p (p i) = i)
    (hfix : ∀ i, p i ≠ i) :
    ∃ σ : Equiv.Perm (Fin 8),
      ∀ i, σ (p i) = oneHighStandardMate (σ i) := by
  native_decide +revert

/-- Abstract eight-point form used for the graph neighborhood subtype. -/
theorem exists_equiv_finEight_intertwining_involution
    {P : Type*} [Fintype P] [DecidableEq P]
    (hcard : Fintype.card P = 8)
    (mate : P → P) (hinv : Function.Involutive mate)
    (hfix : ∀ x, mate x ≠ x) :
    ∃ e : P ≃ Fin 8, ∀ x, e (mate x) = oneHighStandardMate (e x) := by
  let e₀ : P ≃ Fin 8 := Fintype.equivFinOfCardEq hcard
  let p : Equiv.Perm (Fin 8) :=
    Equiv.ofBijective (fun i => e₀ (mate (e₀.symm i))) ⟨
      fun i j hij => by
        apply e₀.symm.injective
        apply hinv.injective
        simpa [e₀] using hij,
      fun j => ⟨e₀ (mate (e₀.symm j)), by
        simpa only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
          using congrArg e₀ (hinv (e₀.symm j))⟩⟩
  have hpInv : Function.Involutive p := by
    intro i
    change e₀ (mate (e₀.symm (e₀ (mate (e₀.symm i))))) = i
    simpa only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
      using congrArg e₀ (hinv (e₀.symm i))
  have hpFix : ∀ i, p i ≠ i := by
    intro i hi
    apply hfix (e₀.symm i)
    apply e₀.injective
    simpa [p] using hi
  obtain ⟨σ, hσ⟩ :=
    finEight_fixedPointFreeInvolution_conjugate_standard p hpInv hpFix
  refine ⟨e₀.trans σ, ?_⟩
  intro x
  simpa [p] using hσ (e₀ x)

/-- Graph-facing specialization: any mate involution on the eight neighbors
of the high root admits the exact branch numbering used by `family_gen.py`. -/
theorem exists_oneHigh_branchLabeling_intertwining_mate
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    (hv : G.degree v = 8)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hmateInv : Function.Involutive mate)
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1) :
    ∃ e : {z : V // z ∈ G.neighborSet v} ≃ Fin 8,
      ∀ s, e (mate s) = oneHighStandardMate (e s) := by
  let P := {z : V // z ∈ G.neighborSet v}
  have hPcard : Fintype.card P = 8 := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet v) =
        G.neighborFinset v := by ext z; simp
    rw [heq, G.card_neighborFinset_eq_degree, hv]
  apply exists_equiv_finEight_intertwining_involution hPcard mate hmateInv
  intro s hfix
  exact G.loopless.irrefl s.1 (congrArg Subtype.val hfix ▸ hmateAdj s)

/-! ## Canonical labels inside a five-point branch -/

/-- Lexicographic position of an unordered pair from `Fin 5`. -/
def oneHighBranchEdgeIndex (i j : Fin 5) : Nat :=
  let a := min i.val j.val
  let b := max i.val j.val
  10 - ((5 - a) * (4 - a) / 2) + (b - a) - 1

def oneHighBranchBitAdj (edges : BitVec 10) (i j : Fin 5) : Bool :=
  if i = j then false else edges.getLsbD (oneHighBranchEdgeIndex i j)

theorem oneHighBranchEdgeIndex_lt (i j : Fin 5) (hij : i ≠ j) :
    oneHighBranchEdgeIndex i j < 10 := by
  native_decide +revert

theorem oneHighBranchEdgeIndex_eq_iff
    (i j k l : Fin 5) (hij : i ≠ j) (hkl : k ≠ l) :
    oneHighBranchEdgeIndex i j = oneHighBranchEdgeIndex k l ↔
      (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  native_decide +revert

def oneHighBranchGraphEdges
    (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] : BitVec 10 :=
  BitVec.ofFnLE fun k => decide (∃ i j : Fin 5,
    i ≠ j ∧ oneHighBranchEdgeIndex i j = k.val ∧ G.Adj i j)

theorem oneHighBranchBitAdj_graphEdges
    (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] (i j : Fin 5) :
    oneHighBranchBitAdj (oneHighBranchGraphEdges G) i j =
      decide (G.Adj i j) := by
  by_cases hij : i = j
  · subst j
    simp [oneHighBranchBitAdj]
  · have hlt := oneHighBranchEdgeIndex_lt i j hij
    simp only [oneHighBranchBitAdj, hij, if_false, oneHighBranchGraphEdges,
      BitVec.getLsbD_ofFnLE]
    rw [dif_pos hlt]
    apply Bool.decide_congr
    constructor
    · rintro ⟨k, l, hkl, hindex, hadj⟩
      rcases (oneHighBranchEdgeIndex_eq_iff k l i j hkl hij).mp hindex with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hadj
      · exact (G.adj_comm _ _).mp hadj
    · intro hadj
      exact ⟨i, j, hij, rfl, hadj⟩

/-- The encoder's canonical one-edge/two-edge matching inside a branch. -/
def oneHighCanonicalBranchAdj (twoEdges : Bool) (i j : Fin 5) : Bool :=
  decide ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
    (twoEdges = true ∧ ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2))))

/-- Closed finite classification of five-point matchings. -/
theorem finFive_matchingBits_canonical
    (edges : BitVec 10) (twoEdges : Bool)
    (hdegree : ∀ i : Fin 5,
      (Finset.univ.filter fun j => oneHighBranchBitAdj edges i j).card ≤ 1)
    (hmatched : (Finset.univ.filter fun i =>
      (Finset.univ.filter fun j => oneHighBranchBitAdj edges i j).card = 1).card =
        if twoEdges then 4 else 2) :
    ∃ σ : Equiv.Perm (Fin 5), ∀ i j,
      oneHighBranchBitAdj edges i j =
        oneHighCanonicalBranchAdj twoEdges (σ i) (σ j) := by
  native_decide +revert

/-- Abstract five-point matching canonicalization.  The Boolean flag is
`false` for one internal edge and `true` for two internal edges. -/
theorem exists_equiv_finFive_canonical_matching
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
      simp [oneHighBranchBitAdj_graphEdges,
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
          simp [oneHighBranchBitAdj_graphEdges,
            SimpleGraph.mem_neighborFinset, decide_eq_true_eq]
        rw [hrow, R.card_neighborFinset_eq_degree]
      rw [heq, hmatchedEq, hm2]
    obtain ⟨σ, hσ⟩ := finFive_matchingBits_canonical
      (oneHighBranchGraphEdges R) false hbitDegree (by simpa using hbitMatched)
    refine ⟨false, e₀.trans σ, Or.inl ⟨rfl, hm2⟩, ?_⟩
    intro x y
    have hh := hσ (e₀ x) (e₀ y)
    rw [oneHighBranchBitAdj_graphEdges] at hh
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
          simp [oneHighBranchBitAdj_graphEdges,
            SimpleGraph.mem_neighborFinset, decide_eq_true_eq]
        rw [hrow, R.card_neighborFinset_eq_degree]
      rw [heq, hmatchedEq, hm4]
    obtain ⟨σ, hσ⟩ := finFive_matchingBits_canonical
      (oneHighBranchGraphEdges R) true hbitDegree (by simpa using hbitMatched)
    refine ⟨true, e₀.trans σ, Or.inr ⟨rfl, hm4⟩, ?_⟩
    intro x y
    have hh := hσ (e₀ x) (e₀ y)
    rw [oneHighBranchBitAdj_graphEdges] at hh
    simpa [R] using hh

/-- Graph-facing branch specialization.  Each five-point second-layer branch
can be numbered exactly as in `family_gen.py`: its internal edges are
`(0,1)` and, in the two-edge case, `(2,3)`. -/
theorem exists_oneHigh_branchVertexLabeling
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (hunique : ∀ {x : V}, G.degree x = 8 → x = v)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hmateInv : Function.Involutive mate)
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1)
    (s : {z : V // z ∈ G.neighborSet v}) :
    ∃ (twoEdges : Bool)
      (e : secondLayerBranch G v s ≃ Fin 5),
      ((twoEdges = false ∧ highBranchMatchedCount G v s = 2) ∨
        (twoEdges = true ∧ highBranchMatchedCount G v s = 4)) ∧
      ∀ x y, decide (G.Adj x.1 y.1) =
        oneHighCanonicalBranchAdj twoEdges (e x) (e y) := by
  classical
  let B := secondLayerBranch G v s
  let H := G.induce B
  have hBcard : Fintype.card B = 5 := by
    rw [Fintype.card_coe]
    exact orderFortyNine_card_secondLayerBranch_degreeEight_eq_five
      G hfree hmin hcard hv s
  have hHdegree : ∀ x : B, H.degree x ≤ 1 := by
    intro x
    simpa [B, H] using
      (degree_induce_secondLayerBranch_le_one G hfree v s x)
  have hmatchedEq :
      ((Finset.univ : Finset B).filter fun x => H.degree x = 1).card =
        highBranchMatchedCount G v s := by
    rw [highBranchMatchedCount]
    apply Finset.card_bij (fun x _ => x.1)
    · intro x hx
      have hxDeg := (Finset.mem_filter.mp hx).2
      exact Finset.mem_filter.mpr ⟨x.2, by
        rw [← degree_induce_secondLayerBranch_eq_card_inter]
        simpa [B, H] using hxDeg⟩
    · intro x _ y _ hxy
      exact Subtype.ext hxy
    · intro x hx
      let xb : B := ⟨x, (Finset.mem_filter.mp hx).1⟩
      refine ⟨xb, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        change (G.induce (secondLayerBranch G v s)).degree
          (⟨x, (Finset.mem_filter.mp hx).1⟩ :
            secondLayerBranch G v s) = 1
        rw [degree_induce_secondLayerBranch_eq_card_inter]
        exact (Finset.mem_filter.mp hx).2⟩
  have hstates := paired_highBranchMatchedCount_states
    G hfree hmin hcard hv hunique hexternal houterDegree
      mate hmateInv hmateAdj s
  have hmatchedCases :
      ((Finset.univ : Finset B).filter fun x => H.degree x = 1).card = 2 ∨
      ((Finset.univ : Finset B).filter fun x => H.degree x = 1).card = 4 := by
    rw [hmatchedEq]
    exact hstates.1
  obtain ⟨twoEdges, e, hflag, hedge⟩ :=
    exists_equiv_finFive_canonical_matching H hBcard hHdegree hmatchedCases
  refine ⟨twoEdges, e, ?_, ?_⟩
  · rcases hflag with hflag | hflag
    · exact Or.inl ⟨hflag.1, by rw [← hmatchedEq]; exact hflag.2⟩
    · exact Or.inr ⟨hflag.1, by rw [← hmatchedEq]; exact hflag.2⟩
  · intro x y
    simpa [H] using hedge x y

end

end Erdos85
