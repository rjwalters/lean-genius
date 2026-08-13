import Proofs.Erdos85PairedBlockRigidity
import Proofs.Erdos85OrderFortyNineOneHighOverlap

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

/-- Automorphisms of the standard four-pair matching can place every marked
endpoint at the even end of an initial mate pair.  The hypothesis says no
mate pair has two marked endpoints. -/
theorem finEight_standardMate_canonicalize_marked
    (marked : Fin 8 → Bool)
    (hpair : ∀ i, marked i = true →
      marked (oneHighStandardMate i) = false) :
    ∃ τ : Equiv.Perm (Fin 8),
      (∀ i, τ (oneHighStandardMate i) = oneHighStandardMate (τ i)) ∧
      ∀ i,
        marked (τ.symm i) =
          decide (i.val % 2 = 0 ∧
            i.val / 2 < (Finset.univ.filter fun j => marked j).card) := by
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

/-- A standard-mate labeling can additionally canonicalize any marking
having at most one marked endpoint per mate pair. -/
theorem exists_equiv_finEight_intertwining_involution_marked
    {P : Type*} [Fintype P] [DecidableEq P]
    (hcard : Fintype.card P = 8)
    (mate : P → P) (hinv : Function.Involutive mate)
    (hfix : ∀ x, mate x ≠ x)
    (marked : P → Bool)
    (hpair : ∀ x, marked x = true → marked (mate x) = false) :
    ∃ e : P ≃ Fin 8,
      (∀ x, e (mate x) = oneHighStandardMate (e x)) ∧
      ∀ i,
        marked (e.symm i) =
          decide (i.val % 2 = 0 ∧
            i.val / 2 < (Finset.univ.filter fun x => marked x).card) := by
  obtain ⟨e₀, he₀⟩ := exists_equiv_finEight_intertwining_involution
    hcard mate hinv hfix
  let marked₀ : Fin 8 → Bool := fun i => marked (e₀.symm i)
  have hpair₀ : ∀ i, marked₀ i = true →
      marked₀ (oneHighStandardMate i) = false := by
    intro i hi
    dsimp [marked₀] at hi ⊢
    have hm := hpair (e₀.symm i) hi
    have he := he₀ (e₀.symm i)
    rw [e₀.apply_symm_apply] at he
    rw [← he, e₀.symm_apply_apply]
    exact hm
  obtain ⟨τ, hτMate, hτMarked⟩ :=
    finEight_standardMate_canonicalize_marked marked₀ hpair₀
  refine ⟨e₀.trans τ, ?_, ?_⟩
  · intro x
    simp only [Equiv.trans_apply]
    rw [he₀]
    exact hτMate (e₀ x)
  · intro i
    have h := hτMarked i
    dsimp [marked₀] at h
    have hcardEq :
        ((Finset.univ : Finset (Fin 8)).filter fun j =>
          marked (e₀.symm j)).card =
          ((Finset.univ : Finset P).filter fun x => marked x).card := by
      apply Finset.card_bij (fun j _ => e₀.symm j)
      · intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hj).2⟩
      · intro j _ k _ hjk
        exact e₀.symm.injective hjk
      · intro x hx
        refine ⟨e₀ x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by simp⟩
        simpa using (Finset.mem_filter.mp hx).2
    simpa [hcardEq] using h

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

/-- Generator-facing branch ordering: all A pairs occur first, and their
one-edge endpoint is the even block.  B pairs follow.  Thus a graph with `a`
A pairs is labeled exactly as `AAAA`, `AAAB`, `AABB`, `ABBB`, or `BBBB`
according as `a = 4,3,2,1,0`. -/
theorem exists_oneHigh_branchLabeling_familyOrdered
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
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1) :
    ∃ e : {z : V // z ∈ G.neighborSet v} ≃ Fin 8,
      (∀ s, e (mate s) = oneHighStandardMate (e s)) ∧
      ∀ i,
        decide (highBranchMatchedCount G v (e.symm i) = 2) =
          decide (i.val % 2 = 0 ∧
            i.val / 2 < ((Finset.univ :
              Finset {z : V // z ∈ G.neighborSet v}).filter fun s =>
                highBranchMatchedCount G v s = 2).card) := by
  let P := {z : V // z ∈ G.neighborSet v}
  have hPcard : Fintype.card P = 8 := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet v) =
        G.neighborFinset v := by ext z; simp
    rw [heq, G.card_neighborFinset_eq_degree, hv]
  let marked : P → Bool := fun s =>
    decide (highBranchMatchedCount G v s = 2)
  have hfix : ∀ s, mate s ≠ s := by
    intro s h
    exact G.loopless.irrefl s.1 (congrArg Subtype.val h ▸ (hmateAdj s).symm)
  have hpair : ∀ s, marked s = true → marked (mate s) = false := by
    intro s hs
    have hs2 : highBranchMatchedCount G v s = 2 := by
      simpa [marked] using hs
    have hp := paired_highBranchMatchedCount_profile
      G hfree hmin hcard hv hunique hexternal houterDegree
        mate hmateInv hmateAdj s
    have hm4 : highBranchMatchedCount G v (mate s) = 4 := by
      rcases hp with hp | hp | hp
      · exact hp.2
      · omega
      · omega
    simp [marked, hm4]
  obtain ⟨e, heMate, heMarked⟩ :=
    exists_equiv_finEight_intertwining_involution_marked
      hPcard mate hmateInv hfix marked hpair
  refine ⟨e, heMate, ?_⟩
  intro i
  have h := heMarked i
  simpa [marked] using h

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

/-- Matched-coordinate predicate for the canonical Fin5 branch. -/
def oneHighCanonicalBranchMatched (twoEdges : Bool) (i : Fin 5) : Prop :=
  i.val < 2 ∨ (twoEdges = true ∧ i.val < 4)

instance oneHighCanonicalBranchMatched_decidable
    (twoEdges : Bool) (i : Fin 5) :
    Decidable (oneHighCanonicalBranchMatched twoEdges i) := by
  unfold oneHighCanonicalBranchMatched
  infer_instance

/-- Far-degree target used by the generator: matched leaf coordinates have
five far neighbors and the unique unmatched coordinate(s) have six. -/
def oneHighCanonicalFarDegree (twoEdges : Bool) (i : Fin 5) : Nat :=
  if oneHighCanonicalBranchMatched twoEdges i then 5 else 6

/-- Exact internal degree of every canonical Fin5 coordinate. -/
theorem card_filter_oneHighCanonicalBranchAdj
    (twoEdges : Bool) (i : Fin 5) :
    (Finset.univ.filter fun j =>
      oneHighCanonicalBranchAdj twoEdges i j).card =
        if oneHighCanonicalBranchMatched twoEdges i then 1 else 0 := by
  native_decide +revert

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

def oneHighSwapZeroOne : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 1

def oneHighSwapTwoThree : Equiv.Perm (Fin 5) :=
  Equiv.swap 2 3

def oneHighSwapMatchingEdges : Equiv.Perm (Fin 5) :=
  (Equiv.swap 0 2).trans (Equiv.swap 1 3)

theorem oneHighCanonicalBranchAdj_swapZeroOne
    (twoEdges : Bool) (i j : Fin 5) :
    oneHighCanonicalBranchAdj twoEdges (oneHighSwapZeroOne i)
        (oneHighSwapZeroOne j) =
      oneHighCanonicalBranchAdj twoEdges i j := by
  native_decide +revert

theorem oneHighCanonicalBranchAdj_swapTwoThree
    (twoEdges : Bool) (i j : Fin 5) :
    oneHighCanonicalBranchAdj twoEdges (oneHighSwapTwoThree i)
        (oneHighSwapTwoThree j) =
      oneHighCanonicalBranchAdj twoEdges i j := by
  native_decide +revert

theorem oneHighCanonicalBranchAdj_swapMatchingEdges
    (i j : Fin 5) :
    oneHighCanonicalBranchAdj true (oneHighSwapMatchingEdges i)
        (oneHighSwapMatchingEdges j) =
      oneHighCanonicalBranchAdj true i j := by
  native_decide +revert

theorem oneHighSwapZeroOne_symm : oneHighSwapZeroOne.symm = oneHighSwapZeroOne := by
  native_decide

theorem oneHighSwapTwoThree_symm :
    oneHighSwapTwoThree.symm = oneHighSwapTwoThree := by
  native_decide

theorem oneHighSwapMatchingEdges_symm :
    oneHighSwapMatchingEdges.symm = oneHighSwapMatchingEdges := by
  native_decide

@[simp] theorem oneHighSwapZeroOne_zero : oneHighSwapZeroOne 0 = 1 := by native_decide
@[simp] theorem oneHighSwapZeroOne_one : oneHighSwapZeroOne 1 = 0 := by native_decide
@[simp] theorem oneHighSwapTwoThree_two : oneHighSwapTwoThree 2 = 3 := by native_decide
@[simp] theorem oneHighSwapTwoThree_three : oneHighSwapTwoThree 3 = 2 := by native_decide
@[simp] theorem oneHighSwapMatchingEdges_zero :
    oneHighSwapMatchingEdges 0 = 2 := by native_decide
@[simp] theorem oneHighSwapMatchingEdges_one :
    oneHighSwapMatchingEdges 1 = 3 := by native_decide
@[simp] theorem oneHighSwapMatchingEdges_two :
    oneHighSwapMatchingEdges 2 = 0 := by native_decide
@[simp] theorem oneHighSwapMatchingEdges_three :
    oneHighSwapMatchingEdges 3 = 1 := by native_decide

/-- A canonical one- or two-edge matching can be relabeled so its matched
endpoints are ordered by any finite key; in the two-edge case the two edges
can also be ordered by their first endpoints. -/
theorem finFive_exists_canonical_lex_perm
    (twoEdges : Bool) (key : Fin 5 → Fin 8) :
    ∃ τ : Equiv.Perm (Fin 5),
      (∀ i j, oneHighCanonicalBranchAdj twoEdges (τ i) (τ j) =
        oneHighCanonicalBranchAdj twoEdges i j) ∧
      key (τ.symm 0) ≤ key (τ.symm 1) ∧
      (twoEdges = true →
        key (τ.symm 2) ≤ key (τ.symm 3) ∧
        key (τ.symm 0) ≤ key (τ.symm 2)) := by
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

/-- Canonical matching labels can simultaneously satisfy the generator's
lexicographic WLOG convention for any `Fin 8` key attached to the vertices. -/
theorem exists_equiv_finFive_canonical_matching_lex
    {P : Type*} [Fintype P] [DecidableEq P]
    (H : SimpleGraph P) [DecidableRel H.Adj]
    (hcard : Fintype.card P = 5)
    (hdegree : ∀ x : P, H.degree x ≤ 1)
    (hmatched : ((Finset.univ : Finset P).filter fun x =>
      H.degree x = 1).card = 2 ∨
      ((Finset.univ : Finset P).filter fun x => H.degree x = 1).card = 4)
    (key : P → Fin 8) :
    ∃ (twoEdges : Bool) (e : P ≃ Fin 5),
      ((twoEdges = false ∧
          ((Finset.univ : Finset P).filter fun x => H.degree x = 1).card = 2) ∨
        (twoEdges = true ∧
          ((Finset.univ : Finset P).filter fun x => H.degree x = 1).card = 4)) ∧
      (∀ x y, decide (H.Adj x y) =
        oneHighCanonicalBranchAdj twoEdges (e x) (e y)) ∧
      key (e.symm 0) ≤ key (e.symm 1) ∧
      (twoEdges = true →
        key (e.symm 2) ≤ key (e.symm 3) ∧
        key (e.symm 0) ≤ key (e.symm 2)) := by
  obtain ⟨twoEdges, e, hflag, hedge⟩ :=
    exists_equiv_finFive_canonical_matching H hcard hdegree hmatched
  obtain ⟨τ, hτAdj, hτ01, hτrest⟩ :=
    finFive_exists_canonical_lex_perm twoEdges (fun i => key (e.symm i))
  refine ⟨twoEdges, e.trans τ, hflag, ?_, ?_, ?_⟩
  · intro x y
    rw [hedge]
    exact (hτAdj (e x) (e y)).symm
  · simpa using hτ01
  · intro htrue
    have hr := hτrest htrue
    simpa using hr

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

/-- Transporting a canonical Fin5 labeling gives the exact internal degree
of every original branch vertex. -/
theorem card_neighbor_inter_branch_eq_canonicalMatched
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    (s : {z : V // z ∈ G.neighborSet v})
    (twoEdges : Bool) (e : secondLayerBranch G v s ≃ Fin 5)
    (hcanonical : ∀ x y, decide (G.Adj x.1 y.1) =
      oneHighCanonicalBranchAdj twoEdges (e x) (e y))
    (x : secondLayerBranch G v s) :
    (G.neighborFinset x.1 ∩ secondLayerBranch G v s).card =
      if oneHighCanonicalBranchMatched twoEdges (e x) then 1 else 0 := by
  classical
  rw [← card_filter_oneHighCanonicalBranchAdj twoEdges (e x)]
  apply Finset.card_bij (fun y hy => e ⟨y, (Finset.mem_inter.mp hy).2⟩)
  · intro y hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hadj := (G.mem_neighborFinset x.1 y).mp
      (Finset.mem_inter.mp hy).1
    have hc := hcanonical x ⟨y, (Finset.mem_inter.mp hy).2⟩
    rw [← hc]
    exact decide_eq_true hadj
  · intro y hy z hz heq
    exact congrArg Subtype.val (e.injective heq)
  · intro j hj
    have hc := hcanonical x (e.symm j)
    have hcanon : oneHighCanonicalBranchAdj twoEdges (e x) j = true := by
      simpa using (Finset.mem_filter.mp hj).2
    have hadj : G.Adj x.1 (e.symm j).1 := by
      apply of_decide_eq_true
      rw [hc, e.apply_symm_apply]
      exact hcanon
    refine ⟨(e.symm j).1, Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset _ _).mpr hadj, (e.symm j).2⟩, ?_⟩
    exact e.apply_symm_apply j

/-- Key-sorted version of the branch labeling.  This is the exact finite
WLOG operation used by the generator's matched-pair lex clauses. -/
theorem exists_oneHigh_branchVertexLabeling_lex
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
    (s : {z : V // z ∈ G.neighborSet v})
    (key : secondLayerBranch G v s → Fin 8) :
    ∃ (twoEdges : Bool)
      (e : secondLayerBranch G v s ≃ Fin 5),
      ((twoEdges = false ∧ highBranchMatchedCount G v s = 2) ∨
        (twoEdges = true ∧ highBranchMatchedCount G v s = 4)) ∧
      (∀ x y, decide (G.Adj x.1 y.1) =
        oneHighCanonicalBranchAdj twoEdges (e x) (e y)) ∧
      key (e.symm 0) ≤ key (e.symm 1) ∧
      (twoEdges = true →
        key (e.symm 2) ≤ key (e.symm 3) ∧
        key (e.symm 0) ≤ key (e.symm 2)) := by
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
      exact Finset.mem_filter.mpr ⟨x.2, by
        rw [← degree_induce_secondLayerBranch_eq_card_inter]
        simpa [B, H] using (Finset.mem_filter.mp hx).2⟩
    · intro x _ y _ hxy
      exact Subtype.ext hxy
    · intro x hx
      refine ⟨⟨x, (Finset.mem_filter.mp hx).1⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rw [degree_induce_secondLayerBranch_eq_card_inter]
        exact (Finset.mem_filter.mp hx).2⟩
  have hstates := paired_highBranchMatchedCount_states
    G hfree hmin hcard hv hunique hexternal houterDegree
      mate hmateInv hmateAdj s
  have hcases :
      ((Finset.univ : Finset B).filter fun x => H.degree x = 1).card = 2 ∨
      ((Finset.univ : Finset B).filter fun x => H.degree x = 1).card = 4 := by
    rw [hmatchedEq]
    exact hstates.1
  obtain ⟨twoEdges, e, hflag, hedge, h01, hrest⟩ :=
    exists_equiv_finFive_canonical_matching_lex
      H hBcard hHdegree hcases key
  refine ⟨twoEdges, e, ?_, ?_, h01, hrest⟩
  · rcases hflag with hflag | hflag
    · exact Or.inl ⟨hflag.1, by rw [← hmatchedEq]; exact hflag.2⟩
    · exact Or.inr ⟨hflag.1, by rw [← hmatchedEq]; exact hflag.2⟩
  · intro x y
    simpa [H] using hedge x y

/-- Far root blocks missed by a leaf.  For an internally matched leaf this
set is a singleton by pointwise dirty conservation. -/
def oneHighFarMissBranches
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (s : {z : V // z ∈ G.neighborSet v}) (x : V) :
    Finset {z : V // z ∈ G.neighborSet v} :=
  ((Finset.univ.erase s).erase (mate s)).filter fun u =>
    (G.neighborFinset x ∩ secondLayerBranch G v u).card = 0

noncomputable def oneHighMissingBranch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (s : {z : V // z ∈ G.neighborSet v}) (x : V) :
    {z : V // z ∈ G.neighborSet v} :=
  if h : (oneHighFarMissBranches G v mate s x).Nonempty then h.choose else s

theorem card_oneHighFarMissBranches_eq_one_of_matched
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1)
    (s : {z : V // z ∈ G.neighborSet v})
    (x : V) (hx : x ∈ secondLayerBranch G v s)
    (hxMatched : (G.neighborFinset x ∩
      secondLayerBranch G v s).card = 1) :
    (oneHighFarMissBranches G v mate s x).card = 1 := by
  have hxSecond : x ∈ secondLayer G v := by
    rw [secondLayer]
    exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, hx⟩
  have h := card_farBranch_misses_eq_internalDegree
    G hfree (d := 7) (by omega) hexternal s (mate s)
      (hmateAdj s) x hx (houterDegree hxSecond)
  simpa [oneHighFarMissBranches, hxMatched] using h

theorem oneHighMissingBranch_mem_of_matched
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1)
    (s : {z : V // z ∈ G.neighborSet v})
    (x : V) (hx : x ∈ secondLayerBranch G v s)
    (hxMatched : (G.neighborFinset x ∩
      secondLayerBranch G v s).card = 1) :
    oneHighMissingBranch G v mate s x ∈
      oneHighFarMissBranches G v mate s x := by
  have hc := card_oneHighFarMissBranches_eq_one_of_matched
    G hfree hv hexternal houterDegree mate hmateAdj s x hx hxMatched
  have hn : (oneHighFarMissBranches G v mate s x).Nonempty :=
    Finset.card_pos.mp (by omega)
  rw [oneHighMissingBranch, dif_pos hn]
  exact hn.choose_spec

theorem eq_oneHighMissingBranch_of_matched_of_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1)
    (s : {z : V // z ∈ G.neighborSet v})
    (x : V) (hx : x ∈ secondLayerBranch G v s)
    (hxMatched : (G.neighborFinset x ∩
      secondLayerBranch G v s).card = 1)
    (u : {z : V // z ∈ G.neighborSet v})
    (hu : u ∈ oneHighFarMissBranches G v mate s x) :
    u = oneHighMissingBranch G v mate s x := by
  have hc := card_oneHighFarMissBranches_eq_one_of_matched
    G hfree hv hexternal houterDegree mate hmateAdj s x hx hxMatched
  have hm := oneHighMissingBranch_mem_of_matched
    G hfree hv hexternal houterDegree mate hmateAdj s x hx hxMatched
  have hle : (oneHighFarMissBranches G v mate s x).card ≤ 1 := by omega
  exact Finset.card_le_one.mp hle u hu
    (oneHighMissingBranch G v mate s x) hm

/-- Generator-facing canonical branch labels.  The matched endpoints are
oriented by their unique missed far-block labels, and a two-edge branch has
its two edges ordered by the first endpoint labels.  These are precisely the
three families of matched-pair lex clauses in `family_gen.py`. -/
theorem exists_oneHigh_branchVertexLabeling_generatorLex
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
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (s : {z : V // z ∈ G.neighborSet v}) :
    ∃ (twoEdges : Bool)
      (e : secondLayerBranch G v s ≃ Fin 5),
      ((twoEdges = false ∧ highBranchMatchedCount G v s = 2) ∨
        (twoEdges = true ∧ highBranchMatchedCount G v s = 4)) ∧
      (∀ x y, decide (G.Adj x.1 y.1) =
        oneHighCanonicalBranchAdj twoEdges (e x) (e y)) ∧
      branchLabel (oneHighMissingBranch G v mate s (e.symm 0).1) ≤
        branchLabel (oneHighMissingBranch G v mate s (e.symm 1).1) ∧
      (twoEdges = true →
        branchLabel (oneHighMissingBranch G v mate s (e.symm 2).1) ≤
          branchLabel (oneHighMissingBranch G v mate s (e.symm 3).1) ∧
        branchLabel (oneHighMissingBranch G v mate s (e.symm 0).1) ≤
          branchLabel (oneHighMissingBranch G v mate s (e.symm 2).1)) := by
  exact exists_oneHigh_branchVertexLabeling_lex
    G hfree hmin hcard hv hunique hexternal houterDegree
      mate hmateInv hmateAdj s
      (fun x => branchLabel (oneHighMissingBranch G v mate s x.1))

/-! ## Assembly into the encoder's forty leaf coordinates -/

/-- Every second-layer leaf has a chosen branch owner. -/
noncomputable def oneHighBranchOwner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (x : {z : V // z ∈ secondLayer G v}) :
    {z : V // z ∈ G.neighborSet v} := by
  classical
  have hx := x.2
  change x.1 ∈ Finset.univ.biUnion (secondLayerBranch G v) at hx
  exact (Finset.mem_biUnion.mp hx).choose

theorem oneHighBranchOwner_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (x : {z : V // z ∈ secondLayer G v}) :
    x.1 ∈ secondLayerBranch G v (oneHighBranchOwner G v x) := by
  classical
  have hx := x.2
  change x.1 ∈ Finset.univ.biUnion (secondLayerBranch G v) at hx
  exact (Finset.mem_biUnion.mp hx).choose_spec.2

theorem oneHighBranchOwner_eq_of_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (v : V)
    (x : {z : V // z ∈ secondLayer G v})
    (s : {z : V // z ∈ G.neighborSet v})
    (hx : x.1 ∈ secondLayerBranch G v s) :
    oneHighBranchOwner G v x = s := by
  classical
  by_contra hne
  have hdisj := secondLayerBranch_pairwiseDisjoint G hfree v
    (Finset.mem_univ _) (Finset.mem_univ _) hne
  exact (Finset.disjoint_left.mp hdisj)
    (oneHighBranchOwner_mem G v x) hx

/-- The second layer is canonically a sigma-type of its eight branches. -/
noncomputable def oneHighLeafSigmaEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (v : V) :
    {z : V // z ∈ secondLayer G v} ≃
      Σ s : {z : V // z ∈ G.neighborSet v}, secondLayerBranch G v s :=
  Equiv.ofBijective
    (fun x => ⟨oneHighBranchOwner G v x,
      ⟨x.1, oneHighBranchOwner_mem G v x⟩⟩)
    ⟨by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z => z.2.1) hxy,
    by
      intro p
      have hpSecond : p.2.1 ∈ secondLayer G v := by
        change p.2.1 ∈ Finset.univ.biUnion (secondLayerBranch G v)
        exact Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_univ _, p.2.2⟩
      let x : {z : V // z ∈ secondLayer G v} := ⟨p.2.1, hpSecond⟩
      refine ⟨x, ?_⟩
      have howner := oneHighBranchOwner_eq_of_mem G hfree v x p.1 p.2.2
      apply Sigma.ext howner
      apply (Subtype.heq_iff_coe_eq (by
        intro z
        change z ∈ secondLayerBranch G v (oneHighBranchOwner G v x) ↔
          z ∈ secondLayerBranch G v p.1
        rw [howner])).2
      rfl⟩

/-- Assemble a branch label and one five-point label per branch into the
row-major `Fin 40` numbering used by the family CNFs. -/
noncomputable def oneHighLeafFinFortyEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (v : V)
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5) :
    {z : V // z ∈ secondLayer G v} ≃ Fin 40 :=
  (oneHighLeafSigmaEquiv G hfree v).trans <|
    (Equiv.sigmaCongrRight leafLabel).trans <|
      (Equiv.sigmaEquivProd _ _).trans <|
        (Equiv.prodCongr branchLabel (Equiv.refl _)).trans <|
          finProdFinEquiv

theorem oneHighLeafFinFortyEquiv_divNat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (v : V)
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (x : {z : V // z ∈ secondLayer G v}) :
    Fin.divNat (m := 8) (n := 5)
      (oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel x) =
      branchLabel (oneHighBranchOwner G v x) := by
  simp only [oneHighLeafFinFortyEquiv, oneHighLeafSigmaEquiv,
    Equiv.trans_apply, Equiv.ofBijective_apply, Equiv.sigmaCongrRight_apply,
    Equiv.sigmaEquivProd_apply, Equiv.prodCongr_apply]
  exact congrArg Prod.fst
    ((finProdFinEquiv : Fin 8 × Fin 5 ≃ Fin 40).symm_apply_apply
      (branchLabel (oneHighBranchOwner G v x),
        leafLabel (oneHighBranchOwner G v x)
          ⟨x.1, oneHighBranchOwner_mem G v x⟩))

theorem oneHighLeafFinFortyEquiv_modNat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (v : V)
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (x : {z : V // z ∈ secondLayer G v}) :
    Fin.modNat (m := 8) (n := 5)
      (oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel x) =
      leafLabel (oneHighBranchOwner G v x)
        ⟨x.1, oneHighBranchOwner_mem G v x⟩ := by
  simp only [oneHighLeafFinFortyEquiv, oneHighLeafSigmaEquiv,
    Equiv.trans_apply, Equiv.ofBijective_apply, Equiv.sigmaCongrRight_apply,
    Equiv.sigmaEquivProd_apply, Equiv.prodCongr_apply]
  exact congrArg Prod.snd
    ((finProdFinEquiv : Fin 8 × Fin 5 ≃ Fin 40).symm_apply_apply
      (branchLabel (oneHighBranchOwner G v x),
        leafLabel (oneHighBranchOwner G v x)
          ⟨x.1, oneHighBranchOwner_mem G v x⟩))

/-! ## The relabeled forty-leaf graph -/

def oneHighRelabeledLeafGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (E : {z : V // z ∈ secondLayer G v} ≃ Fin 40) :
    SimpleGraph (Fin 40) :=
  SimpleGraph.comap E.symm (squareOrderOuterGraph G v)

instance oneHighRelabeledLeafGraph_decidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (E : {z : V // z ∈ secondLayer G v} ≃ Fin 40) :
    DecidableRel (oneHighRelabeledLeafGraph G v E).Adj :=
  fun i j => inferInstanceAs
    (Decidable ((squareOrderOuterGraph G v).Adj (E.symm i) (E.symm j)))

theorem oneHighRelabeledLeafGraph_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (E : {z : V // z ∈ secondLayer G v} ≃ Fin 40)
    (i j : Fin 40) :
    (oneHighRelabeledLeafGraph G v E).Adj i j ↔
      G.Adj (E.symm i).1 (E.symm j).1 := by
  rfl

/-- Relabeling preserves the number of common leaf neighbors. -/
theorem oneHighRelabeledLeafGraph_common_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (E : {z : V // z ∈ secondLayer G v} ≃ Fin 40)
    (i j : Fin 40) :
    ((oneHighRelabeledLeafGraph G v E).neighborFinset i ∩
      (oneHighRelabeledLeafGraph G v E).neighborFinset j).card =
    ((squareOrderOuterGraph G v).neighborFinset (E.symm i) ∩
      (squareOrderOuterGraph G v).neighborFinset (E.symm j)).card := by
  classical
  let R := oneHighRelabeledLeafGraph G v E
  let S := squareOrderOuterGraph G v
  apply Finset.card_bij (fun k _ => E.symm k)
  · intro k hk
    have hp := Finset.mem_inter.mp hk
    exact Finset.mem_inter.mpr ⟨
      (S.mem_neighborFinset _ _).mpr
        ((oneHighRelabeledLeafGraph_adj G v E i k).mp
          ((R.mem_neighborFinset _ _).mp hp.1)),
      (S.mem_neighborFinset _ _).mpr
        ((oneHighRelabeledLeafGraph_adj G v E j k).mp
          ((R.mem_neighborFinset _ _).mp hp.2))⟩
  · intro k _ l _ hkl
    exact E.symm.injective hkl
  · intro x hx
    have hp := Finset.mem_inter.mp hx
    have hix := (S.mem_neighborFinset _ _).mp hp.1
    have hjx := (S.mem_neighborFinset _ _).mp hp.2
    change G.Adj (E.symm i).1 x.1 at hix
    change G.Adj (E.symm j).1 x.1 at hjx
    refine ⟨E x, ?_, E.symm_apply_apply x⟩
    exact Finset.mem_inter.mpr ⟨
      (R.mem_neighborFinset _ _).mpr
        ((oneHighRelabeledLeafGraph_adj G v E i (E x)).mpr
          (by simpa using hix)),
      (R.mem_neighborFinset _ _).mpr
        ((oneHighRelabeledLeafGraph_adj G v E j (E x)).mpr
          (by simpa using hjx))⟩

theorem oneHighRelabeledLeafGraph_not_containsC4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    (hfree : ¬ containsC4 V G)
    (E : {z : V // z ∈ secondLayer G v} ≃ Fin 40) :
    ¬ containsC4 (Fin 40) (oneHighRelabeledLeafGraph G v E) := by
  exact fun h => (squareOrderOuterGraph_not_containsC4 G hfree)
    ((containsC4_iff_of_iso
      (SimpleGraph.Iso.comap E.symm (squareOrderOuterGraph G v))).mp h)

/-- Every canonical forty-leaf relabeling is six-regular, matching the
degree equations emitted by `family_gen.py`. -/
theorem oneHighRelabeledLeafGraph_degree_eq_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (hunique : ∀ {x : V}, G.degree x = 8 → x = v)
    (E : {z : V // z ∈ secondLayer G v} ≃ Fin 40)
    (i : Fin 40) :
    (oneHighRelabeledLeafGraph G v E).degree i = 6 := by
  have hneigh : ∀ y, G.Adj v y → G.degree y = 7 := by
    intro y hyv
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin hcard y with hy7 | hy8
    · exact hy7
    · have hyv' : y = v := hunique hy8
      subst y
      exact (G.loopless.irrefl v hyv).elim
  have hlocal : ∀ s : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree s = 1 :=
    orderFortyNine_localNeighborhood_degree_eq_one_of_degreeEight
      G hfree hmin hcard hv
  have houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7 := by
    intro a ha
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin hcard a with ha7 | ha8
    · exact ha7
    · have hav : a = v := hunique ha8
      change a ∈ Finset.univ.biUnion (secondLayerBranch G v) at ha
      rcases Finset.mem_biUnion.mp ha with ⟨s, _, has⟩
      exact ((Finset.mem_sdiff.mp has).2 (by simp [hav])).elim
  rw [show (oneHighRelabeledLeafGraph G v E).degree i =
      (squareOrderOuterGraph G v).degree (E.symm i) by
    exact (SimpleGraph.Iso.comap E.symm
      (squareOrderOuterGraph G v)).degree_eq i |>.symm]
  exact squareOrderOuterGraph_regular
    G hfree (d := 7) (by norm_num) hcard hv hneigh hlocal houterDegree
      (E.symm i)

/-- Under the assembled coordinates, paired blocks have no cross edges. -/
theorem oneHighRelabeledLeafGraph_not_adj_of_standardMate_blocks
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1)
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (hbranchMate : ∀ s,
      branchLabel (mate s) = oneHighStandardMate (branchLabel s))
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (i j : Fin 40)
    (hij : Fin.divNat (m := 8) (n := 5) j =
      oneHighStandardMate (Fin.divNat (m := 8) (n := 5) i)) :
    ¬(oneHighRelabeledLeafGraph G v
      (oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel)).Adj i j := by
  let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
  let x := E.symm i
  let y := E.symm j
  have hxCoord := oneHighLeafFinFortyEquiv_divNat
    G hfree v branchLabel leafLabel x
  have hyCoord := oneHighLeafFinFortyEquiv_divNat
    G hfree v branchLabel leafLabel y
  rw [E.apply_symm_apply] at hxCoord hyCoord
  have howner : oneHighBranchOwner G v y = mate (oneHighBranchOwner G v x) := by
    apply branchLabel.injective
    rw [hbranchMate, ← hxCoord, ← hyCoord]
    exact hij
  intro hadj
  apply not_adj_between_secondLayerBranches_of_adj_roots
    G hfree v (oneHighBranchOwner G v x) (oneHighBranchOwner G v y)
      (howner ▸ hmateAdj (oneHighBranchOwner G v x))
      ⟨x.1, oneHighBranchOwner_mem G v x⟩
      ⟨y.1, oneHighBranchOwner_mem G v y⟩
  exact (oneHighRelabeledLeafGraph_adj G v E i j).mp hadj

/-- The relabeled leaf graph has at most one common neighbor for every two
distinct vertices.  This is the semantic content of the generator's general
cross-block C4 clauses. -/
theorem oneHighRelabeledLeafGraph_common_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    (hfree : ¬ containsC4 V G)
    (E : {z : V // z ∈ secondLayer G v} ≃ Fin 40)
    (i j : Fin 40) (hij : i ≠ j) :
    ((oneHighRelabeledLeafGraph G v E).neighborFinset i ∩
      (oneHighRelabeledLeafGraph G v E).neighborFinset j).card ≤ 1 := by
  exact common_le_one_of_not_containsC4
    (oneHighRelabeledLeafGraph_not_containsC4 G hfree E) i j hij

/-- Distinct vertices in one encoded block have no common leaf neighbor.
They already share their branch center in the original graph, so any common
leaf would create a C4. -/
theorem oneHighRelabeledLeafGraph_sameBlock_common_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (i j : Fin 40) (hij : i ≠ j)
    (hblock : Fin.divNat (m := 8) (n := 5) i =
      Fin.divNat (m := 8) (n := 5) j) :
    ((oneHighRelabeledLeafGraph G v
        (oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel)).neighborFinset i ∩
      (oneHighRelabeledLeafGraph G v
        (oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel)).neighborFinset j).card = 0 := by
  classical
  let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
  let R := oneHighRelabeledLeafGraph G v E
  let x := E.symm i
  let y := E.symm j
  have hxCoord := oneHighLeafFinFortyEquiv_divNat
    G hfree v branchLabel leafLabel x
  have hyCoord := oneHighLeafFinFortyEquiv_divNat
    G hfree v branchLabel leafLabel y
  rw [E.apply_symm_apply] at hxCoord hyCoord
  have howner : oneHighBranchOwner G v x = oneHighBranchOwner G v y := by
    apply branchLabel.injective
    rw [← hxCoord, ← hyCoord]
    exact hblock
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  let z := E.symm k
  have hkAdjX : G.Adj z.1 x.1 := by
    have := (Finset.mem_inter.mp hk).1
    exact ((oneHighRelabeledLeafGraph_adj G v E i k).mp
      ((R.mem_neighborFinset i k).mp this)).symm
  have hkAdjY : G.Adj z.1 y.1 := by
    have := (Finset.mem_inter.mp hk).2
    exact ((oneHighRelabeledLeafGraph_adj G v E j k).mp
      ((R.mem_neighborFinset j k).mp this)).symm
  have hxy : x.1 ≠ y.1 := by
    intro h
    apply hij
    apply E.symm.injective
    exact Subtype.ext h
  have hzOwner : z.1 ≠ (oneHighBranchOwner G v x).1 := by
    intro h
    have hzSecond := z.2
    change z.1 ∈ Finset.univ.biUnion (secondLayerBranch G v) at hzSecond
    rcases Finset.mem_biUnion.mp hzSecond with ⟨u, _, hzu⟩
    exact (Finset.mem_sdiff.mp hzu).2 (by
      simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
      exact Or.inr (h ▸ (oneHighBranchOwner G v x).2))
  have hOwnerX : G.Adj (oneHighBranchOwner G v x).1 x.1 := by
    exact (G.mem_neighborFinset _ _).mp
      (Finset.mem_sdiff.mp (oneHighBranchOwner_mem G v x)).1
  have hOwnerY : G.Adj (oneHighBranchOwner G v x).1 y.1 := by
    rw [howner]
    exact (G.mem_neighborFinset _ _).mp
      (Finset.mem_sdiff.mp (oneHighBranchOwner_mem G v y)).1
  exact hfree (containsC4_of_two_common hxy hzOwner
    hkAdjX hkAdjY hOwnerX hOwnerY)

/-- Consequently any vertex has at most one neighbor in a specified encoded
block.  This is the literal-level form of `family_gen.py`'s foreign-block
at-most-one clauses. -/
theorem oneHighRelabeledLeafGraph_not_adj_two_in_sameBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (i k l : Fin 40) (hkl : k ≠ l)
    (hblock : Fin.divNat (m := 8) (n := 5) k =
      Fin.divNat (m := 8) (n := 5) l) :
    ¬((oneHighRelabeledLeafGraph G v
        (oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel)).Adj i k ∧
      (oneHighRelabeledLeafGraph G v
        (oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel)).Adj i l) := by
  intro hadj
  let R := oneHighRelabeledLeafGraph G v
    (oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel)
  have hzero := oneHighRelabeledLeafGraph_sameBlock_common_eq_zero
    G hfree branchLabel leafLabel k l hkl hblock
  have hiMem : i ∈ R.neighborFinset k ∩ R.neighborFinset l := by
    exact Finset.mem_inter.mpr ⟨
      (R.mem_neighborFinset k i).mpr hadj.1.symm,
      (R.mem_neighborFinset l i).mpr hadj.2.symm⟩
  have hempty : R.neighborFinset k ∩ R.neighborFinset l = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [R] using hzero
  rw [hempty] at hiMem
  exact Finset.notMem_empty i hiMem

/-- Union of the six branches other than `s` and its mate. -/
def oneHighFarBranchVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (s : {z : V // z ∈ G.neighborSet v}) : Finset V :=
  ((Finset.univ.erase s).erase (mate s)).biUnion
    (secondLayerBranch G v)

/-- Exact far-degree decomposition behind `degfar` in `family_gen.py`. -/
theorem card_neighbor_inter_oneHighFarBranchVertices_add_internal_eq_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hexternal : externalRepairCandidates G v = ∅)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1)
    (s : {z : V // z ∈ G.neighborSet v})
    (x : V) (hx : x ∈ secondLayerBranch G v s)
    (hxDegree : G.degree x = 7) :
    (G.neighborFinset x ∩ oneHighFarBranchVertices G v mate s).card +
      (G.neighborFinset x ∩ secondLayerBranch G v s).card = 6 := by
  classical
  let P := {z : V // z ∈ G.neighborSet v}
  let U : Finset P := (Finset.univ.erase s).erase (mate s)
  let f : P → ℕ := fun u =>
    (G.neighborFinset x ∩ secondLayerBranch G v u).card
  have hmateNe : s ≠ mate s := by
    intro h
    exact G.loopless.irrefl s.1 (congrArg Subtype.val h ▸ hmateAdj s)
  have hsumAll : ∑ u : P, f u = 6 := by
    have h := sum_card_neighbors_inter_highBranches_eq_degree_sub_one
      G hfree hexternal s x hx hxDegree
    simpa [P, f] using h
  have hmateZero : f (mate s) = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    exact not_adj_between_secondLayerBranches_of_adj_roots
      G hfree v s (mate s) (hmateAdj s)
        ⟨x, hx⟩ ⟨q, (Finset.mem_inter.mp hq).2⟩
        ((G.mem_neighborFinset x q).mp (Finset.mem_inter.mp hq).1)
  have hmateMem : mate s ∈ (Finset.univ : Finset P).erase s := by
    simp [hmateNe.symm]
  have hsMem : s ∈ (Finset.univ : Finset P) := Finset.mem_univ s
  have hmateErase := Finset.sum_erase_add
    ((Finset.univ : Finset P).erase s) f hmateMem
  have hsErase := Finset.sum_erase_add (Finset.univ : Finset P) f hsMem
  have hUsum : (∑ u ∈ U, f u) + f s = 6 := by
    dsimp [U]
    dsimp [P, f] at hsumAll hmateZero hmateErase hsErase ⊢
    omega
  have hbranchDisj := secondLayerBranch_pairwiseDisjoint G hfree v
  have hinterDisj : (↑U : Set P).PairwiseDisjoint (fun u =>
      G.neighborFinset x ∩ secondLayerBranch G v u) := by
    intro u _ w _ huw
    change Disjoint
      (G.neighborFinset x ∩ secondLayerBranch G v u)
      (G.neighborFinset x ∩ secondLayerBranch G v w)
    rw [Finset.disjoint_left]
    intro q hqu hqw
    exact (Finset.disjoint_left.mp
      (hbranchDisj (by simp) (by simp) huw))
        (Finset.mem_inter.mp hqu).2 (Finset.mem_inter.mp hqw).2
  have hinter : G.neighborFinset x ∩ oneHighFarBranchVertices G v mate s =
      U.biUnion fun u => G.neighborFinset x ∩ secondLayerBranch G v u := by
    ext q
    constructor
    · intro hq
      have hqi := Finset.mem_inter.mp hq
      rw [oneHighFarBranchVertices] at hqi
      rcases Finset.mem_biUnion.mp hqi.2 with ⟨u, hu, hqu⟩
      exact Finset.mem_biUnion.mpr ⟨u, hu,
        Finset.mem_inter.mpr ⟨hqi.1, hqu⟩⟩
    · intro hq
      rcases Finset.mem_biUnion.mp hq with ⟨u, hu, hqu⟩
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hqu).1, by
        rw [oneHighFarBranchVertices]
        exact Finset.mem_biUnion.mpr
          ⟨u, hu, (Finset.mem_inter.mp hqu).2⟩⟩
  rw [hinter, Finset.card_biUnion hinterDisj]
  exact hUsum

/-- The exact far-neighbor filter used by the encoded degree equations. -/
def oneHighEncodedFarNeighbors
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj] (i : Fin 40) :
    Finset (Fin 40) :=
  Finset.univ.filter fun k => R.Adj i k ∧
    Fin.divNat (m := 8) (n := 5) k ≠ Fin.divNat (m := 8) (n := 5) i ∧
    Fin.divNat (m := 8) (n := 5) k ≠
      oneHighStandardMate (Fin.divNat (m := 8) (n := 5) i)

/-- Encoded far neighbors are in cardinality-preserving bijection with the
original neighbors in the six far branches. -/
theorem card_oneHighEncodedFarNeighbors_eq_original
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (hbranchMate : ∀ s,
      branchLabel (mate s) = oneHighStandardMate (branchLabel s))
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (i : Fin 40) :
    let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
    let R := oneHighRelabeledLeafGraph G v E
    (oneHighEncodedFarNeighbors R i).card =
      (G.neighborFinset (E.symm i).1 ∩
        oneHighFarBranchVertices G v mate
          (oneHighBranchOwner G v (E.symm i))).card := by
  classical
  let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
  let R := oneHighRelabeledLeafGraph G v E
  let x := E.symm i
  let s := oneHighBranchOwner G v x
  have hxCoord := oneHighLeafFinFortyEquiv_divNat
    G hfree v branchLabel leafLabel x
  rw [E.apply_symm_apply] at hxCoord
  apply Finset.card_bij (fun k _ => (E.symm k).1)
  · intro k hk
    have hkp := Finset.mem_filter.mp hk
    let y := E.symm k
    have hyCoord := oneHighLeafFinFortyEquiv_divNat
      G hfree v branchLabel leafLabel y
    rw [E.apply_symm_apply] at hyCoord
    have hyOwn : oneHighBranchOwner G v y ≠ s := by
      intro h
      apply hkp.2.2.1
      rw [hyCoord, hxCoord, h]
    have hyMate : oneHighBranchOwner G v y ≠ mate s := by
      intro h
      apply hkp.2.2.2
      rw [hyCoord, hxCoord, h, hbranchMate]
    apply Finset.mem_inter.mpr
    constructor
    · exact (G.mem_neighborFinset _ _).mpr
        ((oneHighRelabeledLeafGraph_adj G v E i k).mp hkp.2.1)
    · rw [oneHighFarBranchVertices]
      apply Finset.mem_biUnion.mpr
      refine ⟨oneHighBranchOwner G v y, ?_,
        oneHighBranchOwner_mem G v y⟩
      exact Finset.mem_erase.mpr
        ⟨hyMate, Finset.mem_erase.mpr ⟨hyOwn, Finset.mem_univ _⟩⟩
  · intro k _ l _ hkl
    apply E.symm.injective
    exact Subtype.ext hkl
  · intro q hq
    have hqAdj := (Finset.mem_inter.mp hq).1
    have hqFar := (Finset.mem_inter.mp hq).2
    rw [oneHighFarBranchVertices] at hqFar
    rcases Finset.mem_biUnion.mp hqFar with ⟨u, hu, hqu⟩
    have hqSecond : q ∈ secondLayer G v := by
      change q ∈ Finset.univ.biUnion (secondLayerBranch G v)
      exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, hqu⟩
    let y : {z : V // z ∈ secondLayer G v} := ⟨q, hqSecond⟩
    have hyOwner : oneHighBranchOwner G v y = u :=
      oneHighBranchOwner_eq_of_mem G hfree v y u hqu
    have hyCoord := oneHighLeafFinFortyEquiv_divNat
      G hfree v branchLabel leafLabel y
    have huRaw : u ≠ mate s ∧ u ≠ s := by
      simpa only [Finset.mem_erase, Finset.mem_univ, true_and, and_true]
        using hu
    refine ⟨E y, ?_, by simp [y]⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (oneHighRelabeledLeafGraph_adj G v E i (E y)).mpr (by
        simpa [x, y] using (G.mem_neighborFinset _ _).mp hqAdj)
    · rw [hyCoord, hxCoord, hyOwner]
      exact fun h => huRaw.2 (branchLabel.injective h)
    · rw [hyCoord, hxCoord, hyOwner, ← hbranchMate]
      exact fun h => huRaw.1 (branchLabel.injective h)

/-- The encoded `degfar` equation: far degree plus degree inside the vertex's
own five-point block is exactly six. -/
theorem card_oneHighEncodedFarNeighbors_add_internal_eq_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hexternal : externalRepairCandidates G v = ∅)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1)
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (hbranchMate : ∀ s,
      branchLabel (mate s) = oneHighStandardMate (branchLabel s))
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (i : Fin 40)
    (hiDegree : G.degree
      ((oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel).symm i).1 = 7) :
    let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
    let R := oneHighRelabeledLeafGraph G v E
    (oneHighEncodedFarNeighbors R i).card +
      (G.neighborFinset (E.symm i).1 ∩
        secondLayerBranch G v (oneHighBranchOwner G v (E.symm i))).card = 6 := by
  classical
  let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
  let x := E.symm i
  let s := oneHighBranchOwner G v x
  have hx : x.1 ∈ secondLayerBranch G v s :=
    oneHighBranchOwner_mem G v x
  dsimp only
  rw [card_oneHighEncodedFarNeighbors_eq_original
    G hfree mate branchLabel hbranchMate leafLabel i]
  exact card_neighbor_inter_oneHighFarBranchVertices_add_internal_eq_six
    G hfree hexternal mate hmateAdj s x.1 hx hiDegree

/-- Exact encoded far degree after a branch's canonical Fin5 labeling. -/
theorem card_oneHighEncodedFarNeighbors_eq_canonicalFarDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hexternal : externalRepairCandidates G v = ∅)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1)
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (hbranchMate : ∀ s,
      branchLabel (mate s) = oneHighStandardMate (branchLabel s))
    (twoEdges : {z : V // z ∈ G.neighborSet v} → Bool)
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (hcanonical : ∀ s x y, decide (G.Adj x.1 y.1) =
      oneHighCanonicalBranchAdj (twoEdges s)
        (leafLabel s x) (leafLabel s y))
    (i : Fin 40)
    (hiDegree : G.degree
      ((oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel).symm i).1 = 7) :
    let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
    let R := oneHighRelabeledLeafGraph G v E
    let x := E.symm i
    let s := oneHighBranchOwner G v x
    (oneHighEncodedFarNeighbors R i).card =
      oneHighCanonicalFarDegree (twoEdges s)
        (leafLabel s ⟨x.1, oneHighBranchOwner_mem G v x⟩) := by
  classical
  let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
  let x := E.symm i
  let s := oneHighBranchOwner G v x
  let xLocal : secondLayerBranch G v s :=
    ⟨x.1, oneHighBranchOwner_mem G v x⟩
  have htotal := card_oneHighEncodedFarNeighbors_add_internal_eq_six
    G hfree hexternal mate hmateAdj branchLabel hbranchMate leafLabel i hiDegree
  have hinternal := card_neighbor_inter_branch_eq_canonicalMatched
    G s (twoEdges s) (leafLabel s) (hcanonical s) xLocal
  change (oneHighEncodedFarNeighbors
      (oneHighRelabeledLeafGraph G v E) i).card =
        oneHighCanonicalFarDegree (twoEdges s) (leafLabel s xLocal)
  change (G.neighborFinset x.1 ∩ secondLayerBranch G v s).card =
    if oneHighCanonicalBranchMatched (twoEdges s) (leafLabel s xLocal)
      then 1 else 0 at hinternal
  change (oneHighEncodedFarNeighbors
      (oneHighRelabeledLeafGraph G v E) i).card +
        (G.neighborFinset x.1 ∩ secondLayerBranch G v s).card = 6 at htotal
  by_cases hm : oneHighCanonicalBranchMatched (twoEdges s) (leafLabel s xLocal)
  · rw [if_pos hm] at hinternal
    simp [oneHighCanonicalFarDegree, hm]
    omega
  · rw [if_neg hm] at hinternal
    simp [oneHighCanonicalFarDegree, hm]
    omega

/-! ## Exact family profile coordinates -/

/-- The exact branch word used by `family_gen.py`: the low (even) endpoint
of each of the first `a` mate pairs has one internal edge; every other
five-point branch has two.  Thus `a=4,3,2,1,0` respectively encode
`AAAA, AAAB, AABB, ABBB, BBBB`. -/
def oneHighFamilyTwoEdges (a : Nat) (i : Fin 8) : Bool :=
  decide (¬(i.val % 2 = 0 ∧ i.val / 2 < a))

/-- Numeric form of the generator's `IN` array. -/
def oneHighFamilyInternalEdges (a : Nat) (i : Fin 8) : Nat :=
  if i.val % 2 = 0 ∧ i.val / 2 < a then 1 else 2

/-- Literal far-degree target for block `b` and within-block coordinate `r`.
This is `family_gen.py`'s `degfar`: positions 0,1 are always matched;
positions 2,3 are matched exactly when `IN[b]=2`; position 4 is unmatched. -/
def oneHighFamilyFarDegree (a : Nat) (b : Fin 8) (r : Fin 5) : Nat :=
  if r.val < 2 ∨
      (oneHighFamilyInternalEdges a b = 2 ∧ r.val < 4) then 5 else 6

/-- The canonical-branch and literal `IN` descriptions of far degree agree. -/
theorem oneHighCanonicalFarDegree_familyTwoEdges
    (a : Nat) (b : Fin 8) (r : Fin 5) :
    oneHighCanonicalFarDegree (oneHighFamilyTwoEdges a b) r =
      oneHighFamilyFarDegree a b r := by
  unfold oneHighCanonicalFarDegree oneHighCanonicalBranchMatched
    oneHighFamilyTwoEdges oneHighFamilyFarDegree oneHighFamilyInternalEdges
  by_cases hp : b.val % 2 = 0 ∧ b.val / 2 < a
  · simp [hp]
  · simp [hp]

/-! ## Encoder-facing paired-product ledger -/

/-- Ordered pairs in two encoded five-point blocks having one common leaf
neighbor.  This is the Boolean product counted by the generator's m-free
paired-product cardinality constraints. -/
def oneHighEncodedCommonPairBlock
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (a b : Fin 8) : Finset (Fin 40 × Fin 40) :=
  (((Finset.univ.filter fun i =>
      Fin.divNat (m := 8) (n := 5) i = a) ×ˢ
    (Finset.univ.filter fun j =>
      Fin.divNat (m := 8) (n := 5) j = b))).filter fun ij =>
        (R.neighborFinset ij.1 ∩ R.neighborFinset ij.2).card = 1

set_option maxHeartbeats 800000 in
/-- The encoded common-pair product is exactly the graph-theoretic outer
nondefect block. -/
theorem card_oneHighEncodedCommonPairBlock_eq_outerNondefect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (s t : {z : V // z ∈ G.neighborSet v}) (hst : s ≠ t) :
    let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
    let R := oneHighRelabeledLeafGraph G v E
    (oneHighEncodedCommonPairBlock R (branchLabel s) (branchLabel t)).card =
      (orderFortyNineOuterNondefectBlock G v s t).card := by
  classical
  let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
  let R := oneHighRelabeledLeafGraph G v E
  apply Finset.card_bij (fun ij _ => (E.symm ij.1, E.symm ij.2))
  · intro ij hij
    have hp := Finset.mem_filter.mp hij
    have hb := Finset.mem_product.mp hp.1
    have hbi := (Finset.mem_filter.mp hb.1).2
    have hbj := (Finset.mem_filter.mp hb.2).2
    let x := E.symm ij.1
    let y := E.symm ij.2
    have hxi := oneHighLeafFinFortyEquiv_divNat
      G hfree v branchLabel leafLabel x
    have hyj := oneHighLeafFinFortyEquiv_divNat
      G hfree v branchLabel leafLabel y
    rw [E.apply_symm_apply] at hxi hyj
    have hxOwn : oneHighBranchOwner G v x = s := by
      apply branchLabel.injective
      rw [← hxi]
      exact hbi
    have hyOwn : oneHighBranchOwner G v y = t := by
      apply branchLabel.injective
      rw [← hyj]
      exact hbj
    apply (mem_orderFortyNineOuterNondefectBlock_iff_common_eq_one
      G hfree s t hst x y).mpr
    refine ⟨hxOwn ▸ oneHighBranchOwner_mem G v x,
      hyOwn ▸ oneHighBranchOwner_mem G v y, ?_⟩
    rw [← oneHighRelabeledLeafGraph_common_card_eq G v E ij.1 ij.2]
    exact hp.2
  · intro a _ b _ hab
    apply Prod.ext
    · exact E.symm.injective (congrArg Prod.fst hab)
    · exact E.symm.injective (congrArg Prod.snd hab)
  · intro xy hxy
    have ho := (mem_orderFortyNineOuterNondefectBlock_iff_common_eq_one
      G hfree s t hst xy.1 xy.2).mp hxy
    have hxOwn := oneHighBranchOwner_eq_of_mem
      G hfree v xy.1 s ho.1
    have hyOwn := oneHighBranchOwner_eq_of_mem
      G hfree v xy.2 t ho.2.1
    have hxi := oneHighLeafFinFortyEquiv_divNat
      G hfree v branchLabel leafLabel xy.1
    have hyj := oneHighLeafFinFortyEquiv_divNat
      G hfree v branchLabel leafLabel xy.2
    refine ⟨(E xy.1, E xy.2), ?_, by simp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩, ?_⟩
    · simpa [hxOwn] using hxi
    · simpa [hyOwn] using hyj
    · rw [oneHighRelabeledLeafGraph_common_card_eq G v E]
      rw [E.symm_apply_apply, E.symm_apply_apply]
      exact ho.2.2

/-- Exact m-free paired-product ledger in encoder coordinates.  For each
standard mate pair, the number of ordered cross-block pairs with one common
leaf, plus the two branches' matched-vertex counts, is `30`; since a branch
with `in` canonical internal edges has `2 * in` matched vertices, this is
the generator equation `product = 30 - 2*inᵢ - 2*inⱼ`. -/
theorem card_oneHighEncodedCommonPairBlock_add_matched_eq_thirty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (hunique : ∀ {w : V}, G.degree w = 8 → w = v)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hmateInv : Function.Involutive mate)
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1)
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (hbranchMate : ∀ s,
      branchLabel (mate s) = oneHighStandardMate (branchLabel s))
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (s : {z : V // z ∈ G.neighborSet v}) :
    let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
    let R := oneHighRelabeledLeafGraph G v E
    (oneHighEncodedCommonPairBlock R (branchLabel s)
        (oneHighStandardMate (branchLabel s))).card +
      highBranchMatchedCount G v s +
      highBranchMatchedCount G v (mate s) = 30 := by
  classical
  have hmateNe : s ≠ mate s := by
    intro h
    exact G.loopless.irrefl s.1 (congrArg Subtype.val h ▸ hmateAdj s)
  rw [← hbranchMate]
  dsimp only
  rw [card_oneHighEncodedCommonPairBlock_eq_outerNondefect
    G hfree branchLabel leafLabel s (mate s) hmateNe]
  exact (graph_exact_outerNondefectBlocks_of_mate_involution
    G hfree hmin hcard hv hunique hexternal houterDegree
      mate hmateInv hmateAdj s).1

/-- The paired-product ledger in the generator's literal `IN` coordinates.
This is the subtraction-free form of its cardinality bound
`30 - 2*IN[bi] - 2*IN[bj]`. -/
theorem card_oneHighEncodedCommonPairBlock_add_familyIN_eq_thirty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (hunique : ∀ {w : V}, G.degree w = 8 → w = v)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {x : V}, x ∈ secondLayer G v → G.degree x = 7)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hmateInv : Function.Involutive mate)
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1)
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (hbranchMate : ∀ s,
      branchLabel (mate s) = oneHighStandardMate (branchLabel s))
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (a : Nat)
    (hIN : ∀ i, highBranchMatchedCount G v (branchLabel.symm i) =
      2 * oneHighFamilyInternalEdges a i)
    (s : {z : V // z ∈ G.neighborSet v}) :
    let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
    let R := oneHighRelabeledLeafGraph G v E
    (oneHighEncodedCommonPairBlock R (branchLabel s)
        (oneHighStandardMate (branchLabel s))).card +
      2 * oneHighFamilyInternalEdges a (branchLabel s) +
      2 * oneHighFamilyInternalEdges a
        (oneHighStandardMate (branchLabel s)) = 30 := by
  have hledger := card_oneHighEncodedCommonPairBlock_add_matched_eq_thirty
    G hfree hmin hcard hv hunique hexternal houterDegree mate
      hmateInv hmateAdj branchLabel hbranchMate leafLabel s
  have hs := hIN (branchLabel s)
  rw [branchLabel.symm_apply_apply] at hs
  have hm := hIN (oneHighStandardMate (branchLabel s))
  rw [← hbranchMate s, branchLabel.symm_apply_apply] at hm
  simpa [hs, hm, hbranchMate s] using hledger

/-! ## Simultaneous generator labeling terminal -/

/-- Family ordering determines the exact matched-vertex count `2 * IN[i]`
used by the far-degree, paired-product, and augmented k-sum bounds. -/
theorem highBranchMatchedCount_eq_two_mul_familyInternalEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (a : Nat)
    (hfamily : ∀ i,
      decide (highBranchMatchedCount G v (branchLabel.symm i) = 2) =
        decide (i.val % 2 = 0 ∧ i.val / 2 < a))
    (hstates : ∀ i,
      highBranchMatchedCount G v (branchLabel.symm i) = 2 ∨
      highBranchMatchedCount G v (branchLabel.symm i) = 4) :
    ∀ i, highBranchMatchedCount G v (branchLabel.symm i) =
      2 * oneHighFamilyInternalEdges a i := by
  intro i
  have hf := hfamily i
  rcases hstates i with hs | hs
  · have hp : i.val % 2 = 0 ∧ i.val / 2 < a := by
      have hl : decide
          (highBranchMatchedCount G v (branchLabel.symm i) = 2) = true := by
        simp [hs]
      rw [hl] at hf
      exact of_decide_eq_true hf.symm
    simp [oneHighFamilyInternalEdges, hp, hs]
  · have hp : ¬(i.val % 2 = 0 ∧ i.val / 2 < a) := by
      have hne : highBranchMatchedCount G v (branchLabel.symm i) ≠ 2 := by
        omega
      have hl : decide
          (highBranchMatchedCount G v (branchLabel.symm i) = 2) = false := by
        simp [hne]
      rw [hl] at hf
      exact of_decide_eq_false hf.symm
    simp [oneHighFamilyInternalEdges, hp, hs]

/-- The matched-count characterization of a family-ordered labeling fixes
the generator's one-edge/two-edge Boolean word pointwise. -/
theorem oneHighFamilyTwoEdges_eq_of_matchedCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (twoEdges : {z : V // z ∈ G.neighborSet v} → Bool)
    (a : Nat)
    (hfamily : ∀ i,
      decide (highBranchMatchedCount G v (branchLabel.symm i) = 2) =
        decide (i.val % 2 = 0 ∧ i.val / 2 < a))
    (hstates : ∀ s,
      (twoEdges s = false ∧ highBranchMatchedCount G v s = 2) ∨
      (twoEdges s = true ∧ highBranchMatchedCount G v s = 4)) :
    ∀ i, twoEdges (branchLabel.symm i) = oneHighFamilyTwoEdges a i := by
  intro i
  have hf := hfamily i
  have hs := hstates (branchLabel.symm i)
  by_cases hp : i.val % 2 = 0 ∧ i.val / 2 < a
  · have hm : highBranchMatchedCount G v (branchLabel.symm i) = 2 := by
      have hr : decide (i.val % 2 = 0 ∧ i.val / 2 < a) = true := by
        simp [hp]
      rw [hr] at hf
      exact of_decide_eq_true hf
    rcases hs with hs | hs
    · simp [oneHighFamilyTwoEdges, hp, hs.1]
    · omega
  · have hm : highBranchMatchedCount G v (branchLabel.symm i) ≠ 2 := by
      have hr : decide (i.val % 2 = 0 ∧ i.val / 2 < a) = false := by
        simp [hp]
      rw [hr] at hf
      exact of_decide_eq_false hf
    rcases hs with hs | hs
    · exact (hm hs.2).elim
    · simp [oneHighFamilyTwoEdges, hp, hs.1]

/-- Exact Fin40 far-degree counter target in the generator's literal block
and within-block coordinates. -/
theorem card_oneHighEncodedFarNeighbors_eq_familyFarDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hexternal : externalRepairCandidates G v = ∅)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1)
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (hbranchMate : ∀ s,
      branchLabel (mate s) = oneHighStandardMate (branchLabel s))
    (twoEdges : {z : V // z ∈ G.neighborSet v} → Bool)
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (hcanonical : ∀ s x y, decide (G.Adj x.1 y.1) =
      oneHighCanonicalBranchAdj (twoEdges s)
        (leafLabel s x) (leafLabel s y))
    (a : Nat)
    (hword : ∀ i, twoEdges (branchLabel.symm i) =
      oneHighFamilyTwoEdges a i)
    (i : Fin 40)
    (hiDegree : G.degree
      ((oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel).symm i).1 = 7) :
    let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
    let R := oneHighRelabeledLeafGraph G v E
    (oneHighEncodedFarNeighbors R i).card =
      oneHighFamilyFarDegree a
        (Fin.divNat (m := 8) (n := 5) i)
        (Fin.modNat (m := 8) (n := 5) i) := by
  let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
  let x := E.symm i
  let s := oneHighBranchOwner G v x
  let xLocal : secondLayerBranch G v s :=
    ⟨x.1, oneHighBranchOwner_mem G v x⟩
  have hfar := card_oneHighEncodedFarNeighbors_eq_canonicalFarDegree
    G hfree hexternal mate hmateAdj branchLabel hbranchMate
      twoEdges leafLabel hcanonical i hiDegree
  change (oneHighEncodedFarNeighbors
      (oneHighRelabeledLeafGraph G v E) i).card =
        oneHighCanonicalFarDegree (twoEdges s) (leafLabel s xLocal) at hfar
  have hb := oneHighLeafFinFortyEquiv_divNat
    G hfree v branchLabel leafLabel x
  have hr := oneHighLeafFinFortyEquiv_modNat
    G hfree v branchLabel leafLabel x
  rw [E.apply_symm_apply] at hb hr
  have hw := hword (branchLabel s)
  rw [branchLabel.symm_apply_apply] at hw
  change (oneHighEncodedFarNeighbors
      (oneHighRelabeledLeafGraph G v E) i).card = _
  calc
    _ = oneHighCanonicalFarDegree (twoEdges s) (leafLabel s xLocal) := hfar
    _ = oneHighCanonicalFarDegree
        (oneHighFamilyTwoEdges a (branchLabel s)) (leafLabel s xLocal) := by
          rw [hw]
    _ = oneHighFamilyFarDegree a (branchLabel s) (leafLabel s xLocal) :=
      oneHighCanonicalFarDegree_familyTwoEdges a (branchLabel s) _
    _ = oneHighFamilyFarDegree a
        (Fin.divNat (m := 8) (n := 5) i)
        (Fin.modNat (m := 8) (n := 5) i) := by rw [hb, hr]

/-- A raw one-high graph admits all coordinate choices used by the family
generator simultaneously: one mate involution, a family-ordered standard
Fin8 labeling, and lex-sorted canonical Fin5 labels in every branch. -/
theorem orderFortyNine_exists_simultaneous_familyGeneratorLabels
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8) :
    ∃ (mate : {z : V // z ∈ G.neighborSet v} →
          {z : V // z ∈ G.neighborSet v})
      (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
      (twoEdges : {z : V // z ∈ G.neighborSet v} → Bool)
      (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
        secondLayerBranch G v s ≃ Fin 5),
      Function.Involutive mate ∧
      (∀ s, G.Adj s.1 (mate s).1) ∧
      OneHighAugmentedFamilyLaws G v mate ∧
      (∀ s, branchLabel (mate s) =
        oneHighStandardMate (branchLabel s)) ∧
      (∀ i,
        decide (highBranchMatchedCount G v (branchLabel.symm i) = 2) =
          decide (i.val % 2 = 0 ∧
            i.val / 2 < ((Finset.univ :
              Finset {z : V // z ∈ G.neighborSet v}).filter fun s =>
                highBranchMatchedCount G v s = 2).card)) ∧
      (∀ i, twoEdges (branchLabel.symm i) =
        oneHighFamilyTwoEdges
          ((Finset.univ :
            Finset {z : V // z ∈ G.neighborSet v}).filter fun s =>
              highBranchMatchedCount G v s = 2).card i) ∧
      ∀ s,
        ((twoEdges s = false ∧ highBranchMatchedCount G v s = 2) ∨
          (twoEdges s = true ∧ highBranchMatchedCount G v s = 4)) ∧
        (∀ x y, decide (G.Adj x.1 y.1) =
          oneHighCanonicalBranchAdj (twoEdges s)
            (leafLabel s x) (leafLabel s y)) ∧
        branchLabel (oneHighMissingBranch G v mate s
            ((leafLabel s).symm 0).1) ≤
          branchLabel (oneHighMissingBranch G v mate s
            ((leafLabel s).symm 1).1) ∧
        (twoEdges s = true →
          branchLabel (oneHighMissingBranch G v mate s
              ((leafLabel s).symm 2).1) ≤
            branchLabel (oneHighMissingBranch G v mate s
              ((leafLabel s).symm 3).1) ∧
          branchLabel (oneHighMissingBranch G v mate s
              ((leafLabel s).symm 0).1) ≤
            branchLabel (oneHighMissingBranch G v mate s
              ((leafLabel s).symm 2).1)) := by
  classical
  have hunique : ∀ {w : V}, G.degree w = 8 → w = v := by
    intro w hw
    have hvMem : v ∈ orderFortyNineHighVertices G := by
      simp [orderFortyNineHighVertices, hv]
    have hwMem : w ∈ orderFortyNineHighVertices G := by
      simp [orderFortyNineHighVertices, hw]
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hHigh
    have hvz : v = z := by simpa [hz] using hvMem
    have hwz : w = z := by simpa [hz] using hwMem
    exact hwz.trans hvz.symm
  have hlocal : ∀ s : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree s = 1 :=
    orderFortyNine_localNeighborhood_degree_eq_one_of_degreeEight
      G hfree hmin hcard hv
  obtain ⟨mate, hmateInv, hmateAdj⟩ :=
    exists_localMate_involution G v hlocal
  have hexternal : externalRepairCandidates G v = ∅ :=
    orderFortyNine_externalRepairCandidates_degreeEight_eq_empty
      G hfree hmin hcard hv
  have houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7 := by
    intro a ha
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin hcard a with ha7 | ha8
    · exact ha7
    · have hav : a = v := hunique ha8
      rw [secondLayer] at ha
      rcases Finset.mem_biUnion.mp ha with ⟨s, _, has⟩
      exact ((Finset.mem_sdiff.mp has).2 (by simp [hav])).elim
  obtain ⟨branchLabel, hbranchMate, hfamily⟩ :=
    exists_oneHigh_branchLabeling_familyOrdered
      G hfree hmin hcard hv hunique hexternal houterDegree
        mate hmateInv hmateAdj
  have hlabels : ∀ s : {z : V // z ∈ G.neighborSet v},
      ∃ (b : Bool) (e : secondLayerBranch G v s ≃ Fin 5),
        ((b = false ∧ highBranchMatchedCount G v s = 2) ∨
          (b = true ∧ highBranchMatchedCount G v s = 4)) ∧
        (∀ x y, decide (G.Adj x.1 y.1) =
          oneHighCanonicalBranchAdj b (e x) (e y)) ∧
        branchLabel (oneHighMissingBranch G v mate s (e.symm 0).1) ≤
          branchLabel (oneHighMissingBranch G v mate s (e.symm 1).1) ∧
        (b = true →
          branchLabel (oneHighMissingBranch G v mate s (e.symm 2).1) ≤
            branchLabel (oneHighMissingBranch G v mate s (e.symm 3).1) ∧
          branchLabel (oneHighMissingBranch G v mate s (e.symm 0).1) ≤
            branchLabel (oneHighMissingBranch G v mate s (e.symm 2).1)) := by
    intro s
    exact exists_oneHigh_branchVertexLabeling_generatorLex
      G hfree hmin hcard hv hunique hexternal houterDegree
        mate hmateInv hmateAdj branchLabel s
  let twoEdges := fun s => (hlabels s).choose
  let leafLabel := fun s => (hlabels s).choose_spec.choose
  have haug : OneHighAugmentedFamilyLaws G v mate :=
    oneHighAugmentedFamilyLaws_of_mate
      G hfree hmin hcard hHigh hv mate hmateInv hmateAdj
  have hword : ∀ i, twoEdges (branchLabel.symm i) =
      oneHighFamilyTwoEdges
        ((Finset.univ :
          Finset {z : V // z ∈ G.neighborSet v}).filter fun s =>
            highBranchMatchedCount G v s = 2).card i :=
    oneHighFamilyTwoEdges_eq_of_matchedCount
      G branchLabel twoEdges _ hfamily (fun s =>
        (hlabels s).choose_spec.choose_spec.1)
  refine ⟨mate, branchLabel, twoEdges, leafLabel,
    hmateInv, hmateAdj, haug, hbranchMate, hfamily, hword, ?_⟩
  intro s
  exact (hlabels s).choose_spec.choose_spec

end

end Erdos85
