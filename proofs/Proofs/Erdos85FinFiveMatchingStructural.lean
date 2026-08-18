import Proofs.Erdos85FinFourFreeInvolution

/-! # Structural canonicalization of five-point matchings -/

namespace Erdos85

noncomputable section

private theorem branchBitAdj_comm
    (edges : BitVec 10) (i j : Fin 5) :
    oneHighBranchBitAdj edges i j = oneHighBranchBitAdj edges j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · simp [oneHighBranchBitAdj, hij, Ne.symm hij,
      oneHighBranchEdgeIndex, min_comm, max_comm]

private theorem branchBitAdj_self
    (edges : BitVec 10) (i : Fin 5) :
    oneHighBranchBitAdj edges i i = false := by
  simp [oneHighBranchBitAdj]

def finFiveMatchedVertices (edges : BitVec 10) : Finset (Fin 5) :=
  Finset.univ.filter fun i =>
    (Finset.univ.filter fun j => oneHighBranchBitAdj edges i j).card = 1

private noncomputable def finFiveMatchingMateVal
    (edges : BitVec 10) (x : {i // i ∈ finFiveMatchedVertices edges}) : Fin 5 :=
  Classical.choose (Finset.card_eq_one.mp
    (Finset.mem_filter.mp x.2).2)

private theorem finFiveMatchingMateVal_spec
    (edges : BitVec 10) (x : {i // i ∈ finFiveMatchedVertices edges}) :
    (Finset.univ.filter fun j => oneHighBranchBitAdj edges x.1 j) =
      {finFiveMatchingMateVal edges x} := by
  exact Classical.choose_spec (Finset.card_eq_one.mp
    (Finset.mem_filter.mp x.2).2)

private theorem finFiveMatchingMateVal_adj
    (edges : BitVec 10) (x : {i // i ∈ finFiveMatchedVertices edges}) :
    oneHighBranchBitAdj edges x.1 (finFiveMatchingMateVal edges x) = true := by
  have hm : finFiveMatchingMateVal edges x ∈
      (Finset.univ.filter fun j => oneHighBranchBitAdj edges x.1 j) := by
    rw [finFiveMatchingMateVal_spec]
    simp
  simpa using (Finset.mem_filter.mp hm).2

private theorem finFiveMatchingMateVal_mem
    (edges : BitVec 10)
    (hdegree : ∀ i : Fin 5,
      (Finset.univ.filter fun j => oneHighBranchBitAdj edges i j).card ≤ 1)
    (x : {i // i ∈ finFiveMatchedVertices edges}) :
    finFiveMatchingMateVal edges x ∈ finFiveMatchedVertices edges := by
  let y := finFiveMatchingMateVal edges x
  have hyx : oneHighBranchBitAdj edges y x.1 = true := by
    rw [branchBitAdj_comm]
    exact finFiveMatchingMateVal_adj edges x
  have hpos : 0 <
      (Finset.univ.filter fun z => oneHighBranchBitAdj edges y z).card := by
    apply Finset.card_pos.mpr
    exact ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyx⟩⟩
  have hle := hdegree y
  have hone :
      (Finset.univ.filter fun z => oneHighBranchBitAdj edges y z).card = 1 := by
    omega
  exact Finset.mem_filter.mpr ⟨by simp, hone⟩

/-- The unique-neighbor map on the matched vertices of a degree-at-most-one
relation. -/
def finFiveMatchingMate
    (edges : BitVec 10)
    (hdegree : ∀ i : Fin 5,
      (Finset.univ.filter fun j => oneHighBranchBitAdj edges i j).card ≤ 1) :
    {i // i ∈ finFiveMatchedVertices edges} →
      {i // i ∈ finFiveMatchedVertices edges} :=
  fun x => ⟨finFiveMatchingMateVal edges x,
    finFiveMatchingMateVal_mem edges hdegree x⟩

theorem finFiveMatchingMate_ne
    (edges : BitVec 10)
    (hdegree : ∀ i : Fin 5,
      (Finset.univ.filter fun j => oneHighBranchBitAdj edges i j).card ≤ 1)
    (x : {i // i ∈ finFiveMatchedVertices edges}) :
    finFiveMatchingMate edges hdegree x ≠ x := by
  intro h
  have hadj := finFiveMatchingMateVal_adj edges x
  have hval : finFiveMatchingMateVal edges x = x.1 := congrArg Subtype.val h
  rw [hval, branchBitAdj_self] at hadj
  contradiction

theorem finFiveMatchingMate_involutive
    (edges : BitVec 10)
    (hdegree : ∀ i : Fin 5,
      (Finset.univ.filter fun j => oneHighBranchBitAdj edges i j).card ≤ 1) :
    Function.Involutive (finFiveMatchingMate edges hdegree) := by
  intro x
  apply Subtype.ext
  let y := finFiveMatchingMate edges hdegree x
  have hxy : oneHighBranchBitAdj edges y.1 x.1 = true := by
    rw [branchBitAdj_comm]
    exact finFiveMatchingMateVal_adj edges x
  have hxmem : x.1 ∈
      (Finset.univ.filter fun z => oneHighBranchBitAdj edges y.1 z) :=
    Finset.mem_filter.mpr ⟨by simp, hxy⟩
  have hySpec := finFiveMatchingMateVal_spec edges y
  rw [hySpec] at hxmem
  have hxEq : x.1 = finFiveMatchingMateVal edges y := by
    simpa using hxmem
  simpa [y, finFiveMatchingMate] using hxEq.symm

theorem card_finFiveMatchedVertices
    (edges : BitVec 10) (twoEdges : Bool)
    (hmatched : (Finset.univ.filter fun i =>
      (Finset.univ.filter fun j => oneHighBranchBitAdj edges i j).card = 1).card =
        if twoEdges then 4 else 2) :
    (finFiveMatchedVertices edges).card = if twoEdges then 4 else 2 := by
  exact hmatched

theorem fintypeCard_finFiveMatchedVertices
    (edges : BitVec 10) (twoEdges : Bool)
    (hmatched : (Finset.univ.filter fun i =>
      (Finset.univ.filter fun j => oneHighBranchBitAdj edges i j).card = 1).card =
        if twoEdges then 4 else 2) :
    Fintype.card {i // i ∈ finFiveMatchedVertices edges} =
      if twoEdges then 4 else 2 := by
  rw [Fintype.card_coe]
  exact card_finFiveMatchedVertices edges twoEdges hmatched

theorem finFiveBranchBitAdj_iff_matchingMate
    (edges : BitVec 10)
    (hdegree : ∀ i : Fin 5,
      (Finset.univ.filter fun j => oneHighBranchBitAdj edges i j).card ≤ 1)
    (x y : {i // i ∈ finFiveMatchedVertices edges}) :
    oneHighBranchBitAdj edges x.1 y.1 = true ↔
      finFiveMatchingMate edges hdegree x = y := by
  constructor
  · intro hxy
    apply Subtype.ext
    have hymem : y.1 ∈
        (Finset.univ.filter fun z => oneHighBranchBitAdj edges x.1 z) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩
    rw [finFiveMatchingMateVal_spec] at hymem
    have hyEq : y.1 = finFiveMatchingMateVal edges x := by
      simpa using hymem
    simpa [finFiveMatchingMate] using hyEq.symm
  · intro hmate
    have hval : finFiveMatchingMateVal edges x = y.1 :=
      congrArg Subtype.val hmate
    simpa [hval] using finFiveMatchingMateVal_adj edges x

theorem finFiveBranchBitAdj_false_of_not_matched
    (edges : BitVec 10)
    (hdegree : ∀ i : Fin 5,
      (Finset.univ.filter fun j => oneHighBranchBitAdj edges i j).card ≤ 1)
    {x : Fin 5} (hx : x ∉ finFiveMatchedVertices edges) (y : Fin 5) :
    oneHighBranchBitAdj edges x y = false := by
  by_contra hxy
  have hxyTrue : oneHighBranchBitAdj edges x y = true :=
    Bool.eq_true_of_not_eq_false hxy
  have hpos : 0 <
      (Finset.univ.filter fun z => oneHighBranchBitAdj edges x z).card := by
    apply Finset.card_pos.mpr
    exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxyTrue⟩⟩
  have hone :
      (Finset.univ.filter fun z => oneHighBranchBitAdj edges x z).card = 1 := by
    have := hdegree x
    omega
  exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hone⟩)

/-- Kernel-checked canonical form of a degree-at-most-one relation on five
points having exactly two or four matched vertices. -/
theorem finFive_matchingBits_canonical_structural
    (edges : BitVec 10) (twoEdges : Bool)
    (hdegree : ∀ i : Fin 5,
      (Finset.univ.filter fun j => oneHighBranchBitAdj edges i j).card ≤ 1)
    (hmatched : (Finset.univ.filter fun i =>
      (Finset.univ.filter fun j => oneHighBranchBitAdj edges i j).card = 1).card =
        if twoEdges then 4 else 2) :
    ∃ σ : Equiv.Perm (Fin 5), ∀ i j,
      oneHighBranchBitAdj edges i j =
        oneHighCanonicalBranchAdj twoEdges (σ i) (σ j) := by
  set_option maxRecDepth 10000 in
    decide +revert

end

end Erdos85
