import Proofs.Erdos85OddSquareOrderNineOrder34PuncturedProfileCapstone

/-! # Owner-puncture transfer for the order-27 articulation branch -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Normalize the unordered `(27,50)` articulation output, retaining the
boundary equation belonging to each oriented shore.  FullType cannot occur
on the 50-point shore. -/
theorem orderNine_order27_orient_articulation_shores
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Finset V) (h₁ h₂ h₃ : V) (U S T : Finset V)
    (hunion : S ∪ T = U) (hdisj : Disjoint S T)
    (horders : (S.card = 27 ∧ T.card = 50) ∨
      (S.card = 50 ∧ T.card = 27))
    (hfull : orderNineArticulationSmallShoreFullType G E h₁ h₂ h₃ S ∨
      orderNineArticulationSmallShoreFullType G E h₁ h₂ h₃ T)
    (hSclosed : ∀ x ∈ S,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ S)
    (hTclosed : ∀ x ∈ T,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ T)
    (hSboundary : (∑ x ∈ S,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ S)).card) = (E ∩ S).card)
    (hTboundary : (∑ x ∈ T,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ T)).card) = (E ∩ T).card) :
    ∃ A B : Finset V,
      A ∪ B = U ∧ Disjoint A B ∧ A.card = 27 ∧ B.card = 50 ∧
      orderNineArticulationSmallShoreFullType G E h₁ h₂ h₃ A ∧
      (∀ x ∈ A, (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ A) ∧
      (∀ x ∈ B, (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ B) ∧
      (∑ x ∈ A, ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ A)).card) = (E ∩ A).card ∧
      (∑ x ∈ B, ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ B)).card) = (E ∩ B).card := by
  rcases horders with hST | hTS
  · rcases hfull with hfullS | hfullT
    · exact ⟨S, T, hunion, hdisj, hST.1, hST.2, hfullS,
        hSclosed, hTclosed, hSboundary, hTboundary⟩
    · have hbad := hfullT.1
      unfold orderNineArticulationSmallShoreBetaType at hbad
      omega
  · rcases hfull with hfullS | hfullT
    · have hbad := hfullS.1
      unfold orderNineArticulationSmallShoreBetaType at hbad
      omega
    · exact ⟨T, S, by simpa [Finset.union_comm] using hunion,
        hdisj.symm, hTS.2, hTS.1, hfullT, hTclosed, hSclosed,
        hTboundary, hSboundary⟩

/-- In an oriented order-27 split, the five exceptional points divide as
three on the FullType small shore and two on the large shore. -/
theorem orderNine_order27_exceptional_inter_large_card_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (E A B U : Finset V) (h₁ h₂ h₃ : V)
    (hunion : A ∪ B = U) (hdisj : Disjoint A B)
    (hEsub : E ⊆ U) (hEcard : E.card = 5)
    (hAcard : A.card = 27)
    (hfull : orderNineArticulationSmallShoreFullType G E h₁ h₂ h₃ A) :
    (E ∩ B).card = 2 := by
  have hEA : (E ∩ A).card = 3 := hfull.2.2.1 hAcard
  have hsplit : (E ∩ A).card + (E ∩ B).card = E.card := by
    have hset : (E ∩ A) ∪ (E ∩ B) = E := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact (Finset.mem_inter.mp hx).1
        · exact (Finset.mem_inter.mp hx).1
      · intro hxE
        have hxU := hEsub hxE
        rw [← hunion] at hxU
        rcases Finset.mem_union.mp hxU with hxA | hxB
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxE, hxA⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxE, hxB⟩)
    have hd : Disjoint (E ∩ A) (E ∩ B) :=
      Finset.disjoint_of_subset_right Finset.inter_subset_right
        (Finset.disjoint_of_subset_left Finset.inter_subset_right hdisj)
    rw [← Finset.card_union_of_disjoint hd, hset]
  omega

/-- If the 27-shore has three incidences from a high root, then the
opposite 50-shore has six: the tenth incidence is the deleted owner. -/
theorem orderNine_order27_high_neighbor_large_card_eq_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H A B : Finset V) (owner h : V)
    (hunion : A ∪ B = ((Finset.univ : Finset V) \ H).erase owner)
    (hdisj : Disjoint A B)
    (hownerO : owner ∈ (Finset.univ : Finset V) \ H)
    (hownerAdj : G.Adj h owner)
    (hdeg : G.degree h = 10)
    (hhighIndependent : Disjoint (G.neighborFinset h) H)
    (hsmall : (G.neighborFinset h ∩ A).card = 3) :
    (G.neighborFinset h ∩ B).card = 6 := by
  let O := (Finset.univ : Finset V) \ H
  let U := O.erase owner
  have hunion' : A ∪ B = U := by simpa [U, O] using hunion
  have hAsubU : A ⊆ U := by
    intro x hx
    rw [← hunion']
    exact Finset.mem_union_left B hx
  have hBsubU : B ⊆ U := by
    intro x hx
    rw [← hunion']
    exact Finset.mem_union_right A hx
  have hcompSet : O \ A = insert owner B := by
    ext x
    constructor
    · intro hx
      have hxO := (Finset.mem_sdiff.mp hx).1
      have hxA := (Finset.mem_sdiff.mp hx).2
      by_cases hxo : x = owner
      · exact Finset.mem_insert.mpr (Or.inl hxo)
      · have hxU : x ∈ U := Finset.mem_erase.mpr ⟨hxo, hxO⟩
        rw [← hunion'] at hxU
        rcases Finset.mem_union.mp hxU with hxA' | hxB
        · exact (hxA hxA').elim
        · exact Finset.mem_insert.mpr (Or.inr hxB)
    · intro hx
      rcases Finset.mem_insert.mp hx with rfl | hxB
      · exact Finset.mem_sdiff.mpr ⟨hownerO,
          fun hoA => (Finset.mem_erase.mp (hAsubU hoA)).1 rfl⟩
      · have hxU := hBsubU hxB
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_erase.mp hxU).2,
          fun hxA => Finset.disjoint_left.mp hdisj hxA hxB⟩
  have hcomp := orderNine_high_neighbor_ordinary_compl_card
    G H A h hdeg hhighIndependent
  change (G.neighborFinset h ∩ (O \ A)).card =
    10 - (G.neighborFinset h ∩ A).card at hcomp
  rw [hcompSet, hsmall] at hcomp
  have hownerNotB : owner ∉ B := by
    intro hoB
    exact (Finset.mem_erase.mp (hBsubU hoB)).1 rfl
  have hset : G.neighborFinset h ∩ insert owner B =
      insert owner (G.neighborFinset h ∩ B) := by
    ext x
    simp [hownerAdj]
  rw [hset, Finset.card_insert_of_notMem] at hcomp
  · omega
  · intro hm
    exact hownerNotB (Finset.mem_inter.mp hm).2

/-- Direct sharp-partition extraction on the actual 50-point shore.  This
is preferable in the graph-facing wrapper to transferring the 51-point
complement partition: the articulation capstone already supplies this
shore's boundary equality. -/
theorem orderNine_order27_explicitPartition_of_large_boundary
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃) (h₂₃ : h₂ ≠ h₃)
    (T : Finset V) (hTcard : T.card = 50)
    (hTsub : T ⊆ (Finset.univ : Finset V) \ {h₁, h₂, h₃})
    (hboundary : (∑ x ∈ T,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ T)).card) = 2)
    (hhigh₁ : (G.neighborFinset h₁ ∩ T).card = 6)
    (hhigh₂ : (G.neighborFinset h₂ ∩ T).card = 6)
    (hhigh₃ : (G.neighborFinset h₃ ∩ T).card = 6)
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ x ∈ ({h₁, h₂, h₃} : Finset V), G.degree x = 10) :
    orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ T 5 42 := by
  have hTH : Disjoint T ({h₁, h₂, h₃} : Finset V) := by
    rw [Finset.disjoint_left]
    intro x hxT hxH
    exact (Finset.mem_sdiff.mp (hTsub hxT)).2 hxH
  have hsharp := orderNineOrdinarySharpPartition_of_boundary
    G hfree hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ T hTH hdegOrd hdegHigh 2
      hboundary (by
        simp [orderNineNearRegularCutLower, orderNineBalancedSquareSum,
          hTcard, hhigh₁, hhigh₂, hhigh₃])
  apply orderNineOrdinaryExplicitPartition_of_sharp
    G h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ T 5 42 hTH hdegOrd hsharp
  · omega
  · norm_num

/-- Complete equation-(20) package on oriented actual articulation shores. -/
theorem orderNine_order27_largeShore_profile_package
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃) (h₂₃ : h₂ ≠ h₃)
    (owner : V) (E A B : Finset V)
    (hunion : A ∪ B =
      ((Finset.univ : Finset V) \ {h₁, h₂, h₃}).erase owner)
    (hdisj : Disjoint A B)
    (hEsub : E ⊆
      ((Finset.univ : Finset V) \ {h₁, h₂, h₃}).erase owner)
    (hEcard : E.card = 5)
    (hAcard : A.card = 27) (hBcard : B.card = 50)
    (hownerO : owner ∈
      (Finset.univ : Finset V) \ {h₁, h₂, h₃})
    (hfull : orderNineArticulationSmallShoreFullType G E h₁ h₂ h₃ A)
    (hBboundary : (∑ x ∈ B,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ B)).card) = (E ∩ B).card)
    (hownerAdj₁ : G.Adj h₁ owner)
    (hownerAdj₂ : G.Adj h₂ owner)
    (hownerAdj₃ : G.Adj h₃ owner)
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ x ∈ ({h₁, h₂, h₃} : Finset V), G.degree x = 10)
    (hhighIndependent : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      Disjoint (G.neighborFinset h) ({h₁, h₂, h₃} : Finset V)) :
    let Z := orderNineOrdinaryLowSet G h₁ h₂ h₃ B 5
    orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ B 5 42 ∧
      Z.card = 36 ∧
      ∀ x : V,
        (((secondOrderDefectGraph G).neighborFinset x ∩ B).card : ℤ) =
          8 * (if x ∈ B then 1 else 0) - 4 -
            6 * (if x ∈ ({h₁, h₂, h₃} : Finset V) then 1 else 0) +
            ((G.neighborFinset x ∩ Z).card : ℤ) := by
  classical
  dsimp only
  let H : Finset V := {h₁, h₂, h₃}
  let U := ((Finset.univ : Finset V) \ H).erase owner
  let Z := orderNineOrdinaryLowSet G h₁ h₂ h₃ B 5
  have hBsubU : B ⊆ U := by
    intro x hx
    rw [← show A ∪ B = U by simpa [U, H] using hunion]
    exact Finset.mem_union_right A hx
  have hBsub : B ⊆ (Finset.univ : Finset V) \ H := by
    intro x hx
    exact (Finset.mem_erase.mp (hBsubU hx)).2
  have hsmall :
      (G.neighborFinset h₁ ∩ A).card = 3 ∧
      (G.neighborFinset h₂ ∩ A).card = 3 ∧
      (G.neighborFinset h₃ ∩ A).card = 3 := by
    have hb := hfull.1
    unfold orderNineArticulationSmallShoreBetaType at hb
    rcases hb with hb | hb | hb
    · omega
    · exact ⟨hb.2.1, hb.2.2.1, hb.2.2.2⟩
    · omega
  have hE2 : (E ∩ B).card = 2 :=
    orderNine_order27_exceptional_inter_large_card_eq_two
      G E A B U h₁ h₂ h₃ (by simpa [U, H] using hunion) hdisj
        (by simpa [U, H] using hEsub) hEcard hAcard hfull
  have hboundary : (∑ x ∈ B,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ B)).card) = 2 := hBboundary.trans hE2
  have hb₁ : (G.neighborFinset h₁ ∩ B).card = 6 :=
    orderNine_order27_high_neighbor_large_card_eq_six
      G H A B owner h₁ (by simpa [H] using hunion) hdisj
        (by simpa [H] using hownerO)
        hownerAdj₁ (hdegHigh h₁ (by simp [H]))
        (hhighIndependent h₁ (by simp [H])) hsmall.1
  have hb₂ : (G.neighborFinset h₂ ∩ B).card = 6 :=
    orderNine_order27_high_neighbor_large_card_eq_six
      G H A B owner h₂ (by simpa [H] using hunion) hdisj
        (by simpa [H] using hownerO)
        hownerAdj₂ (hdegHigh h₂ (by simp [H]))
        (hhighIndependent h₂ (by simp [H])) hsmall.2.1
  have hb₃ : (G.neighborFinset h₃ ∩ B).card = 6 :=
    orderNine_order27_high_neighbor_large_card_eq_six
      G H A B owner h₃ (by simpa [H] using hunion) hdisj
        (by simpa [H] using hownerO)
        hownerAdj₃ (hdegHigh h₃ (by simp [H]))
        (hhighIndependent h₃ (by simp [H])) hsmall.2.2
  have hpart := orderNine_order27_explicitPartition_of_large_boundary
    G hfree hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ B hBcard
      (by simpa [H] using hBsub) hboundary hb₁ hb₂ hb₃ hdegOrd hdegHigh
  have hZcard := orderNineOrdinaryLowSet_card G hcard
    h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ B 5 42 hpart
  have hBH : Disjoint B H := by
    rw [Finset.disjoint_left]
    intro x hxB hxH
    exact (Finset.mem_sdiff.mp (hBsub hxB)).2 hxH
  have heq := orderNineOrdinaryExplicitPartition_defect_lowSet_eq_nearRegular
    G hfree h₁ h₂ h₃ B 5 42 hpart hb₁ hb₂ hb₃
      (by simpa [H] using hBH) hdegOrd hdegHigh
  refine ⟨hpart, by simpa [Z] using hZcard, ?_⟩
  intro x
  have hx := heq x
  dsimp [Z] at hx ⊢
  rw [hBcard] at hx
  norm_num at hx ⊢
  convert hx using 1 <;> ring

/-- Equation (20) evaluated at an isolated high root puts all ten of its
neighbors in the 36-point low set. -/
theorem orderNine_order27_highRoot_neighbors_subset_lowSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B Z H : Finset V) (h : V)
    (hhH : h ∈ H) (hhB : h ∉ B)
    (hdeg : G.degree h = 10)
    (hDzero : ((secondOrderDefectGraph G).neighborFinset h ∩ B).card = 0)
    (heq20 : ∀ x : V,
      (((secondOrderDefectGraph G).neighborFinset x ∩ B).card : ℤ) =
        8 * (if x ∈ B then 1 else 0) - 4 -
          6 * (if x ∈ H then 1 else 0) +
          ((G.neighborFinset x ∩ Z).card : ℤ)) :
    G.neighborFinset h ⊆ Z := by
  have heq := heq20 h
  rw [hDzero] at heq
  simp [hhH, hhB] at heq
  have hcard : (G.neighborFinset h ∩ Z).card =
      (G.neighborFinset h).card := by
    rw [G.card_neighborFinset_eq_degree, hdeg]
    omega
  exact Finset.inter_eq_left.mp (Finset.eq_of_subset_of_card_le
    Finset.inter_subset_left (by omega :
      (G.neighborFinset h).card ≤ (G.neighborFinset h ∩ Z).card))

/-- Equation (20) at the deleted articulation owner.  The owner is outside
the actual large shore and outside the high triple, while its defect boundary
into that shore has size two; consequently exactly six of its original
neighbors lie in the low set. -/
theorem orderNine_order27_owner_lowSet_degree_eq_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (owner : V) (B Z H : Finset V)
    (hownerB : owner ∉ B) (hownerH : owner ∉ H)
    (hdefectB :
      ((secondOrderDefectGraph G).neighborFinset owner ∩ B).card = 2)
    (heq20 : ∀ x : V,
      (((secondOrderDefectGraph G).neighborFinset x ∩ B).card : ℤ) =
        8 * (if x ∈ B then 1 else 0) - 4 -
          6 * (if x ∈ H then 1 else 0) +
          ((G.neighborFinset x ∩ Z).card : ℤ)) :
    (G.neighborFinset owner ∩ Z).card = 6 := by
  have h := heq20 owner
  rw [hdefectB] at h
  simp [hownerB, hownerH] at h
  omega

/-- Equation (20) at an ordinary exceptional point.  Its deleted-owner
defect neighborhood contributes seven points when it lies on the large
shore and zero otherwise, giving low-set degree three versus four. -/
theorem orderNine_order27_exceptional_lowSet_degree_eq_if
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : V) (B Z H : Finset V)
    (hyH : y ∉ H)
    (hdefectB :
      ((secondOrderDefectGraph G).neighborFinset y ∩ B).card =
        if y ∈ B then 7 else 0)
    (heq20 : ∀ x : V,
      (((secondOrderDefectGraph G).neighborFinset x ∩ B).card : ℤ) =
        8 * (if x ∈ B then 1 else 0) - 4 -
          6 * (if x ∈ H then 1 else 0) +
          ((G.neighborFinset x ∩ Z).card : ℤ)) :
    (G.neighborFinset y ∩ Z).card = if y ∈ B then 3 else 4 := by
  have h := heq20 y
  rw [hdefectB] at h
  simp [hyH] at h
  by_cases hyB : y ∈ B <;> simp [hyB] at h ⊢ <;> omega

/-- Equation (20) at an ordinary regular point whose full eight-point
defect neighborhood stays on its own shore.  Its low-set degree is four on
either side. -/
theorem orderNine_order27_regular_lowSet_degree_eq_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : V) (B Z H : Finset V)
    (hyH : y ∉ H)
    (hdefectB :
      ((secondOrderDefectGraph G).neighborFinset y ∩ B).card =
        if y ∈ B then 8 else 0)
    (heq20 : ∀ x : V,
      (((secondOrderDefectGraph G).neighborFinset x ∩ B).card : ℤ) =
        8 * (if x ∈ B then 1 else 0) - 4 -
          6 * (if x ∈ H then 1 else 0) +
          ((G.neighborFinset x ∩ Z).card : ℤ)) :
    (G.neighborFinset y ∩ Z).card = 4 := by
  have h := heq20 y
  rw [hdefectB] at h
  simp [hyH] at h
  by_cases hyB : y ∈ B <;> simp [hyB] at h <;> omega

/-- Graph-facing punctured-shore provider for equation (20) at an
exceptional original bin-zero owner-neighbor.  Its eighth defect neighbor is
the deleted owner, so it has seven defect neighbors on its own articulation
shore and none on the complementary shore. -/
theorem orderNine_order27_exceptional_owner_neighbors_lowSet_degree_eq_if_of_punctured_shores
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (owner : V) (U S T B Z H : Finset V)
    (hownerNotU : owner ∉ U)
    (hunion : S ∪ T = U) (hdisj : Disjoint S T)
    (hneighbors : ∀ x ∈ U,
      (secondOrderDefectGraph G).neighborFinset x ⊆ insert owner U)
    (hSclosed : ∀ x ∈ S,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ S)
    (hTclosed : ∀ x ∈ T,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ T)
    (hlocalU : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
        (secondOrderDefectGraph G).neighborFinset owner), y ∈ U)
    (hlocalOrd : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
        (secondOrderDefectGraph G).neighborFinset owner), y ∉ H)
    (hB : B = S)
    (heq20 : ∀ x : V,
      (((secondOrderDefectGraph G).neighborFinset x ∩ B).card : ℤ) =
        8 * (if x ∈ B then 1 else 0) - 4 -
          6 * (if x ∈ H then 1 else 0) +
          ((G.neighborFinset x ∩ Z).card : ℤ)) :
    ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
        (secondOrderDefectGraph G).neighborFinset owner),
      (G.neighborFinset y ∩ Z).card = if y ∈ B then 3 else 4 := by
  classical
  intro y hy
  let D := secondOrderDefectGraph G
  have hyParts := Finset.mem_inter.mp hy
  have hyLocal := Finset.mem_inter.mp hyParts.1
  have hyDadj : D.Adj y owner := by
    exact (D.adj_comm owner y).mp
      ((D.mem_neighborFinset owner y).mp hyParts.2)
  have hledger := squareOrderNine_lowIncidenceBin_pointwise_ledger
    G hfree hmin hcover hcard hyLocal.2
  have hyDegree : D.degree y = 8 := by
    simpa [D] using hledger.1
  have hdefectS :=
    neighbor_inter_shore_card_eq_if_of_complementary_closed_punctured_owner
      D owner U S T y hownerNotU hunion hdisj (hlocalU y hy)
        hyDadj hneighbors hSclosed hTclosed hyDegree
  have hdefectB : (D.neighborFinset y ∩ B).card =
      if y ∈ B then 7 else 0 := by simpa [hB] using hdefectS
  exact orderNine_order27_exceptional_lowSet_degree_eq_if
    G y B Z H (hlocalOrd y hy) (by simpa [D] using hdefectB) heq20

/-- Complementary punctured-shore provider for a regular original bin-zero
owner-neighbor.  Since it is not defect-adjacent to the deleted owner, the
punctured closure sharpens to genuine closure in `U`; all eight defect
neighbors stay on its own shore, and equation (20) gives `Z`-degree four. -/
theorem orderNine_order27_regular_owner_neighbors_lowSet_degree_four_of_punctured_shores
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (owner : V) (U S T B Z H : Finset V)
    (hunion : S ∪ T = U) (hdisj : Disjoint S T)
    (hneighborsPunctured : ∀ x ∈ U,
      (secondOrderDefectGraph G).neighborFinset x ⊆ insert owner U)
    (hSclosed : ∀ x ∈ S,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ S)
    (hTclosed : ∀ x ∈ T,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ T)
    (hlocalU : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0), y ∈ U)
    (hlocalOrd : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0), y ∉ H)
    (hB : B = S)
    (heq20 : ∀ x : V,
      (((secondOrderDefectGraph G).neighborFinset x ∩ B).card : ℤ) =
        8 * (if x ∈ B then 1 else 0) - 4 -
          6 * (if x ∈ H then 1 else 0) +
          ((G.neighborFinset x ∩ Z).card : ℤ)) :
    ∀ y ∈ (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset owner,
      (G.neighborFinset y ∩ Z).card = 4 := by
  classical
  intro y hy
  have hyParts := Finset.mem_sdiff.mp hy
  have hyLocal := Finset.mem_inter.mp hyParts.1
  have hyClosed : (secondOrderDefectGraph G).neighborFinset y ⊆ U := by
    intro z hz
    rcases Finset.mem_insert.mp
        (hneighborsPunctured y (hlocalU y hyParts.1) hz) with hzo | hzU
    · subst z
      have hAdj : (secondOrderDefectGraph G).Adj owner y :=
        ((secondOrderDefectGraph G).adj_comm y owner).mp
          (((secondOrderDefectGraph G).mem_neighborFinset y owner).mp hz)
      exact (hyParts.2
        (((secondOrderDefectGraph G).mem_neighborFinset owner y).mpr hAdj)).elim
    · exact hzU
  have hledger := squareOrderNine_lowIncidenceBin_pointwise_ledger
    G hfree hmin hcover hcard hyLocal.2
  have hyDegree : (secondOrderDefectGraph G).degree y = 8 := by
    simpa using hledger.1
  have hdefectS := neighbor_inter_shore_card_eq_if_of_complementary_closed
    (secondOrderDefectGraph G) U S T y hunion hdisj
      (hlocalU y hyParts.1) hyClosed hSclosed hTclosed hyDegree
  have hdefectB : ((secondOrderDefectGraph G).neighborFinset y ∩ B).card =
      if y ∈ B then 8 else 0 := by simpa [hB] using hdefectS
  exact orderNine_order27_regular_lowSet_degree_eq_four
    G y B Z H (hlocalOrd y hyParts.1) hdefectB heq20

/-- General form of the regular punctured-shore provider.  Any bin-zero
vertex in the articulation universe which is not defect-adjacent to the
deleted owner has all eight defect neighbors on its own shore, hence
equation (20) gives low-set degree four.  Unlike the owner-neighbor wrapper
above, this also applies to the five vertices of `W \ U_owner` in (22). -/
theorem orderNine_order27_binZero_lowSet_degree_four_of_punctured_shores
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (owner : V) (U S T B Z H : Finset V)
    (hunion : S ∪ T = U) (hdisj : Disjoint S T)
    (hneighborsPunctured : ∀ x ∈ U,
      (secondOrderDefectGraph G).neighborFinset x ⊆ insert owner U)
    (hSclosed : ∀ x ∈ S,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ S)
    (hTclosed : ∀ x ∈ T,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ T)
    (hB : B = S)
    (heq20 : ∀ x : V,
      (((secondOrderDefectGraph G).neighborFinset x ∩ B).card : ℤ) =
        8 * (if x ∈ B then 1 else 0) - 4 -
          6 * (if x ∈ H then 1 else 0) +
          ((G.neighborFinset x ∩ Z).card : ℤ))
    (y : V) (hyU : y ∈ U)
    (hyB0 : y ∈ squareOrderNineLowIncidenceBin G 0)
    (hyOwnerDefect : y ∉ (secondOrderDefectGraph G).neighborFinset owner)
    (hyH : y ∉ H) :
    (G.neighborFinset y ∩ Z).card = 4 := by
  have hyClosed : (secondOrderDefectGraph G).neighborFinset y ⊆ U := by
    intro z hz
    rcases Finset.mem_insert.mp
        (hneighborsPunctured y hyU hz) with hzo | hzU
    · subst z
      have hAdj : (secondOrderDefectGraph G).Adj owner y :=
        ((secondOrderDefectGraph G).adj_comm y owner).mp
          (((secondOrderDefectGraph G).mem_neighborFinset y owner).mp hz)
      exact (hyOwnerDefect
        (((secondOrderDefectGraph G).mem_neighborFinset owner y).mpr hAdj)).elim
    · exact hzU
  have hledger := squareOrderNine_lowIncidenceBin_pointwise_ledger
    G hfree hmin hcover hcard hyB0
  have hyDegree : (secondOrderDefectGraph G).degree y = 8 := by
    simpa using hledger.1
  have hdefectS := neighbor_inter_shore_card_eq_if_of_complementary_closed
    (secondOrderDefectGraph G) U S T y hunion hdisj hyU hyClosed
      hSclosed hTclosed hyDegree
  have hdefectB : ((secondOrderDefectGraph G).neighborFinset y ∩ B).card =
      if y ∈ B then 8 else 0 := by simpa [hB] using hdefectS
  exact orderNine_order27_regular_lowSet_degree_eq_four
    G y B Z H hyH hdefectB heq20

/-- General exceptional counterpart: any bin-zero articulation vertex
defect-adjacent to the deleted owner has seven remaining defect neighbors on
its own shore and none on the other, so equation (20) gives `Z`-degree three
or four. -/
theorem orderNine_order27_binZero_lowSet_degree_eq_if_of_punctured_owner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (owner : V) (U S T B Z H : Finset V)
    (hownerNotU : owner ∉ U)
    (hunion : S ∪ T = U) (hdisj : Disjoint S T)
    (hneighborsPunctured : ∀ x ∈ U,
      (secondOrderDefectGraph G).neighborFinset x ⊆ insert owner U)
    (hSclosed : ∀ x ∈ S,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ S)
    (hTclosed : ∀ x ∈ T,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ T)
    (hB : B = S)
    (heq20 : ∀ x : V,
      (((secondOrderDefectGraph G).neighborFinset x ∩ B).card : ℤ) =
        8 * (if x ∈ B then 1 else 0) - 4 -
          6 * (if x ∈ H then 1 else 0) +
          ((G.neighborFinset x ∩ Z).card : ℤ))
    (y : V) (hyU : y ∈ U)
    (hyB0 : y ∈ squareOrderNineLowIncidenceBin G 0)
    (hyOwnerDefect : y ∈ (secondOrderDefectGraph G).neighborFinset owner)
    (hyH : y ∉ H) :
    (G.neighborFinset y ∩ Z).card = if y ∈ B then 3 else 4 := by
  let D := secondOrderDefectGraph G
  have hyDadj : D.Adj y owner := by
    exact (D.adj_comm owner y).mp
      ((D.mem_neighborFinset owner y).mp hyOwnerDefect)
  have hledger := squareOrderNine_lowIncidenceBin_pointwise_ledger
    G hfree hmin hcover hcard hyB0
  have hyDegree : D.degree y = 8 := by
    simpa [D] using hledger.1
  have hdefectS :=
    neighbor_inter_shore_card_eq_if_of_complementary_closed_punctured_owner
      D owner U S T y hownerNotU hunion hdisj hyU hyDadj
        hneighborsPunctured hSclosed hTclosed hyDegree
  have hdefectB : (D.neighborFinset y ∩ B).card =
      if y ∈ B then 7 else 0 := by simpa [hB] using hdefectS
  exact orderNine_order27_exceptional_lowSet_degree_eq_if
    G y B Z H hyH (by simpa [D] using hdefectB) heq20

/-- Cardinal saturation behind the repaired placement argument: if a
six-point set is contained in the union of two disjoint three-point sets and
already contains the first one, it contains the second one as well. -/
theorem six_set_contains_other_three_of_partition
    {V : Type*} [DecidableEq V]
    (S K U : Finset V)
    (hS : S.card = 6) (hK : K.card = 3) (hU : U.card = 3)
    (hdisj : Disjoint K U) (hSsub : S ⊆ K ∪ U) :
    U ⊆ S := by
  have hKU : (K ∪ U).card = 6 := by
    rw [Finset.card_union_of_disjoint hdisj, hK, hU]
  have hSeq : S = K ∪ U :=
    Finset.eq_of_subset_of_card_le hSsub (by omega)
  rw [hSeq]
  exact Finset.subset_union_right

/-- Repaired graph-facing placement omitted in the prose before (21).
Evaluating (20) at the deleted owner gives six low-set neighbors.  The
second profile partitions its six ordinary neighbors into three bin-one and
three bin-zero points, so every original bin-zero neighbor belongs to `W`. -/
theorem orderNine_order27_owner_binZero_neighbors_subset_W
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    (owner : V) (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hownerDegree : G.degree owner = 9)
    (B Z : Finset V)
    (hownerB : owner ∉ B)
    (hdefectB :
      ((secondOrderDefectGraph G).neighborFinset owner ∩ B).card = 2)
    (hZsub : Z ⊆
      (Finset.univ : Finset V) \ squareOrderHighVertices G 9)
    (heq20 : ∀ x : V,
      (((secondOrderDefectGraph G).neighborFinset x ∩ B).card : ℤ) =
        8 * (if x ∈ B then 1 else 0) - 4 -
          6 * (if x ∈ squareOrderHighVertices G 9 then 1 else 0) +
          ((G.neighborFinset x ∩ Z).card : ℤ)) :
    G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ⊆
      Z ∩ squareOrderNineLowIncidenceBin G 0 := by
  classical
  let H := squareOrderHighVertices G 9
  let O := (Finset.univ : Finset V) \ H
  let S := G.neighborFinset owner ∩ Z
  let K := G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1
  let U := G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0
  have hownerH : owner ∉ H := by
    intro ho
    have hd10 := (Finset.mem_filter.mp ho).2
    omega
  have hScard : S.card = 6 :=
    orderNine_order27_owner_lowSet_degree_eq_six
      G owner B Z H hownerB hownerH hdefectB (by simpa [H] using heq20)
  have hKcard : K.card = 3 := by
    simpa [K] using
      squareOrderNine_threeHigh_secondProfile_binThree_original_binOne_neighbors
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 howner
  have hordinaryErase :=
    orderNine_binThree_owner_ordinary_erase_neighbor_card_eq_six
      G owner hownerDegree howner
  have hordinary : (G.neighborFinset owner ∩ O).card = 6 := by
    have heq : G.neighborFinset owner ∩ O.erase owner =
        G.neighborFinset owner ∩ O := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_erase]
      constructor
      · exact fun hz ↦ ⟨hz.1, hz.2.2⟩
      · intro hz
        refine ⟨hz.1, ?_, hz.2⟩
        intro hzo
        subst z
        exact G.loopless.irrefl owner
          ((G.mem_neighborFinset owner owner).mp hz.1)
    simpa [O, H, heq] using hordinaryErase
  have hpart :=
    orderNine_secondProfile_owner_neighbor_inter_ordinary_shore_bin_partition
      G hp hhigh hc2 hc3 howner O (by intro z hz; exact hz)
  have hKsubO : K ⊆ O := by
    intro z hz
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp hz).2).1
  have hUsubO : U ⊆ O := by
    intro z hz
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp hz).2).1
  have hKO : K ∩ O = K := Finset.inter_eq_left.mpr hKsubO
  have hUO : U ∩ O = U := Finset.inter_eq_left.mpr hUsubO
  have hKU : K ∪ U = G.neighborFinset owner ∩ O := by
    change G.neighborFinset owner ∩ O = (U ∩ O) ∪ (K ∩ O) at hpart
    rw [hUO, hKO] at hpart
    simpa [Finset.union_comm] using hpart.symm
  have hdisj : Disjoint K U := by
    rw [Finset.disjoint_left]
    intro z hzK hzU
    have hk1 := (Finset.mem_filter.mp (Finset.mem_inter.mp hzK).2).2
    have hk0 := (Finset.mem_filter.mp (Finset.mem_inter.mp hzU).2).2
    omega
  have hUcard : U.card = 3 := by
    have hc := Finset.card_union_of_disjoint hdisj
    rw [hKU, hordinary, hKcard] at hc
    omega
  have hSsub : S ⊆ K ∪ U := by
    intro z hzS
    have hz := Finset.mem_inter.mp hzS
    have hzO : z ∈ O := hZsub hz.2
    rw [hKU]
    exact Finset.mem_inter.mpr ⟨hz.1, hzO⟩
  have hUsubS := six_set_contains_other_three_of_partition
    S K U hScard hKcard hUcard hdisj hSsub
  intro z hzU
  exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (hUsubS hzU)).2,
    (Finset.mem_inter.mp hzU).2⟩

/-- Any positive high-incidence bin lies in a set containing every high
root's neighborhood. -/
theorem orderNine_positiveIncidenceBin_subset_of_high_neighbors_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : ℕ) (hi : 0 < i) (Z : Finset V)
    (hsaturated : ∀ h ∈ squareOrderHighVertices G 9,
      G.neighborFinset h ⊆ Z) :
    squareOrderNineLowIncidenceBin G i ⊆ Z := by
  intro z hz
  have hzCount := (Finset.mem_filter.mp hz).2
  have hpos : 0 < (G.neighborFinset z ∩
      squareOrderHighVertices G 9).card := by
    rw [show (G.neighborFinset z ∩ squareOrderHighVertices G 9).card = i
      by exact hzCount]
    exact hi
  obtain ⟨h, hh⟩ := Finset.card_pos.mp hpos
  have hhParts := Finset.mem_inter.mp hh
  exact hsaturated h hhParts.2
    ((G.mem_neighborFinset h z).mpr
      ((G.adj_comm z h).mp ((G.mem_neighborFinset z h).mp hhParts.1)))

/-- In the second three-high profile, a saturated 36-point ordinary set is
the owner, all 27 bin-one points, and exactly eight bin-zero points. -/
theorem orderNine_order27_lowSet_composition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (owner : V) (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (Z : Finset V)
    (hZsub : Z ⊆ (Finset.univ : Finset V) \ squareOrderHighVertices G 9)
    (hZcard : Z.card = 36)
    (hsaturated : ∀ h ∈ squareOrderHighVertices G 9,
      G.neighborFinset h ⊆ Z) :
    owner ∈ Z ∧
      squareOrderNineLowIncidenceBin G 1 ⊆ Z ∧
      Z = insert owner
        ((Z ∩ squareOrderNineLowIncidenceBin G 1) ∪
          (Z ∩ squareOrderNineLowIncidenceBin G 0)) ∧
      (Z ∩ squareOrderNineLowIncidenceBin G 0).card = 8 := by
  classical
  let k := squareOrderHighIncidenceCount G 9
  let P := Z ∩ squareOrderNineLowIncidenceBin G 1
  let W := Z ∩ squareOrderNineLowIncidenceBin G 0
  have hownerZ := orderNine_positiveIncidenceBin_subset_of_high_neighbors_subset
    G 3 (by omega) Z hsaturated howner
  have hB1sub := orderNine_positiveIncidenceBin_subset_of_high_neighbors_subset
    G 1 (by omega) Z hsaturated
  have hcap : ∀ z ∈ Z, z ≠ owner → k z ≤ 1 := by
    intro z hz hne
    exact orderNine_secondProfile_nonowner_ordinary_highIncidence_le_one
      G hp hhigh hc2 hc3 owner z howner (hZsub hz) hne
  have hpartition := lowSet_eq_insert_incidence_one_union_zero
    owner Z k hownerZ hcap
  have hfilter (i : ℕ) : Z.filter (fun z ↦ k z = i) =
      Z ∩ squareOrderNineLowIncidenceBin G i := by
    ext z
    constructor
    · intro hz
      have hpz := Finset.mem_filter.mp hz
      exact Finset.mem_inter.mpr ⟨hpz.1,
        Finset.mem_filter.mpr ⟨hZsub hpz.1, hpz.2⟩⟩
    · intro hz
      have hpz := Finset.mem_inter.mp hz
      exact Finset.mem_filter.mpr ⟨hpz.1,
        (Finset.mem_filter.mp hpz.2).2⟩
  rw [hfilter 1, hfilter 0] at hpartition
  change Z = insert owner (P ∪ W) at hpartition
  have hc1 : squareOrderNineHighIncidenceHistogram G 1 = 27 := by
    rcases squareOrderNine_highIncidence_profile_of_three_high
        G hcard hp hhigh with hfirst | hsecond
    · rw [hfirst.2.2.2.1] at hc3
      omega
    · exact hsecond.2.1
  have hB1card : (squareOrderNineLowIncidenceBin G 1).card = 27 := by
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 1) (by omega), hc1]
  have hP : P = squareOrderNineLowIncidenceBin G 1 := by
    exact Finset.inter_eq_right.mpr hB1sub
  have hownerNotP : owner ∉ P := by
    intro ho
    have hk1 := (Finset.mem_filter.mp (Finset.mem_inter.mp ho).2).2
    have hk3 := (Finset.mem_filter.mp howner).2
    omega
  have hownerNotW : owner ∉ W := by
    intro ho
    have hk0 := (Finset.mem_filter.mp (Finset.mem_inter.mp ho).2).2
    have hk3 := (Finset.mem_filter.mp howner).2
    omega
  have hPW : Disjoint P W := by
    rw [Finset.disjoint_left]
    intro z hzP hzW
    have hk1 := (Finset.mem_filter.mp (Finset.mem_inter.mp hzP).2).2
    have hk0 := (Finset.mem_filter.mp (Finset.mem_inter.mp hzW).2).2
    omega
  have hcardSplit : Z.card = 1 + P.card + W.card := by
    rw [hpartition, Finset.card_insert_of_notMem]
    · rw [Finset.card_union_of_disjoint hPW]
      omega
    · simp [hownerNotP, hownerNotW]
  refine ⟨hownerZ, hB1sub, hpartition, ?_⟩
  change W.card = 8
  rw [hZcard, hP, hB1card] at hcardSplit
  omega

/-- Set-theoretic form of audit (21), separating the owner, bin-one, and
bin-zero contributions to a bin-zero point's low-set degree. -/
theorem orderNine_binZero_W_degree_of_lowSet_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (owner y : V) (Z P W : Finset V)
    (hpartition : Z = insert owner (P ∪ W))
    (hownerP : owner ∉ P) (hownerW : owner ∉ W)
    (hPW : Disjoint P W)
    (hPdegree : (G.neighborFinset y ∩ P).card =
      if G.Adj y owner then 0 else 3) :
    (G.neighborFinset y ∩ Z).card =
      (G.neighborFinset y ∩ W).card +
        if G.Adj y owner then 1 else 3 := by
  classical
  by_cases hadj : G.Adj y owner
  · have hPempty : G.neighborFinset y ∩ P = ∅ := by
      rw [← Finset.card_eq_zero, hPdegree, if_pos hadj]
    have hset : G.neighborFinset y ∩ Z =
        insert owner (G.neighborFinset y ∩ W) := by
      ext x
      simp only [hpartition, Finset.mem_inter, Finset.mem_insert,
        Finset.mem_union]
      constructor
      · rintro ⟨hxy, rfl | hxP | hxW⟩
        · exact Or.inl rfl
        · have hm : x ∈ G.neighborFinset y ∩ P :=
            Finset.mem_inter.mpr ⟨hxy, hxP⟩
          rw [hPempty] at hm
          exact (Finset.notMem_empty x hm).elim
        · exact Or.inr ⟨hxy, hxW⟩
      · intro hu
        rcases hu with huo | huW
        · subst x
          exact ⟨(G.mem_neighborFinset y owner).mpr hadj, Or.inl rfl⟩
        · exact ⟨huW.1, Or.inr (Or.inr huW.2)⟩
    have hnot : owner ∉ G.neighborFinset y ∩ W := by
      intro hm
      exact hownerW (Finset.mem_inter.mp hm).2
    rw [hset, Finset.card_insert_of_notMem hnot, if_pos hadj]
  · have hownerNotNeighbor : owner ∉ G.neighborFinset y := by
      simpa using hadj
    have hset : G.neighborFinset y ∩ Z =
        (G.neighborFinset y ∩ P) ∪ (G.neighborFinset y ∩ W) := by
      ext x
      constructor
      · intro hx
        have hp := Finset.mem_inter.mp hx
        rw [hpartition] at hp
        rcases Finset.mem_insert.mp hp.2 with hxo | hxPW
        · subst x
          exact (hownerNotNeighbor hp.1).elim
        · rcases Finset.mem_union.mp hxPW with hxP | hxW
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hp.1, hxP⟩)
          · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hp.1, hxW⟩)
      · intro hx
        rcases Finset.mem_union.mp hx with hxP | hxW
        · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hxP).1, by
            rw [hpartition]
            exact Finset.mem_insert_of_mem
              (Finset.mem_union_left _ (Finset.mem_inter.mp hxP).2)⟩
        · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hxW).1, by
            rw [hpartition]
            exact Finset.mem_insert_of_mem
              (Finset.mem_union_right _ (Finset.mem_inter.mp hxW).2)⟩
    have hd : Disjoint (G.neighborFinset y ∩ P)
        (G.neighborFinset y ∩ W) :=
      Finset.disjoint_of_subset_right Finset.inter_subset_right
        (Finset.disjoint_of_subset_left Finset.inter_subset_right hPW)
    rw [hset, Finset.card_union_of_disjoint hd, hPdegree]
    simp [hadj]
    omega

/-- Graph/profile specialization of audit (21). -/
theorem orderNine_order27_binZero_W_degree_equation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    (owner : V) (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (Z W : Finset V)
    (hB1sub : squareOrderNineLowIncidenceBin G 1 ⊆ Z)
    (hW : W = Z ∩ squareOrderNineLowIncidenceBin G 0)
    (hpartition : Z = insert owner
      ((Z ∩ squareOrderNineLowIncidenceBin G 1) ∪ W)) :
    ∀ y ∈ W,
      (G.neighborFinset y ∩ Z).card =
        (G.neighborFinset y ∩ W).card +
          if G.Adj y owner then 1 else 3 := by
  classical
  intro y hyW
  let P := Z ∩ squareOrderNineLowIncidenceBin G 1
  have hyB0 : y ∈ squareOrderNineLowIncidenceBin G 0 := by
    rw [hW] at hyW
    exact (Finset.mem_inter.mp hyW).2
  have hownerP : owner ∉ P := by
    intro ho
    have hk1 := (Finset.mem_filter.mp (Finset.mem_inter.mp ho).2).2
    have hk3 := (Finset.mem_filter.mp howner).2
    omega
  have hownerW : owner ∉ W := by
    intro ho
    have ho' := ho
    rw [hW] at ho'
    have hk0 := (Finset.mem_filter.mp (Finset.mem_inter.mp ho').2).2
    have hk3 := (Finset.mem_filter.mp howner).2
    omega
  have hPW : Disjoint P W := by
    rw [Finset.disjoint_left]
    intro z hzP hzW
    have hzW' := hzW
    rw [hW] at hzW'
    have hk1 := (Finset.mem_filter.mp (Finset.mem_inter.mp hzP).2).2
    have hk0 := (Finset.mem_filter.mp (Finset.mem_inter.mp hzW').2).2
    omega
  have hPdegree : (G.neighborFinset y ∩ P).card =
      if G.Adj y owner then 0 else 3 := by
    have hraw := squareOrderNine_threeHigh_secondProfile_binZero_original_binOne_neighbors
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 howner hyB0
    have hPfull : P = squareOrderNineLowIncidenceBin G 1 :=
      Finset.inter_eq_right.mpr hB1sub
    simpa [P, hPfull] using hraw
  exact orderNine_binZero_W_degree_of_lowSet_partition
    G owner y Z P W (by simpa [P] using hpartition)
      hownerP hownerW hPW hPdegree

/-- The common right-hand budget in both cases of (22).  The five points of
`W \ U` are not adjacent to the owner, so (21) subtracts three from their
`Z`-degree.  A pointwise `Z`-degree cap four therefore leaves at most one
`W`-neighbor apiece. -/
theorem orderNine_order27_complement_W_degree_sum_le_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (owner : V) (Z U W : Finset V)
    (hWcard : W.card = 8) (hUcard : U.card = 3) (hUsub : U ⊆ W)
    (hUnbr : U = G.neighborFinset owner ∩ W)
    (heq21 : ∀ y ∈ W,
      (G.neighborFinset y ∩ Z).card =
        (G.neighborFinset y ∩ W).card +
          if G.Adj y owner then 1 else 3)
    (hZle : ∀ y ∈ W \ U, (G.neighborFinset y ∩ Z).card ≤ 4) :
    (∑ y ∈ W \ U, (G.neighborFinset y ∩ W).card) ≤ 5 := by
  classical
  let C := W \ U
  have hCcard : C.card = 5 := by
    dsimp [C]
    rw [Finset.card_sdiff_of_subset hUsub, hWcard, hUcard]
  have hnotAdj : ∀ y ∈ C, ¬ G.Adj y owner := by
    intro y hy hadj
    have hyW := (Finset.mem_sdiff.mp hy).1
    have hyU : y ∈ U := by
      rw [hUnbr]
      exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset owner y).mpr
          ((G.adj_comm y owner).mp hadj), hyW⟩
    exact (Finset.mem_sdiff.mp hy).2 hyU
  have hone : ∀ y ∈ C, (G.neighborFinset y ∩ W).card ≤ 1 := by
    intro y hy
    have he := heq21 y (Finset.mem_sdiff.mp hy).1
    have hz := hZle y hy
    simp [hnotAdj y hy] at he
    omega
  calc
    (∑ y ∈ W \ U, (G.neighborFinset y ∩ W).card) =
        ∑ y ∈ C, (G.neighborFinset y ∩ W).card := by rfl
    _ ≤ ∑ _y ∈ C, 1 := Finset.sum_le_sum fun y hy ↦ hone y hy
    _ = 5 := by simp [hCcard]

/-- Graph-facing assembly of the common right-hand budget in (22).  Every
point of `W \ U_owner` is bin zero and lies in the punctured articulation
universe.  If it were defect-adjacent to the deleted owner, the second-profile
identification of those defect neighbors with original triangle-free
neighbors would put it back in `U_owner`, a contradiction.  The generalized
punctured-shore provider therefore gives `Z`-degree four pointwise, and (21)
leaves at most one `W`-incidence at each of the five points. -/
theorem orderNine_order27_complement_W_degree_sum_le_five_of_punctured_shores
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (owner : V)
    (A S T B Z W Uowner H : Finset V)
    (hownerNotA : owner ∉ A)
    (hunion : S ∪ T = A) (hdisj : Disjoint S T)
    (hneighborsPunctured : ∀ x ∈ A,
      (secondOrderDefectGraph G).neighborFinset x ⊆ insert owner A)
    (hSclosed : ∀ x ∈ S,
      (secondOrderDefectGraph G).neighborFinset x ∩ A ⊆ S)
    (hTclosed : ∀ x ∈ T,
      (secondOrderDefectGraph G).neighborFinset x ∩ A ⊆ T)
    (hB : B = S)
    (heq20 : ∀ x : V,
      (((secondOrderDefectGraph G).neighborFinset x ∩ B).card : ℤ) =
        8 * (if x ∈ B then 1 else 0) - 4 -
          6 * (if x ∈ H then 1 else 0) +
          ((G.neighborFinset x ∩ Z).card : ℤ))
    (hWsubA : W ⊆ A)
    (hWsubB0 : W ⊆ squareOrderNineLowIncidenceBin G 0)
    (hWH : Disjoint W H)
    (hWcard : W.card = 8)
    (hUowner : Uowner = G.neighborFinset owner ∩ W)
    (hUcard : Uowner.card = 3)
    (heq21 : ∀ y ∈ W,
      (G.neighborFinset y ∩ Z).card =
        (G.neighborFinset y ∩ W).card +
          if G.Adj y owner then 1 else 3) :
    (∑ y ∈ W \ Uowner, (G.neighborFinset y ∩ W).card) ≤ 5 := by
  classical
  have hZle : ∀ y ∈ W \ Uowner,
      (G.neighborFinset y ∩ Z).card ≤ 4 := by
    intro y hy
    have hyW := (Finset.mem_sdiff.mp hy).1
    have hyH : y ∉ H := fun hyH ↦
      Finset.disjoint_left.mp hWH hyW hyH
    by_cases hyDefect :
        y ∈ (secondOrderDefectGraph G).neighborFinset owner
    · have hyDegree :=
        orderNine_order27_binZero_lowSet_degree_eq_if_of_punctured_owner
          G hfree hmin hcover hcard owner A S T B Z H hownerNotA
            hunion hdisj hneighborsPunctured hSclosed hTclosed hB heq20
            y (hWsubA hyW) (hWsubB0 hyW) hyDefect hyH
      by_cases hyB : y ∈ B <;> simp [hyB] at hyDegree ⊢ <;> omega
    · have hyDegree :=
        orderNine_order27_binZero_lowSet_degree_four_of_punctured_shores
          G hfree hmin hcover hcard owner A S T B Z H hunion hdisj
            hneighborsPunctured hSclosed hTclosed hB heq20 y (hWsubA hyW)
            (hWsubB0 hyW) hyDefect hyH
      omega
  have hUsub : Uowner ⊆ W := by
    rw [hUowner]
    exact Finset.inter_subset_right
  exact orderNine_order27_complement_W_degree_sum_le_five
    G owner Z Uowner W hWcard hUcard hUsub hUowner heq21 hZle

/-- In the three-edge branch all three original bin-zero owner-neighbors
are exceptional (defect-adjacent to the owner).  Consequently the FullType
split placing two exceptional points on the large shore places exactly two
of those three owner-neighbors there.  This is the graph-facing shore
placement needed by the left side of audit equation (22). -/
theorem orderNine_order27_threeEdge_owner_neighbors_large_card_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    (owner : V) (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (B : Finset V)
    (hloc : (G.induce (G.neighborSet owner)).edgeFinset.card = 3)
    (hExceptionalLarge :
      (((G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0) ∩
        (secondOrderDefectGraph G).neighborFinset owner) ∩ B).card = 2) :
    ((G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0) ∩ B).card = 2 := by
  classical
  let D := secondOrderDefectGraph G
  let U := G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0
  let E := U ∩ D.neighborFinset owner
  let R := U \ D.neighborFinset owner
  have hpackage := orderNine_secondProfile_owner_binZero_local_type_package
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  dsimp only at hpackage
  have hRcard : R.card = 0 := by
    rcases hpackage with hthree | hfour
    · exact hthree.2
    · omega
  have hRempty : R = ∅ := Finset.card_eq_zero.mp hRcard
  have hUsubD : U ⊆ D.neighborFinset owner := by
    intro y hyU
    by_contra hyD
    have hyR : y ∈ R := Finset.mem_sdiff.mpr ⟨hyU, hyD⟩
    rw [hRempty] at hyR
    exact Finset.notMem_empty y hyR
  have hEU : E = U := Finset.inter_eq_left.mpr hUsubD
  change (U ∩ B).card = 2
  change (E ∩ B).card = 2 at hExceptionalLarge
  simpa [hEU] using hExceptionalLarge

/-- Three-edge left-hand arithmetic: among three owner-neighbors, two on
the large shore have `W`-degree two and the remaining point has degree
three. -/
theorem orderNine_order27_threeEdge_W_degree_sum_eq_seven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U B W : Finset V)
    (hUcard : U.card = 3) (hUBcard : (U ∩ B).card = 2)
    (hdegree : ∀ u ∈ U,
      (G.neighborFinset u ∩ W).card = if u ∈ B then 2 else 3) :
    (∑ u ∈ U, (G.neighborFinset u ∩ W).card) = 7 := by
  classical
  let L := U ∩ B
  let C := U \ B
  have hLC : Disjoint L C := by
    rw [Finset.disjoint_left]
    intro u huL huC
    exact (Finset.mem_sdiff.mp huC).2 (Finset.mem_inter.mp huL).2
  have hcover : L ∪ C = U := by
    ext u
    simp only [L, C, Finset.mem_union, Finset.mem_inter,
      Finset.mem_sdiff]
    constructor
    · rintro (hu | hu) <;> exact hu.1
    · intro hu
      by_cases huB : u ∈ B
      · exact Or.inl ⟨hu, huB⟩
      · exact Or.inr ⟨hu, huB⟩
  have hCcard : C.card = 1 := by
    have hs := Finset.card_sdiff_add_card_inter U B
    change C.card + L.card = U.card at hs
    rw [hUcard, show L.card = 2 by simpa [L] using hUBcard] at hs
    omega
  rw [← hcover, Finset.sum_union hLC]
  have hLsum : (∑ u ∈ L, (G.neighborFinset u ∩ W).card) = 4 := by
    calc
      (∑ u ∈ L, (G.neighborFinset u ∩ W).card) = ∑ _u ∈ L, 2 := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [hdegree u (Finset.mem_inter.mp hu).1,
          if_pos (Finset.mem_inter.mp hu).2]
      _ = 4 := by simp [show L.card = 2 by simpa [L] using hUBcard]
  have hCsum : (∑ u ∈ C, (G.neighborFinset u ∩ W).card) = 3 := by
    calc
      (∑ u ∈ C, (G.neighborFinset u ∩ W).card) = ∑ _u ∈ C, 3 := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [hdegree u (Finset.mem_sdiff.mp hu).1,
          if_neg (Finset.mem_sdiff.mp hu).2]
      _ = 3 := by simp [hCcard]
  omega

/-- Four-edge left-hand arithmetic: the exceptional point contributes at
least two `W`-incidences and the two regular points contribute three each. -/
theorem orderNine_order27_fourEdge_W_degree_sum_ge_eight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (E R U W : Finset V)
    (hEcard : E.card = 1) (hRcard : R.card = 2)
    (hdisj : Disjoint E R) (hU : U = E ∪ R)
    (hEdegree : ∀ e ∈ E, 2 ≤ (G.neighborFinset e ∩ W).card)
    (hRdegree : ∀ r ∈ R, (G.neighborFinset r ∩ W).card = 3) :
    8 ≤ ∑ u ∈ U, (G.neighborFinset u ∩ W).card := by
  rw [hU, Finset.sum_union hdisj]
  have hEsum : 2 ≤ ∑ e ∈ E, (G.neighborFinset e ∩ W).card := by
    calc
      2 = ∑ _e ∈ E, 2 := by simp [hEcard]
      _ ≤ ∑ e ∈ E, (G.neighborFinset e ∩ W).card :=
        Finset.sum_le_sum fun e he ↦ hEdegree e he
  have hRsum : (∑ r ∈ R, (G.neighborFinset r ∩ W).card) = 6 := by
    calc
      (∑ r ∈ R, (G.neighborFinset r ∩ W).card) = ∑ _r ∈ R, 3 := by
        apply Finset.sum_congr rfl
        exact fun r hr ↦ hRdegree r hr
      _ = 6 := by simp [hRcard]
  omega

/-- The exact internal incidence count supplied by the four-edge local
geometry: the exceptional singleton avoids the regular pair, and the two
regular points form one edge. -/
theorem orderNine_order27_fourEdge_internal_degree_sum_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (E R U : Finset V)
    (hEcard : E.card = 1) (hRcard : R.card = 2)
    (hdisj : Disjoint E R) (hU : U = E ∪ R)
    (hER : ∀ e ∈ E, ∀ r ∈ R, ¬ G.Adj e r)
    (hRR : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → G.Adj r s) :
    (∑ u ∈ U, (G.neighborFinset u ∩ U).card) = 2 := by
  classical
  have hEzero : ∀ e ∈ E, (G.neighborFinset e ∩ U).card = 0 := by
    intro e he
    rw [Finset.card_eq_zero]
    ext z
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro hez hzU
    rw [hU] at hzU
    rcases Finset.mem_union.mp hzU with hzE | hzR
    · have hne : z ≠ e := by
        intro h
        subst z
        exact G.loopless.irrefl e ((G.mem_neighborFinset e e).mp hez)
      have heq : z = e := Finset.card_le_one.mp (by rw [hEcard]) z hzE e he
      exact hne heq
    · exact hER e he z hzR ((G.mem_neighborFinset e z).mp hez)
  have hRone : ∀ r ∈ R, (G.neighborFinset r ∩ U).card = 1 := by
    intro r hr
    obtain ⟨s, hs, hsr⟩ := Finset.exists_mem_ne (by rw [hRcard]; omega) r
    have hset : G.neighborFinset r ∩ U = {s} := by
      ext z
      constructor
      · intro hz
        have hzParts := Finset.mem_inter.mp hz
        rw [hU] at hzParts
        rcases Finset.mem_union.mp hzParts.2 with hzE | hzR
        · exact (hER z hzE r hr
            ((G.adj_comm r z).mp
              ((G.mem_neighborFinset r z).mp hzParts.1))).elim
        · have hzr : z ≠ r := by
            intro h
            subst z
            exact G.loopless.irrefl r
              ((G.mem_neighborFinset r r).mp hzParts.1)
          have htwo := Finset.card_le_one.mp (by
            rw [Finset.card_erase_of_mem hr, hRcard])
          have hzErase : z ∈ R.erase r := Finset.mem_erase.mpr ⟨hzr, hzR⟩
          have hsErase : s ∈ R.erase r := Finset.mem_erase.mpr ⟨hsr, hs⟩
          exact Finset.mem_singleton.mpr (htwo z hzErase s hsErase)
      · intro hz
        have hzs : z = s := Finset.mem_singleton.mp hz
        subst z
        exact Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset r s).mpr (hRR r hr s hs (Ne.symm hsr)),
            by rw [hU]; exact Finset.mem_union_right E hs⟩
    rw [hset]
    simp
  rw [hU, Finset.sum_union hdisj]
  have hEsum : (∑ e ∈ E, (G.neighborFinset e ∩ (E ∪ R)).card) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    simpa [hU] using hEzero e he
  have hRsum : (∑ r ∈ R, (G.neighborFinset r ∩ (E ∪ R)).card) = 2 := by
    calc
      (∑ r ∈ R, (G.neighborFinset r ∩ (E ∪ R)).card) = ∑ _r ∈ R, 1 := by
        apply Finset.sum_congr rfl
        intro r hr
        simpa [hU] using hRone r hr
      _ = 2 := by simp [hRcard]
  omega

/-- Cross-incidence handshake, proved by swapping the two endpoints. -/
theorem sum_neighbor_inter_card_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    (∑ a ∈ A, (G.neighborFinset a ∩ B).card) =
      ∑ b ∈ B, (G.neighborFinset b ∩ A).card := by
  classical
  let L := A.sigma fun a => G.neighborFinset a ∩ B
  let R := B.sigma fun b => G.neighborFinset b ∩ A
  have hcard : (A.sigma fun a => G.neighborFinset a ∩ B).card =
      (B.sigma fun b => G.neighborFinset b ∩ A).card := by
    refine Finset.card_bij
      (s := A.sigma fun a => G.neighborFinset a ∩ B)
      (t := B.sigma fun b => G.neighborFinset b ∩ A)
      (fun p : Sigma fun _ : V => V => fun _ => ⟨p.2, p.1⟩) ?_ ?_ ?_
    · intro p hp
      have hp' := Finset.mem_sigma.mp hp
      exact Finset.mem_sigma.mpr ⟨(Finset.mem_inter.mp hp'.2).2,
        Finset.mem_inter.mpr ⟨
          (G.mem_neighborFinset p.2 p.1).mpr
            ((G.adj_comm p.1 p.2).mp
              ((G.mem_neighborFinset p.1 p.2).mp
                (Finset.mem_inter.mp hp'.2).1)), hp'.1⟩⟩
    · intro p₁ hp₁ p₂ hp₂ heq
      have hs := congrArg
        (fun q : Sigma fun _ : V => V =>
          (⟨q.2, q.1⟩ : Sigma fun _ : V => V)) heq
      simpa using hs
    · intro q hq
      refine ⟨(⟨q.2, q.1⟩ : Sigma fun _ : V => V), ?_, ?_⟩
      have hq' := Finset.mem_sigma.mp hq
      exact Finset.mem_sigma.mpr ⟨(Finset.mem_inter.mp hq'.2).2,
        Finset.mem_inter.mpr ⟨
          (G.mem_neighborFinset q.2 q.1).mpr
            ((G.adj_comm q.1 q.2).mp
              ((G.mem_neighborFinset q.1 q.2).mp
                (Finset.mem_inter.mp hq'.2).1)), hq'.1⟩⟩
      · cases q
        rfl
  simpa [L, R, Finset.card_sigma] using hcard

/-- An independent subset sends no more incidences into an ambient set than
its complement receives. -/
theorem sum_neighbor_inter_card_le_complement_of_independent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W : Finset V) (hUsub : U ⊆ W)
    (hind : ∀ u ∈ U, (G.neighborFinset u ∩ U).card = 0) :
    (∑ u ∈ U, (G.neighborFinset u ∩ W).card) ≤
      ∑ w ∈ W \ U, (G.neighborFinset w ∩ W).card := by
  classical
  let C := W \ U
  have hleft : (∑ u ∈ U, (G.neighborFinset u ∩ W).card) =
      ∑ u ∈ U, (G.neighborFinset u ∩ C).card := by
    apply Finset.sum_congr rfl
    intro u hu
    congr 1
    ext x
    constructor
    · intro hx
      have hp := Finset.mem_inter.mp hx
      refine Finset.mem_inter.mpr ⟨hp.1, Finset.mem_sdiff.mpr ⟨hp.2, ?_⟩⟩
      intro hxU
      have hm : x ∈ G.neighborFinset u ∩ U :=
        Finset.mem_inter.mpr ⟨hp.1, hxU⟩
      have hempty := Finset.card_eq_zero.mp (hind u hu)
      rw [hempty] at hm
      exact Finset.notMem_empty x hm
    · intro hx
      have hp := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr ⟨hp.1, (Finset.mem_sdiff.mp hp.2).1⟩
  have hcross := sum_neighbor_inter_card_comm G U C
  rw [hleft, hcross]
  apply Finset.sum_le_sum
  intro w hw
  exact Finset.card_le_card (by
    intro x hx
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
      hUsub (Finset.mem_inter.mp hx).2⟩)

/-- Three-edge arithmetic terminal in (22). -/
theorem false_of_orderNine_order27_threeEdge_handshake
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W : Finset V) (hUsub : U ⊆ W)
    (hind : ∀ u ∈ U, (G.neighborFinset u ∩ U).card = 0)
    (hleft : (∑ u ∈ U, (G.neighborFinset u ∩ W).card) = 7)
    (hright : (∑ w ∈ W \ U, (G.neighborFinset w ∩ W).card) ≤ 5) :
    False := by
  have hle := sum_neighbor_inter_card_le_complement_of_independent
    G U W hUsub hind
  omega

/-- General complement handshake with the twice-counted internal incidence
term left explicit. -/
theorem sum_neighbor_inter_card_le_internal_add_complement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W : Finset V) (hUsub : U ⊆ W) :
    (∑ u ∈ U, (G.neighborFinset u ∩ W).card) ≤
      (∑ u ∈ U, (G.neighborFinset u ∩ U).card) +
        ∑ w ∈ W \ U, (G.neighborFinset w ∩ W).card := by
  classical
  let C := W \ U
  have hsplit : (∑ u ∈ U, (G.neighborFinset u ∩ W).card) =
      (∑ u ∈ U, (G.neighborFinset u ∩ U).card) +
        ∑ u ∈ U, (G.neighborFinset u ∩ C).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    have hset : G.neighborFinset u ∩ W =
        (G.neighborFinset u ∩ U) ∪ (G.neighborFinset u ∩ C) := by
      ext x
      constructor
      · intro hx
        have hp := Finset.mem_inter.mp hx
        by_cases hxU : x ∈ U
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hp.1, hxU⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hp.1,
            Finset.mem_sdiff.mpr ⟨hp.2, hxU⟩⟩)
      · intro hx
        rcases Finset.mem_union.mp hx with hxU | hxC
        · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hxU).1,
            hUsub (Finset.mem_inter.mp hxU).2⟩
        · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hxC).1,
            (Finset.mem_sdiff.mp (Finset.mem_inter.mp hxC).2).1⟩
    have hd : Disjoint (G.neighborFinset u ∩ U)
        (G.neighborFinset u ∩ C) := by
      rw [Finset.disjoint_left]
      intro x hxU hxC
      exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hxC).2).2
        (Finset.mem_inter.mp hxU).2
    rw [hset, Finset.card_union_of_disjoint hd]
  have hcross := sum_neighbor_inter_card_comm G U C
  have hcrossLe : (∑ u ∈ U, (G.neighborFinset u ∩ C).card) ≤
      ∑ w ∈ C, (G.neighborFinset w ∩ W).card := by
    rw [hcross]
    apply Finset.sum_le_sum
    intro w hw
    exact Finset.card_le_card (by
      intro x hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
        hUsub (Finset.mem_inter.mp hx).2⟩)
  rw [hsplit]
  exact Nat.add_le_add_left hcrossLe _

/-- Four-edge arithmetic terminal in (22): one internal edge contributes
two incidences, so total degree at least eight forces at least six crossing
incidences, exceeding the complement budget five. -/
theorem false_of_orderNine_order27_fourEdge_handshake
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W : Finset V) (hUsub : U ⊆ W)
    (hleft : 8 ≤ ∑ u ∈ U, (G.neighborFinset u ∩ W).card)
    (hinternal : (∑ u ∈ U, (G.neighborFinset u ∩ U).card) = 2)
    (hright : (∑ w ∈ W \ U, (G.neighborFinset w ∩ W).card) ≤ 5) :
    False := by
  have hle := sum_neighbor_inter_card_le_internal_add_complement
    G U W hUsub
  omega

/-- Final graph-facing dispatcher for audit (22).  The punctured articulation
data supplies the common five-point budget.  In the three-edge branch all
three owner-neighbors are exceptional and independent, with shore split
`2+1`, giving left mass seven.  In the four-edge branch the local set is one
exceptional point plus an adjacent regular pair, giving left mass at least
eight and internal mass exactly two.  Both contradict the common budget
five. -/
theorem false_of_orderNine_order27_handshake_of_punctured_articulation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    (owner : V) (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (A S T B Z W H : Finset V)
    (hownerNotA : owner ∉ A)
    (hunion : S ∪ T = A) (hdisj : Disjoint S T)
    (hneighborsPunctured : ∀ x ∈ A,
      (secondOrderDefectGraph G).neighborFinset x ⊆ insert owner A)
    (hSclosed : ∀ x ∈ S,
      (secondOrderDefectGraph G).neighborFinset x ∩ A ⊆ S)
    (hTclosed : ∀ x ∈ T,
      (secondOrderDefectGraph G).neighborFinset x ∩ A ⊆ T)
    (hB : B = S)
    (heq20 : ∀ x : V,
      (((secondOrderDefectGraph G).neighborFinset x ∩ B).card : ℤ) =
        8 * (if x ∈ B then 1 else 0) - 4 -
          6 * (if x ∈ H then 1 else 0) +
          ((G.neighborFinset x ∩ Z).card : ℤ))
    (hWsubA : W ⊆ A)
    (hWsubB0 : W ⊆ squareOrderNineLowIncidenceBin G 0)
    (hWH : Disjoint W H)
    (hWcard : W.card = 8)
    (hUeq : G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 =
      G.neighborFinset owner ∩ W)
    (hUcard :
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0).card = 3)
    (heq21 : ∀ y ∈ W,
      (G.neighborFinset y ∩ Z).card =
        (G.neighborFinset y ∩ W).card +
          if G.Adj y owner then 1 else 3)
    (hownerSmall : (G.neighborFinset owner ∩ T).card = 1)
    (hExceptionalLarge :
      (((secondOrderDefectGraph G).neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0) ∩ B).card = 2)
    (hlocAlt : (G.induce (G.neighborSet owner)).edgeFinset.card = 3 ∨
      (G.induce (G.neighborSet owner)).edgeFinset.card = 4) : False := by
  classical
  let U := G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0
  let E := U ∩ (secondOrderDefectGraph G).neighborFinset owner
  let R := U \ (secondOrderDefectGraph G).neighborFinset owner
  have hright :
      (∑ y ∈ W \ U, (G.neighborFinset y ∩ W).card) ≤ 5 := by
    apply orderNine_order27_complement_W_degree_sum_le_five_of_punctured_shores
      G hfree hmin hcover hcard owner A S T B Z W U H hownerNotA
        hunion hdisj hneighborsPunctured hSclosed hTclosed hB heq20
        hWsubA hWsubB0 hWH hWcard
    · simpa [U] using hUeq
    · simpa [U] using hUcard
    · exact heq21
  rcases hlocAlt with hthree | hfour
  · have hpackage := orderNine_secondProfile_owner_binZero_local_type_package
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
    dsimp only at hpackage
    have hRempty : R = ∅ := by
      apply Finset.card_eq_zero.mp
      rcases hpackage with hp3 | hp4
      · simpa [R, U] using hp3.2
      · omega
    have hUsubD : U ⊆ (secondOrderDefectGraph G).neighborFinset owner := by
      intro y hyU
      by_contra hyD
      have hyR : y ∈ R := Finset.mem_sdiff.mpr ⟨hyU, hyD⟩
      rw [hRempty] at hyR
      exact Finset.notMem_empty y hyR
    have hUBcard : (U ∩ B).card = 2 := by
      have hUsubA : U ⊆ A := by
        intro u hu
        have huW : u ∈ W := by
          have : u ∈ G.neighborFinset owner ∩ W := by rw [← hUeq]; exact hu
          exact (Finset.mem_inter.mp this).2
        exact hWsubA huW
      have hsplit : (U ∩ B).card + (U ∩ T).card = U.card := by
        have hset : (U ∩ B) ∪ (U ∩ T) = U := by
          ext u
          constructor
          · intro hu
            rcases Finset.mem_union.mp hu with hu | hu
            · exact (Finset.mem_inter.mp hu).1
            · exact (Finset.mem_inter.mp hu).1
          · intro hu
            have huA := hUsubA hu
            rw [← hunion] at huA
            rcases Finset.mem_union.mp huA with huS | huT
            · exact Finset.mem_union_left _
                (Finset.mem_inter.mpr ⟨hu, by simpa [hB] using huS⟩)
            · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hu, huT⟩)
        have hd : Disjoint (U ∩ B) (U ∩ T) := by
          rw [Finset.disjoint_left]
          intro u huB huT
          exact Finset.disjoint_left.mp hdisj
            (by simpa [hB] using (Finset.mem_inter.mp huB).2)
            (Finset.mem_inter.mp huT).2
        rw [← Finset.card_union_of_disjoint hd, hset]
      have hUTle : (U ∩ T).card ≤ 1 := by
        calc
          (U ∩ T).card ≤ (G.neighborFinset owner ∩ T).card :=
            Finset.card_le_card (by
              intro u hu
              exact Finset.mem_inter.mpr
                ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hu).1).1,
                  (Finset.mem_inter.mp hu).2⟩)
          _ = 1 := hownerSmall
      have hUBle : (U ∩ B).card ≤ 2 := by
        calc
          (U ∩ B).card ≤
              (((secondOrderDefectGraph G).neighborFinset owner ∩
                squareOrderNineLowIncidenceBin G 0) ∩ B).card :=
            Finset.card_le_card (by
              intro u hu
              have huU := (Finset.mem_inter.mp hu).1
              exact Finset.mem_inter.mpr
                ⟨Finset.mem_inter.mpr
                  ⟨hUsubD huU, (Finset.mem_inter.mp huU).2⟩,
                  (Finset.mem_inter.mp hu).2⟩)
          _ = 2 := hExceptionalLarge
      have hUc : U.card = 3 := by simpa [U] using hUcard
      omega
    have hdegree : ∀ u ∈ U,
        (G.neighborFinset u ∩ W).card = if u ∈ B then 2 else 3 := by
      intro u hu
      have huW : u ∈ W := by
        have hu' : u ∈ G.neighborFinset owner ∩ W := by
          rw [← hUeq]
          exact hu
        exact (Finset.mem_inter.mp hu').2
      have huZ :=
        orderNine_order27_binZero_lowSet_degree_eq_if_of_punctured_owner
          G hfree hmin hcover hcard owner A S T B Z H hownerNotA
            hunion hdisj hneighborsPunctured hSclosed hTclosed hB heq20
            u (hWsubA huW) (Finset.mem_inter.mp hu).2 (hUsubD hu)
            (fun huH ↦ Finset.disjoint_left.mp hWH huW huH)
      have h21 := heq21 u huW
      have huAdj : G.Adj u owner := (G.adj_comm owner u).mp
        ((G.mem_neighborFinset owner u).mp (Finset.mem_inter.mp hu).1)
      by_cases huB : u ∈ B <;>
        simp [huB, huAdj] at huZ h21 ⊢ <;> omega
    have hind : ∀ u ∈ U, (G.neighborFinset u ∩ U).card = 0 := by
      intro u hu
      rw [Finset.card_eq_zero]
      ext v
      constructor
      · intro hv
        have hvp := Finset.mem_inter.mp hv
        have huExceptional : u ∈
            G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
              (secondOrderDefectGraph G).neighborFinset owner :=
          Finset.mem_inter.mpr ⟨hu, hUsubD hu⟩
        have hvOwner : G.Adj owner v :=
          (G.mem_neighborFinset owner v).mp (Finset.mem_inter.mp hvp.2).1
        exact (orderNine_secondProfile_owner_defect_binZero_avoids_owner_neighbors
          G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
            huExceptional hvOwner
              ((G.mem_neighborFinset u v).mp hvp.1)).elim
      · simp
    have hleft := orderNine_order27_threeEdge_W_degree_sum_eq_seven
      G U B W (by simpa [U] using hUcard) hUBcard hdegree
    have hUsubW : U ⊆ W := by
      intro u hu
      have : u ∈ G.neighborFinset owner ∩ W := by rw [← hUeq]; exact hu
      exact (Finset.mem_inter.mp this).2
    have hle := sum_neighbor_inter_card_le_complement_of_independent
      G U W hUsubW hind
    omega
  · have hgeom := orderNine_secondProfile_owner_four_edge_binZero_partition
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner hfour
    dsimp only at hgeom
    have hERdisj : Disjoint E R := by
      rw [Finset.disjoint_left]
      intro x hxE hxR
      exact (Finset.mem_sdiff.mp hxR).2 (Finset.mem_inter.mp hxE).2
    have hUunion : U = E ∪ R := by
      ext x
      constructor
      · intro hx
        by_cases hxd : x ∈ (secondOrderDefectGraph G).neighborFinset owner
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hxd⟩)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hxd⟩)
      · intro hx
        rcases Finset.mem_union.mp hx with hxE | hxR
        · exact (Finset.mem_inter.mp hxE).1
        · exact (Finset.mem_sdiff.mp hxR).1
    have hEdegree : ∀ e ∈ E, 2 ≤ (G.neighborFinset e ∩ W).card := by
      intro e he
      have heU := (Finset.mem_inter.mp he).1
      have heW : e ∈ W := by
        have : e ∈ G.neighborFinset owner ∩ W := by rw [← hUeq]; exact heU
        exact (Finset.mem_inter.mp this).2
      have heZ :=
        orderNine_order27_binZero_lowSet_degree_eq_if_of_punctured_owner
          G hfree hmin hcover hcard owner A S T B Z H hownerNotA
            hunion hdisj hneighborsPunctured hSclosed hTclosed hB heq20
            e (hWsubA heW) (Finset.mem_inter.mp heU).2
            (Finset.mem_inter.mp he).2
            (fun heH ↦ Finset.disjoint_left.mp hWH heW heH)
      have h21 := heq21 e heW
      have heAdj : G.Adj e owner := (G.adj_comm owner e).mp
        ((G.mem_neighborFinset owner e).mp (Finset.mem_inter.mp heU).1)
      by_cases heB : e ∈ B <;> simp [heB, heAdj] at heZ h21 <;> omega
    have hRdegree : ∀ r ∈ R, (G.neighborFinset r ∩ W).card = 3 := by
      intro r hr
      have hrU := (Finset.mem_sdiff.mp hr).1
      have hrW : r ∈ W := by
        have : r ∈ G.neighborFinset owner ∩ W := by rw [← hUeq]; exact hrU
        exact (Finset.mem_inter.mp this).2
      have hrZ := orderNine_order27_binZero_lowSet_degree_four_of_punctured_shores
        G hfree hmin hcover hcard owner A S T B Z H hunion hdisj
          hneighborsPunctured hSclosed hTclosed hB heq20 r (hWsubA hrW)
          (Finset.mem_inter.mp hrU).2 (Finset.mem_sdiff.mp hr).2
          (fun hrH ↦ Finset.disjoint_left.mp hWH hrW hrH)
      have h21 := heq21 r hrW
      have hrAdj : G.Adj r owner := (G.adj_comm owner r).mp
        ((G.mem_neighborFinset owner r).mp (Finset.mem_inter.mp hrU).1)
      simp [hrAdj] at h21
      omega
    have hleft := orderNine_order27_fourEdge_W_degree_sum_ge_eight
      G E R U W (by simpa [E, U] using hgeom.1)
        (by simpa [R, U] using hgeom.2.1) hERdisj hUunion hEdegree hRdegree
    have hinternal := orderNine_order27_fourEdge_internal_degree_sum_eq_two
      G E R U (by simpa [E, U] using hgeom.1)
        (by simpa [R, U] using hgeom.2.1) hERdisj hUunion
        (by simpa [E, R, U] using hgeom.2.2.1)
        (by simpa [E, R, U] using hgeom.2.2.2)
    have hUsubW : U ⊆ W := by
      intro u hu
      have : u ∈ G.neighborFinset owner ∩ W := by rw [← hUeq]; exact hu
      exact (Finset.mem_inter.mp this).2
    exact false_of_orderNine_order27_fourEdge_handshake
      G U W hUsubW hleft hinternal hright

/-- The oriented `(27,50)` branch exactly as returned by the deleted-owner
articulation capstone is impossible.  This wrapper constructs equation (20),
the saturated 36-point low set, equation (21), and every punctured-closure
input consumed by the handshake dispatcher. -/
theorem false_of_orderNine_order27_oriented_articulation_output
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃) (h₂₃ : h₂ ≠ h₃)
    (hH : squareOrderHighVertices G 9 = {h₁, h₂, h₃})
    (owner : V) (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (S T : Finset V)
    (hunion : S ∪ T =
      ((Finset.univ : Finset V) \ squareOrderHighVertices G 9).erase owner)
    (hdisj : Disjoint S T)
    (hScard : S.card = 27) (hTcard : T.card = 50)
    (hfull : orderNineArticulationSmallShoreFullType G
      ((secondOrderDefectGraph G).neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0) h₁ h₂ h₃ S)
    (hSclosed : ∀ x ∈ S, (secondOrderDefectGraph G).neighborFinset x ∩
      ((Finset.univ : Finset V) \ squareOrderHighVertices G 9).erase owner ⊆ S)
    (hTclosed : ∀ x ∈ T, (secondOrderDefectGraph G).neighborFinset x ∩
      ((Finset.univ : Finset V) \ squareOrderHighVertices G 9).erase owner ⊆ T)
    (hTboundary : (∑ x ∈ T,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ T)).card) =
      (((secondOrderDefectGraph G).neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0) ∩ T).card)
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ x ∈ ({h₁, h₂, h₃} : Finset V), G.degree x = 10)
    (hhighIndependent : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      Disjoint (G.neighborFinset h) ({h₁, h₂, h₃} : Finset V))
    (hdefectHighIsolated : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      (secondOrderDefectGraph G).neighborFinset h = ∅) : False := by
  classical
  let H : Finset V := {h₁, h₂, h₃}
  let O := (Finset.univ : Finset V) \ squareOrderHighVertices G 9
  let U := O.erase owner
  let E := (secondOrderDefectGraph G).neighborFinset owner ∩
    squareOrderNineLowIncidenceBin G 0
  let Z := orderNineOrdinaryLowSet G h₁ h₂ h₃ T 5
  let W := Z ∩ squareOrderNineLowIncidenceBin G 0
  have hownerO : owner ∈ (Finset.univ : Finset V) \ H := by
    have ho := (Finset.mem_filter.mp howner).1
    simpa [H, hH] using ho
  have hownerNotU : owner ∉ U := Finset.notMem_erase owner O
  have hEinfo := squareOrderNine_threeHigh_secondProfile_owner_defect_neighbors
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  dsimp only at hEinfo
  have hEcard : E.card = 5 := by simpa [E] using hEinfo.1
  have hEsub : E ⊆ U := by
    intro x hx
    have hxB0 := (Finset.mem_inter.mp hx).2
    have hxO := (Finset.mem_filter.mp hxB0).1
    have hxne : x ≠ owner := by
      intro hxo
      subst x
      exact (secondOrderDefectGraph G).loopless.irrefl owner
        ((secondOrderDefectGraph G).mem_neighborFinset owner owner |>.mp
          (Finset.mem_inter.mp hx).1)
    exact Finset.mem_erase.mpr ⟨hxne, hxO⟩
  have hownerHighSet : G.neighborFinset owner ∩
      squareOrderHighVertices G 9 = squareOrderHighVertices G 9 := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
    have hk3 := (Finset.mem_filter.mp howner).2
    have hinter : (G.neighborFinset owner ∩
        squareOrderHighVertices G 9).card = 3 := hk3
    rw [hhigh, hinter]
  have hownerAdj (h : V) (hh : h ∈ H) : G.Adj h owner := by
    have hhHigh : h ∈ squareOrderHighVertices G 9 := by simpa [H, hH] using hh
    have hhN : h ∈ G.neighborFinset owner :=
      (Finset.mem_inter.mp (show h ∈ G.neighborFinset owner ∩
        squareOrderHighVertices G 9 by rw [hownerHighSet]; exact hhHigh)).1
    exact (G.adj_comm owner h).mp ((G.mem_neighborFinset owner h).mp hhN)
  have hprofile := orderNine_order27_largeShore_profile_package
    G hfree hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ owner E S T
      (by simpa [U, O, H, hH] using hunion) hdisj
      (by simpa [U, O, H, hH] using hEsub) hEcard hScard hTcard
      hownerO hfull (by simpa [E] using hTboundary)
      (hownerAdj h₁ (by simp [H])) (hownerAdj h₂ (by simp [H]))
      (hownerAdj h₃ (by simp [H])) hdegOrd hdegHigh hhighIndependent
  dsimp only at hprofile
  have heq20 := hprofile.2.2
  have hZsub : Z ⊆ (Finset.univ : Finset V) \
      squareOrderHighVertices G 9 := by
    intro x hx
    have hx' := orderNineOrdinaryLowSet_subset G h₁ h₂ h₃ T 5 hx
    simpa [Z, hH] using hx'
  have hTsaturated : ∀ h ∈ H, G.neighborFinset h ⊆ Z := by
    intro h hh
    have hhT : h ∉ T := by
      intro hht
      have htU : h ∈ U := by
        change h ∈ O.erase owner
        change h ∈ ((Finset.univ : Finset V) \
          squareOrderHighVertices G 9).erase owner
        rw [← hunion]
        exact Finset.mem_union_right S hht
      have htO := (Finset.mem_erase.mp htU).2
      exact (Finset.mem_sdiff.mp htO).2 (by simpa [H, hH] using hh)
    have hDz : ((secondOrderDefectGraph G).neighborFinset h ∩ T).card = 0 := by
      rw [hdefectHighIsolated h hh]
      simp
    exact orderNine_order27_highRoot_neighbors_subset_lowSet
      G T Z H h hh hhT (hdegHigh h hh) hDz (by simpa [H] using heq20)
  have hcomp := orderNine_order27_lowSet_composition
    G hcard hp hhigh hc2 hc3 owner howner Z hZsub hprofile.2.1
      (by
        intro h hh
        exact hTsaturated h (by simpa [H, hH] using hh))
  have hWcard : W.card = 8 := by simpa [W] using hcomp.2.2.2
  have hWsubB0 : W ⊆ squareOrderNineLowIncidenceBin G 0 :=
    Finset.inter_subset_right
  have hWsubU : W ⊆ U := by
    intro x hx
    have hxZ := (Finset.mem_inter.mp hx).1
    have hxO := hZsub hxZ
    have hxne : x ≠ owner := by
      intro hxo
      subst x
      have hk0 := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).2).2
      have hk3 := (Finset.mem_filter.mp howner).2
      omega
    exact Finset.mem_erase.mpr ⟨hxne, hxO⟩
  have hWH : Disjoint W H := by
    rw [Finset.disjoint_left]
    intro x hxW hxH'
    exact (Finset.mem_sdiff.mp (hZsub (Finset.mem_inter.mp hxW).1)).2
      (by simpa [H, hH] using hxH')
  have hownerDegree : G.degree owner = 9 := by
    apply hdegOrd
    have ho := (Finset.mem_filter.mp howner).1
    simpa [hH] using (Finset.mem_sdiff.mp ho).2
  have hownerNotT : owner ∉ T := by
    intro hot
    apply hownerNotU
    change owner ∈ O.erase owner
    change owner ∈ ((Finset.univ : Finset V) \
      squareOrderHighVertices G 9).erase owner
    rw [← hunion]
    exact Finset.mem_union_right S hot
  have hdefectT : ((secondOrderDefectGraph G).neighborFinset owner ∩ T).card = 2 := by
    have hE2 := orderNine_order27_exceptional_inter_large_card_eq_two
      G E S T U h₁ h₂ h₃ (by simpa [U, O, H, hH] using hunion) hdisj
        hEsub hEcard hScard hfull
    have hDE : (secondOrderDefectGraph G).neighborFinset owner = E := by
      simpa [E] using hEinfo.2.1
    rw [hDE]
    exact hE2
  have hownerB0subW := orderNine_order27_owner_binZero_neighbors_subset_W
    G hfree hmin hcard hp hhigh hc2 hc3 hc4 owner howner hownerDegree
      T Z hownerNotT hdefectT hZsub (by simpa [H, hH] using heq20)
  have hUeq : G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 =
      G.neighborFinset owner ∩ W := by
    apply Finset.Subset.antisymm
    · intro x hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
        hownerB0subW hx⟩
    · intro x hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
        hWsubB0 (Finset.mem_inter.mp hx).2⟩
  have hUcard :
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0).card = 3 := by
    let K := G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1
    let L := G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0
    have hKcard : K.card = 3 := by
      simpa [K] using
        squareOrderNine_threeHigh_secondProfile_binThree_original_binOne_neighbors
          G hfree hmin hcard hp hhigh hc2 hc3 hc4 howner
    have hOrd := orderNine_binThree_owner_ordinary_erase_neighbor_card_eq_six
      G owner hownerDegree howner
    have hpart := orderNine_secondProfile_owner_neighbor_inter_ordinary_shore_bin_partition
      G hp hhigh hc2 hc3 howner
        ((Finset.univ : Finset V) \ squareOrderHighVertices G 9)
        (by intro z hz; exact hz)
    have hKO : K ∩ ((Finset.univ : Finset V) \
        squareOrderHighVertices G 9) = K := by
      exact Finset.inter_eq_left.mpr (fun z hz ↦
        (Finset.mem_filter.mp (Finset.mem_inter.mp hz).2).1)
    have hLO : L ∩ ((Finset.univ : Finset V) \
        squareOrderHighVertices G 9) = L := by
      exact Finset.inter_eq_left.mpr (fun z hz ↦
        (Finset.mem_filter.mp (Finset.mem_inter.mp hz).2).1)
    have hKL : K ∪ L = G.neighborFinset owner ∩
        ((Finset.univ : Finset V) \ squareOrderHighVertices G 9) := by
      rw [hKO, hLO] at hpart
      simpa [K, L, Finset.union_comm] using hpart.symm
    have hd : Disjoint K L := by
      rw [Finset.disjoint_left]
      intro z hzK hzL
      have hk1 := (Finset.mem_filter.mp (Finset.mem_inter.mp hzK).2).2
      have hk0 := (Finset.mem_filter.mp (Finset.mem_inter.mp hzL).2).2
      omega
    have hc := Finset.card_union_of_disjoint hd
    rw [hKL, hKcard] at hc
    have hOrd' : (G.neighborFinset owner ∩
        ((Finset.univ : Finset V) \ squareOrderHighVertices G 9)).card = 6 := by
      have heq : G.neighborFinset owner ∩
          ((Finset.univ : Finset V) \ squareOrderHighVertices G 9).erase owner =
          G.neighborFinset owner ∩
            ((Finset.univ : Finset V) \ squareOrderHighVertices G 9) := by
        ext z
        simp only [Finset.mem_inter, Finset.mem_erase]
        constructor
        · exact fun hz ↦ ⟨hz.1, hz.2.2⟩
        · intro hz
          refine ⟨hz.1, ?_, hz.2⟩
          intro hzo
          subst z
          exact G.loopless.irrefl owner
            ((G.mem_neighborFinset owner owner).mp hz.1)
      rw [← heq]
      exact hOrd
    rw [hOrd'] at hc
    simpa [L] using (show L.card = 3 by omega)
  have heq21 := orderNine_order27_binZero_W_degree_equation
    G hfree hmin hcard hp hhigh hc2 hc3 hc4 owner howner Z W
      hcomp.2.1 rfl (by simpa [W] using hcomp.2.2.1)
  have hExceptionalLarge :
      (((secondOrderDefectGraph G).neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0) ∩ T).card = 2 := by
    have hE2 := orderNine_order27_exceptional_inter_large_card_eq_two
      G E S T U h₁ h₂ h₃ (by simpa [U, O, H, hH] using hunion) hdisj
        hEsub hEcard hScard hfull
    simpa [E] using hE2
  have hlocAlt : (G.induce (G.neighborSet owner)).edgeFinset.card = 3 ∨
      (G.induce (G.neighborSet owner)).edgeFinset.card = 4 := by
    have hpkg := orderNine_secondProfile_owner_binZero_local_type_package
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
    rcases hpkg with h3 | h4
    · exact Or.inl h3.1
    · exact Or.inr h4.1
  have hpunctured : ∀ x ∈ U,
      (secondOrderDefectGraph G).neighborFinset x ⊆ insert owner U := by
    simpa [U, O] using
      (orderNine_defect_neighbors_subset_insert_owner_ordinary_erase
        G h₁ h₂ h₃ owner hH hdefectHighIsolated)
  exact false_of_orderNine_order27_handshake_of_punctured_articulation
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 owner howner
      U T S T Z W H hownerNotU (by
        simpa [U, O, Finset.union_comm] using hunion)
      hdisj.symm hpunctured hTclosed hSclosed rfl
      (by simpa [H] using heq20) hWsubU hWsubB0 hWH hWcard hUeq hUcard
      heq21 (by
        have hownerZ : owner ∈ Z := hcomp.1
        have hTdeg : (G.neighborFinset owner ∩ T).card = 5 := by
          have hz := (Finset.mem_filter.mp hownerZ).2
          simpa [Z, orderNineOrdinaryLowSet] using hz
        have hOrd := orderNine_binThree_owner_ordinary_erase_neighbor_card_eq_six
          G owner hownerDegree howner
        have hsplit : (G.neighborFinset owner ∩ S).card +
            (G.neighborFinset owner ∩ T).card = 6 := by
          have hd : Disjoint (G.neighborFinset owner ∩ S)
              (G.neighborFinset owner ∩ T) :=
            Finset.disjoint_of_subset_right Finset.inter_subset_right
              (Finset.disjoint_of_subset_left Finset.inter_subset_right hdisj)
          have hset : (G.neighborFinset owner ∩ S) ∪
              (G.neighborFinset owner ∩ T) =
              G.neighborFinset owner ∩ U := by
            ext x
            simp only [Finset.mem_union, Finset.mem_inter]
            constructor
            · rintro (hx | hx)
              · refine ⟨hx.1, ?_⟩
                change x ∈ O.erase owner
                change x ∈ ((Finset.univ : Finset V) \
                  squareOrderHighVertices G 9).erase owner
                rw [← hunion]
                exact Finset.mem_union_left T hx.2
              · refine ⟨hx.1, ?_⟩
                change x ∈ O.erase owner
                change x ∈ ((Finset.univ : Finset V) \
                  squareOrderHighVertices G 9).erase owner
                rw [← hunion]
                exact Finset.mem_union_right S hx.2
            · intro hx
              have hxU : x ∈ ((Finset.univ : Finset V) \
                  squareOrderHighVertices G 9).erase owner := by
                simpa [U, O] using hx.2
              rw [← hunion] at hxU
              rcases Finset.mem_union.mp hxU with hxS | hxT
              · exact Or.inl ⟨hx.1, hxS⟩
              · exact Or.inr ⟨hx.1, hxT⟩
          rw [← Finset.card_union_of_disjoint hd, hset]
          simpa [U, O] using hOrd
        omega) hExceptionalLarge hlocAlt

/-- The unordered `(27,50)` branch returned by the articulation capstone is
impossible, by orienting the FullType shore as the order-27 side. -/
theorem false_of_orderNine_order27_unordered_articulation_output
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃) (h₂₃ : h₂ ≠ h₃)
    (hH : squareOrderHighVertices G 9 = {h₁, h₂, h₃})
    (owner : V) (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (S T : Finset V)
    (hunion : S ∪ T =
      ((Finset.univ : Finset V) \ squareOrderHighVertices G 9).erase owner)
    (hdisj : Disjoint S T)
    (horders : (S.card = 27 ∧ T.card = 50) ∨
      (S.card = 50 ∧ T.card = 27))
    (hfull : orderNineArticulationSmallShoreFullType G
        ((secondOrderDefectGraph G).neighborFinset owner ∩
          squareOrderNineLowIncidenceBin G 0) h₁ h₂ h₃ S ∨
      orderNineArticulationSmallShoreFullType G
        ((secondOrderDefectGraph G).neighborFinset owner ∩
          squareOrderNineLowIncidenceBin G 0) h₁ h₂ h₃ T)
    (hSclosed : ∀ x ∈ S, (secondOrderDefectGraph G).neighborFinset x ∩
      ((Finset.univ : Finset V) \ squareOrderHighVertices G 9).erase owner ⊆ S)
    (hTclosed : ∀ x ∈ T, (secondOrderDefectGraph G).neighborFinset x ∩
      ((Finset.univ : Finset V) \ squareOrderHighVertices G 9).erase owner ⊆ T)
    (hSboundary : (∑ x ∈ S,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ S)).card) =
      (((secondOrderDefectGraph G).neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0) ∩ S).card)
    (hTboundary : (∑ x ∈ T,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ T)).card) =
      (((secondOrderDefectGraph G).neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0) ∩ T).card)
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ x ∈ ({h₁, h₂, h₃} : Finset V), G.degree x = 10)
    (hhighIndependent : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      Disjoint (G.neighborFinset h) ({h₁, h₂, h₃} : Finset V))
    (hdefectHighIsolated : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      (secondOrderDefectGraph G).neighborFinset h = ∅) : False := by
  rcases horders with hST | hTS
  · rcases hfull with hfullS | hfullT
    · exact false_of_orderNine_order27_oriented_articulation_output
        G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4
          h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hH owner howner S T hunion hdisj
          hST.1 hST.2 hfullS hSclosed hTclosed hTboundary
          hdegOrd hdegHigh hhighIndependent hdefectHighIsolated
    · have hbad := hfullT.1
      unfold orderNineArticulationSmallShoreBetaType at hbad
      omega
  · rcases hfull with hfullS | hfullT
    · have hbad := hfullS.1
      unfold orderNineArticulationSmallShoreBetaType at hbad
      omega
    · exact false_of_orderNine_order27_oriented_articulation_output
        G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4
          h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hH owner howner T S
          (by simpa [Finset.union_comm] using hunion) hdisj.symm
          hTS.2 hTS.1 hfullT hTclosed hSclosed hSboundary
          hdegOrd hdegHigh hhighIndependent hdefectHighIsolated

/-- Erasing an ordinary owner from the target of a `5/6` partition changes
exactly its six ordinary neighbors from the upper class to the lower class.
This is the missing transfer between the 51-point unpunctured complement
returned by the sharp-partition theorem and the actual 50-point shore. -/
theorem orderNine_explicitPartition_five_48_erase_owner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h₁ h₂ h₃ owner : V) (R : Finset V)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ R 5 48)
    (hownerR : owner ∈ R)
    (hordinaryNeighbors :
      (G.neighborFinset owner ∩
        ((Finset.univ : Finset V) \ {h₁, h₂, h₃})).card = 6)
    (hneighborsUpper : ∀ x ∈
      (Finset.univ : Finset V) \ {h₁, h₂, h₃},
      G.Adj x owner → (G.neighborFinset x ∩ R).card = 6) :
    orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ (R.erase owner) 5 42 := by
  classical
  let O := (Finset.univ : Finset V) \ {h₁, h₂, h₃}
  let fR := fun x : ↥(↑O : Set V) => (G.neighborFinset x.1 ∩ R).card
  let fT := fun x : ↥(↑O : Set V) =>
    (G.neighborFinset x.1 ∩ R.erase owner).card
  change (∀ x, fR x = 5 ∨ fR x = 6) ∧
    (Finset.univ.filter fun x => fR x = 6).card = 48 at hpart
  change (∀ x, fT x = 5 ∨ fT x = 6) ∧
    (Finset.univ.filter fun x => fT x = 6).card = 42
  have herase (x : V) :
      G.neighborFinset x ∩ R.erase owner =
        (G.neighborFinset x ∩ R).erase owner := by
    ext y
    simp [and_left_comm]
  have hfT_adj (x : ↥(↑O : Set V)) (hx : G.Adj x.1 owner) :
      fT x = fR x - 1 := by
    have hm : owner ∈ G.neighborFinset x.1 ∩ R := by
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x.1 owner).mpr hx, hownerR⟩
    dsimp [fT, fR]
    rw [herase, Finset.card_erase_of_mem hm]
  have hfT_not_adj (x : ↥(↑O : Set V)) (hx : ¬ G.Adj x.1 owner) :
      fT x = fR x := by
    have hm : owner ∉ G.neighborFinset x.1 ∩ R := by
      intro hm
      exact hx ((G.mem_neighborFinset x.1 owner).mp (Finset.mem_inter.mp hm).1)
    dsimp [fT, fR]
    rw [herase, Finset.erase_eq_self.mpr hm]
  have hlevels : ∀ x, fT x = 5 ∨ fT x = 6 := by
    intro x
    by_cases hx : G.Adj x.1 owner
    · have hu : fR x = 6 := hneighborsUpper x.1 x.2 hx
      left
      rw [hfT_adj x hx, hu]
    · simpa [hfT_not_adj x hx] using hpart.1 x
  let A := Finset.univ.filter fun x : ↥(↑O : Set V) => fR x = 6
  let B := Finset.univ.filter fun x : ↥(↑O : Set V) => fT x = 6
  let N := Finset.univ.filter fun x : ↥(↑O : Set V) => G.Adj x.1 owner
  have hBA : B = A \ N := by
    ext x
    simp only [B, A, N, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff]
    by_cases hx : G.Adj x.1 owner
    · have hu : fR x = 6 := hneighborsUpper x.1 x.2 hx
      have hl : fT x = 5 := by rw [hfT_adj x hx, hu]
      simp [hx, hl]
    · rw [hfT_not_adj x hx]
      simp [hx]
  have hNsubA : N ⊆ A := by
    intro x hx
    have hxAdj : G.Adj x.1 owner := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x,
      hneighborsUpper x.1 x.2 hxAdj⟩
  have hNcard : N.card = 6 := by
    have hequiv : N.card = (G.neighborFinset owner ∩ O).card := by
      apply Finset.card_bij (fun x _ => x.1)
      · intro x hx
        have hxAdj : G.Adj x.1 owner := (Finset.mem_filter.mp hx).2
        exact Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset owner x.1).mpr ((G.adj_comm _ _).mp hxAdj), x.2⟩
      · intro a₁ ha₁ a₂ ha₂ heq
        exact Subtype.ext heq
      · intro y hy
        have hyO := (Finset.mem_inter.mp hy).2
        refine ⟨⟨y, hyO⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (G.adj_comm _ _).mp ((G.mem_neighborFinset owner y).mp
            (Finset.mem_inter.mp hy).1)⟩
    rw [hequiv]
    exact hordinaryNeighbors
  refine ⟨hlevels, ?_⟩
  change B.card = 42
  rw [hBA, Finset.card_sdiff_of_subset hNsubA]
  have hAcard : A.card = 48 := hpart.2
  omega

/-- The punctured lower class consists of the old lower class together with
the six ordinary neighbors whose target incidence drops from six to five. -/
theorem orderNine_lowSet_five_erase_owner_eq_union_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h₁ h₂ h₃ owner : V) (R : Finset V)
    (hownerR : owner ∈ R)
    (hneighborsUpper : ∀ x ∈
      (Finset.univ : Finset V) \ {h₁, h₂, h₃},
      G.Adj x owner → (G.neighborFinset x ∩ R).card = 6) :
    orderNineOrdinaryLowSet G h₁ h₂ h₃ (R.erase owner) 5 =
      orderNineOrdinaryLowSet G h₁ h₂ h₃ R 5 ∪
        (G.neighborFinset owner ∩
          ((Finset.univ : Finset V) \ {h₁, h₂, h₃})) := by
  classical
  let O := (Finset.univ : Finset V) \ {h₁, h₂, h₃}
  ext x
  have herase :
      G.neighborFinset x ∩ R.erase owner =
        (G.neighborFinset x ∩ R).erase owner := by
    ext y
    simp [and_left_comm]
  by_cases hxO : x ∈ O
  · by_cases hx : G.Adj x owner
    · have hu : (G.neighborFinset x ∩ R).card = 6 :=
        hneighborsUpper x hxO hx
      have hx' : G.Adj owner x := (G.adj_comm x owner).mp hx
      have hm : owner ∈ G.neighborFinset x ∩ R :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x owner).mpr hx, hownerR⟩
      have hnew : (G.neighborFinset x ∩ R.erase owner).card = 5 := by
        rw [herase, Finset.card_erase_of_mem hm, hu]
      simp [orderNineOrdinaryLowSet, O, hxO, hx', hu, hnew]
    · have hm : owner ∉ G.neighborFinset x ∩ R := by
        intro hm
        exact hx ((G.mem_neighborFinset x owner).mp (Finset.mem_inter.mp hm).1)
      have hsame : (G.neighborFinset x ∩ R.erase owner).card =
          (G.neighborFinset x ∩ R).card := by
        rw [herase, Finset.erase_eq_self.mpr hm]
      have hx' : ¬ G.Adj owner x := fun h ↦ hx ((G.adj_comm owner x).mp h)
      simp [orderNineOrdinaryLowSet, O, hxO, hx', hsame]
  · simp [orderNineOrdinaryLowSet, O, hxO]

/-- Consequently the corrected order-50-shore low set has cardinality 36,
the number used in audit equation (20). -/
theorem orderNine_lowSet_card_eq_thirtySix_after_owner_puncture
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ owner : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃)
    (h₂₃ : h₂ ≠ h₃) (R : Finset V)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ R 5 48)
    (hownerR : owner ∈ R)
    (hordinaryNeighbors :
      (G.neighborFinset owner ∩
        ((Finset.univ : Finset V) \ {h₁, h₂, h₃})).card = 6)
    (hneighborsUpper : ∀ x ∈
      (Finset.univ : Finset V) \ {h₁, h₂, h₃},
      G.Adj x owner → (G.neighborFinset x ∩ R).card = 6) :
    (orderNineOrdinaryLowSet G h₁ h₂ h₃ (R.erase owner) 5).card = 36 := by
  have hnew := orderNine_explicitPartition_five_48_erase_owner
    G h₁ h₂ h₃ owner R hpart hownerR hordinaryNeighbors hneighborsUpper
  have hcardLow := orderNineOrdinaryLowSet_card G hcard
    h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ (R.erase owner) 5 42 hnew
  omega

#print axioms orderNine_explicitPartition_five_48_erase_owner
#print axioms orderNine_order27_orient_articulation_shores
#print axioms orderNine_order27_exceptional_inter_large_card_eq_two
#print axioms orderNine_order27_high_neighbor_large_card_eq_six
#print axioms orderNine_order27_explicitPartition_of_large_boundary
#print axioms orderNine_order27_largeShore_profile_package
#print axioms orderNine_order27_highRoot_neighbors_subset_lowSet
#print axioms orderNine_order27_owner_lowSet_degree_eq_six
#print axioms orderNine_order27_exceptional_lowSet_degree_eq_if
#print axioms orderNine_order27_regular_lowSet_degree_eq_four
#print axioms orderNine_order27_exceptional_owner_neighbors_lowSet_degree_eq_if_of_punctured_shores
#print axioms orderNine_order27_regular_owner_neighbors_lowSet_degree_four_of_punctured_shores
#print axioms orderNine_order27_binZero_lowSet_degree_four_of_punctured_shores
#print axioms orderNine_order27_binZero_lowSet_degree_eq_if_of_punctured_owner
#print axioms six_set_contains_other_three_of_partition
#print axioms orderNine_order27_owner_binZero_neighbors_subset_W
#print axioms orderNine_positiveIncidenceBin_subset_of_high_neighbors_subset
#print axioms orderNine_order27_lowSet_composition
#print axioms orderNine_binZero_W_degree_of_lowSet_partition
#print axioms orderNine_order27_binZero_W_degree_equation
#print axioms orderNine_order27_complement_W_degree_sum_le_five
#print axioms orderNine_order27_complement_W_degree_sum_le_five_of_punctured_shores
#print axioms orderNine_order27_threeEdge_owner_neighbors_large_card_eq_two
#print axioms orderNine_order27_threeEdge_W_degree_sum_eq_seven
#print axioms orderNine_order27_fourEdge_W_degree_sum_ge_eight
#print axioms orderNine_order27_fourEdge_internal_degree_sum_eq_two
#print axioms sum_neighbor_inter_card_comm
#print axioms sum_neighbor_inter_card_le_complement_of_independent
#print axioms false_of_orderNine_order27_threeEdge_handshake
#print axioms sum_neighbor_inter_card_le_internal_add_complement
#print axioms false_of_orderNine_order27_fourEdge_handshake
#print axioms false_of_orderNine_order27_handshake_of_punctured_articulation
#print axioms false_of_orderNine_order27_oriented_articulation_output
#print axioms false_of_orderNine_order27_unordered_articulation_output
#print axioms orderNine_lowSet_five_erase_owner_eq_union_neighbors
#print axioms orderNine_lowSet_card_eq_thirtySix_after_owner_puncture

end

end Erdos85
