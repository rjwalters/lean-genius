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
#print axioms orderNine_positiveIncidenceBin_subset_of_high_neighbors_subset
#print axioms orderNine_order27_lowSet_composition
#print axioms orderNine_binZero_W_degree_of_lowSet_partition
#print axioms orderNine_order27_binZero_W_degree_equation
#print axioms orderNine_lowSet_five_erase_owner_eq_union_neighbors
#print axioms orderNine_lowSet_card_eq_thirtySix_after_owner_puncture

end

end Erdos85
