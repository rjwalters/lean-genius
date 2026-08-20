import Proofs.Erdos85OddSquareOrderNineThreeHighLocalMatching

/-! # Bin-one defect types in the q = 9 three-high profile

Node: B.3 / GAP B-CLASSIFY.  The pointwise defect ledger leaves exactly two
possible neighbor types for a bin-one vertex in the first three-high profile.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In the `(54,24,3,0,0)` profile, every bin-one vertex has one of two
exact defect-neighborhood types: `(B₀,B₁,B₂)=(6,0,1)` or `(5,2,0)`. -/
theorem squareOrderNine_threeHigh_firstProfile_binOne_defect_neighbor_dichotomy
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
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 1) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    ((D.neighborFinset x ∩ B 0).card = 6 ∧
        (D.neighborFinset x ∩ B 1).card = 0 ∧
        (D.neighborFinset x ∩ B 2).card = 1) ∨
      ((D.neighborFinset x ∩ B 0).card = 5 ∧
        (D.neighborFinset x ∩ B 1).card = 2 ∧
        (D.neighborFinset x ∩ B 2).card = 0) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  have hB3 : B 3 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 3) (by omega), hc3]
  have hB4 : B 4 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 4) (by omega), hc4]
  have hpnt := squareOrderNine_lowIncidenceBin_pointwise_ledger
    G hfree hmin hcover hcard hx
  dsimp only at hpnt
  rw [hhigh] at hpnt
  change D.degree x = 8 - 1 ∧
    (∑ y ∈ D.neighborFinset x, squareOrderHighIncidenceCount G 9 y) =
      3 - 1 at hpnt
  norm_num at hpnt
  have hpart := squareOrderNine_defectNeighbor_bin_partition
    G hfree hmin hcard hp x
  dsimp only at hpart
  change
    (∑ j ∈ Finset.range 5, (D.neighborFinset x ∩ B j).card) = D.degree x ∧
      (∑ j ∈ Finset.range 5, j * (D.neighborFinset x ∩ B j).card) =
        ∑ y ∈ D.neighborFinset x, squareOrderHighIncidenceCount G 9 y at hpart
  rw [hpnt.1, hpnt.2] at hpart
  norm_num [Finset.sum_range_succ] at hpart
  rw [hB3, hB4] at hpart
  norm_num at hpart
  by_cases htwo : (D.neighborFinset x ∩ B 2).card = 0
  · right
    change (D.neighborFinset x ∩ B 0).card = 5 ∧
      (D.neighborFinset x ∩ B 1).card = 2 ∧
      (D.neighborFinset x ∩ B 2).card = 0
    omega
  · left
    change (D.neighborFinset x ∩ B 0).card = 6 ∧
      (D.neighborFinset x ∩ B 1).card = 0 ∧
      (D.neighborFinset x ∩ B 2).card = 1
    omega

/-- A bin-one vertex defect-adjacent to a bin-two witness is necessarily the
exceptional `(B₀,B₁,B₂)=(6,0,1)` type. -/
theorem squareOrderNine_threeHigh_firstProfile_defectMate_binOne_type
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
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {x y : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 2)
    (hy : y ∈ squareOrderNineLowIncidenceBin G 1)
    (hDxy : (secondOrderDefectGraph G).Adj x y) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    (D.neighborFinset y ∩ B 0).card = 6 ∧
      (D.neighborFinset y ∩ B 1).card = 0 ∧
      (D.neighborFinset y ∩ B 2).card = 1 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  have htypes :=
    squareOrderNine_threeHigh_firstProfile_binOne_defect_neighbor_dichotomy
      G hfree hmin hcover hcard hp hhigh hc3 hc4 hy
  dsimp only at htypes
  rcases htypes with hexceptional | hordinary
  · exact hexceptional
  · have hxMem : x ∈ D.neighborFinset y ∩ B 2 :=
      Finset.mem_inter.mpr ⟨
        (D.mem_neighborFinset y x).mpr hDxy.symm, hx⟩
    have hpos : 0 < (D.neighborFinset y ∩ B 2).card :=
      Finset.card_pos.mpr ⟨x, hxMem⟩
    rw [hordinary.2.2] at hpos
    omega

/-- Exactly three bin-one vertices have a bin-two defect neighbor in the
first three-high profile.  These are precisely the exceptional pointwise
type singled out above. -/
theorem squareOrderNine_threeHigh_firstProfile_exceptional_binOne_card
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
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    ((B 1).filter fun y => (D.neighborFinset y ∩ B 2).card = 1).card = 3 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let E := (B 1).filter fun y =>
    ((secondOrderDefectGraph G).neighborFinset y ∩ B 2).card = 1
  have hB3 : B 3 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 3) (by omega), hc3]
  have he12 : squareOrderNineDefectBinEdgeCount G 1 2 = 3 := by
    rcases squareOrderNine_threeHigh_defectQuotient_census
        G hfree hmin hcover hcard hp hhigh with hfirst | hsecond
    · exact hfirst.2.2.2.2.1
    · have he03zero : squareOrderNineDefectBinEdgeCount G 0 3 = 0 := by
        simp [squareOrderNineDefectBinEdgeCount, B, hB3]
      omega
  have hpoint : ∀ y ∈ B 1,
      ((secondOrderDefectGraph G).neighborFinset y ∩ B 2).card = 0 ∨
        ((secondOrderDefectGraph G).neighborFinset y ∩ B 2).card = 1 := by
    intro y hy
    have ht :=
      squareOrderNine_threeHigh_firstProfile_binOne_defect_neighbor_dichotomy
        G hfree hmin hcover hcard hp hhigh hc3 hc4 hy
    dsimp only at ht
    rcases ht with he | ho
    · exact Or.inr he.2.2
    · exact Or.inl ho.2.2
  change E.card = 3
  calc
    E.card = ∑ y ∈ B 1, if y ∈ E then 1 else 0 := by
      rw [Finset.card_eq_sum_ones]
      simp [E]
      congr 1
      ext y
      simp
    _ = ∑ y ∈ B 1,
        ((secondOrderDefectGraph G).neighborFinset y ∩ B 2).card := by
      apply Finset.sum_congr rfl
      intro y hy
      rcases hpoint y hy with hzero | hone
      · have hyNotE : y ∉ E := by simp [E, hzero]
        simp [hyNotE, hzero]
      · have hyE : y ∈ E := by simp [E, hy, hone]
        simp [hyE, hone]
    _ = squareOrderNineDefectBinEdgeCount G 1 2 := by
      rfl
    _ = 3 := he12

/-- Removing the three exceptional bin-one vertices leaves a two-regular
induced defect graph: exceptional vertices have no bin-one defect edges, so
the two bin-one neighbors of every ordinary vertex remain in the ordinary
core. -/
theorem squareOrderNine_threeHigh_firstProfile_ordinary_binOne_defect_twoRegular
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
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    let O := (B 1).filter fun y => (D.neighborFinset y ∩ B 2).card = 0
    ∀ y : ↥(↑O : Set V), (D.induce (↑O : Set V)).degree y = 2 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let O := (B 1).filter fun y =>
    ((secondOrderDefectGraph G).neighborFinset y ∩ B 2).card = 0
  intro y
  have hyO : y.1 ∈ O := y.2
  have hyB : y.1 ∈ B 1 := (Finset.mem_filter.mp hyO).1
  have hyZero : (D.neighborFinset y.1 ∩ B 2).card = 0 := by
    simpa [O] using (Finset.mem_filter.mp hyO).2
  have hyTypes :=
    squareOrderNine_threeHigh_firstProfile_binOne_defect_neighbor_dichotomy
      G hfree hmin hcover hcard hp hhigh hc3 hc4 hyB
  dsimp only at hyTypes
  have hyOrdinary : (D.neighborFinset y.1 ∩ B 1).card = 2 := by
    rcases hyTypes with he | ho
    · rw [he.2.2] at hyZero
      omega
    · exact ho.2.1
  have hinter : D.neighborFinset y.1 ∩ O = D.neighborFinset y.1 ∩ B 1 := by
    ext z
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hyz, hzO⟩
      exact ⟨hyz, (Finset.mem_filter.mp hzO).1⟩
    · rintro ⟨hyz, hzB⟩
      refine ⟨hyz, Finset.mem_filter.mpr ⟨hzB, ?_⟩⟩
      have hzTypes :=
        squareOrderNine_threeHigh_firstProfile_binOne_defect_neighbor_dichotomy
          G hfree hmin hcover hcard hp hhigh hc3 hc4 hzB
      dsimp only at hzTypes
      rcases hzTypes with he | ho
      · have hyMem : y.1 ∈ D.neighborFinset z ∩ B 1 :=
          Finset.mem_inter.mpr ⟨
            (D.mem_neighborFinset z y.1).mpr
              ((D.adj_comm y.1 z).mp ((D.mem_neighborFinset y.1 z).mp hyz)),
            hyB⟩
        have hpos : 0 < (D.neighborFinset z ∩ B 1).card :=
          Finset.card_pos.mpr ⟨y.1, hyMem⟩
        rw [he.2.1] at hpos
        omega
      · exact ho.2.2
  rw [degree_induce_finset_eq_card_inter]
  rw [hinter]
  exact hyOrdinary

/-- The ordinary two-regular bin-one defect core has exactly 21 vertices. -/
theorem squareOrderNine_threeHigh_firstProfile_ordinary_binOne_card
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
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    ((B 1).filter fun y => (D.neighborFinset y ∩ B 2).card = 0).card = 21 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let E := (B 1).filter fun y =>
    ((secondOrderDefectGraph G).neighborFinset y ∩ B 2).card = 1
  let O := (B 1).filter fun y =>
    ((secondOrderDefectGraph G).neighborFinset y ∩ B 2).card = 0
  have hc1 : squareOrderNineHighIncidenceHistogram G 1 = 24 := by
    rcases squareOrderNine_highIncidence_profile_of_three_high
        G hcard hp hhigh with hfirst | hsecond
    · exact hfirst.2.1
    · omega
  have hB1card : (B 1).card = 24 := by
    dsimp [B]
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 1) (by omega), hc1]
  have hEcard : E.card = 3 := by
    simpa [E, B] using
      (squareOrderNine_threeHigh_firstProfile_exceptional_binOne_card
        G hfree hmin hcover hcard hp hhigh hc3 hc4)
  have hpartition : E ∪ O = B 1 := by
    dsimp [E, O]
    ext y
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    · intro hy
      have ht :=
        squareOrderNine_threeHigh_firstProfile_binOne_defect_neighbor_dichotomy
          G hfree hmin hcover hcard hp hhigh hc3 hc4 hy
      dsimp only at ht
      rcases ht with he | ho
      · exact Or.inl ⟨hy, he.2.2⟩
      · exact Or.inr ⟨hy, ho.2.2⟩
  have hdisj : Disjoint E O := by
    dsimp [E, O]
    rw [Finset.disjoint_left]
    intro y hyE hyO
    have h1 := (Finset.mem_filter.mp hyE).2
    have h0 := (Finset.mem_filter.mp hyO).2
    omega
  have hunionCard : E.card + O.card = (B 1).card := by
    rw [← Finset.card_union_of_disjoint hdisj, hpartition]
  change O.card = 21
  omega

/-- The 21-vertex ordinary bin-one defect core has an odd-order connected
component.  Together with two-regularity, this supplies an odd defect-cycle
component in the first three-high profile. -/
theorem squareOrderNine_threeHigh_firstProfile_exists_odd_ordinary_binOne_component
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
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    let O := (B 1).filter fun y => (D.neighborFinset y ∩ B 2).card = 0
    let K := D.induce (↑O : Set V)
    ∃ c : K.ConnectedComponent, Odd c.supp.ncard := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let O := (B 1).filter fun y =>
    ((secondOrderDefectGraph G).neighborFinset y ∩ B 2).card = 0
  let K := D.induce (↑O : Set V)
  have hOcard : O.card = 21 := by
    simpa [O, B] using
      (squareOrderNine_threeHigh_firstProfile_ordinary_binOne_card
        G hfree hmin hcover hcard hp hhigh hc3 hc4)
  have hKcard : Fintype.card ↥(↑O : Set V) = 21 := by
    simpa using hOcard
  by_contra hnone
  push Not at hnone
  have hparts : (∑ c : K.ConnectedComponent, c.supp.ncard) =
      Fintype.card ↥(↑O : Set V) := by
    simpa [K] using sum_connectedComponent_supp_ncard K
  have hdvd : 2 ∣ ∑ c : K.ConnectedComponent, c.supp.ncard := by
    apply Finset.dvd_sum
    intro c _
    exact (Nat.not_odd_iff_even.mp (hnone c)).two_dvd
  rw [hparts, hKcard] at hdvd
  omega

/-- A defect edge between bin-one vertices joins distinct high-incidence
colors: both endpoints have singleton high neighborhoods, and those
singletons are disjoint. -/
theorem squareOrderNine_defectAdjacent_binOne_highIncidence_singletons_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {x y : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 1)
    (hy : y ∈ squareOrderNineLowIncidenceBin G 1)
    (hDxy : (secondOrderDefectGraph G).Adj x y) :
    let H := squareOrderHighVertices G 9
    Disjoint (G.neighborFinset x ∩ H) (G.neighborFinset y ∩ H) ∧
      (G.neighborFinset x ∩ H).card = 1 ∧
      (G.neighborFinset y ∩ H).card = 1 := by
  classical
  dsimp only
  let H := squareOrderHighVertices G 9
  have hxcard : (G.neighborFinset x ∩ H).card = 1 :=
    (Finset.mem_filter.mp hx).2
  have hycard : (G.neighborFinset y ∩ H).card = 1 :=
    (Finset.mem_filter.mp hy).2
  refine ⟨?_, hxcard, hycard⟩
  rw [Finset.disjoint_left]
  intro a hax hay
  have hax' := Finset.mem_inter.mp hax
  have hay' := Finset.mem_inter.mp hay
  have hnot := not_secondOrderDefect_adj_of_commonNeighbor
    G hfree ((secondOrderDefectGraph G).ne_of_adj hDxy)
    ((G.mem_neighborFinset x a).mp hax'.1)
    ((G.mem_neighborFinset y a).mp hay'.1)
  exact hnot hDxy

/-- In the first three-high profile, every high root has exactly one
exceptional bin-one neighbor.  It is the canonical defect mate of the
bin-two witness for the other two high roots. -/
theorem squareOrderNine_threeHigh_firstProfile_existsUnique_exceptional_binOne_at_high
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
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {a : V} (ha : a ∈ squareOrderHighVertices G 9) :
    let D := secondOrderDefectGraph G
    let H := squareOrderHighVertices G 9
    let B := squareOrderNineLowIncidenceBin G
    let E := (B 1).filter fun y => (D.neighborFinset y ∩ B 2).card = 1
    ∃! y : V, y ∈ E ∧ y ∈ G.neighborFinset a := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let H := squareOrderHighVertices G 9
  let B := squareOrderNineLowIncidenceBin G
  let E := (B 1).filter fun y =>
    ((secondOrderDefectGraph G).neighborFinset y ∩ B 2).card = 1
  have heraseCard : (H.erase a).card = 2 := by
    rw [Finset.card_erase_of_mem ha, hhigh]
  obtain ⟨b, c, hbc, herase⟩ := Finset.card_eq_two.mp heraseCard
  have hbErase : b ∈ H.erase a := by rw [herase]; simp
  have hcErase : c ∈ H.erase a := by rw [herase]; simp
  have hbH : b ∈ H := (Finset.mem_erase.mp hbErase).2
  have hcH : c ∈ H := (Finset.mem_erase.mp hcErase).2
  have hba : b ≠ a := (Finset.mem_erase.mp hbErase).1
  have hca : c ≠ a := (Finset.mem_erase.mp hcErase).1
  obtain ⟨x, hxData, huniqX⟩ :=
    squareOrderNine_threeHigh_firstProfile_existsUnique_pairWitness
      G hfree hmin hcard hp hc3 hc4 hbH hcH hbc
  obtain ⟨y, hyData, huniqY⟩ :=
    squareOrderNine_threeHigh_firstProfile_binTwo_existsUnique_opposite_defectMate
      G hfree hmin hcover hcard hp hhigh hc3 hc4 hxData.1
  have hyDB := hyData.1
  have hyB : y ∈ B 1 := (Finset.mem_inter.mp hyDB).2
  have hDxy : D.Adj x y :=
    (D.mem_neighborFinset x y).mp (Finset.mem_inter.mp hyDB).1
  have hyType := squareOrderNine_threeHigh_firstProfile_defectMate_binOne_type
    G hfree hmin hcover hcard hp hhigh hc3 hc4 hxData.1 hyB hDxy
  dsimp only at hyType
  have hyE : y ∈ E := by
    refine Finset.mem_filter.mpr ⟨hyB, ?_⟩
    simpa [D] using hyType.2.2
  have hIxCard : (G.neighborFinset x ∩ H).card = 2 :=
    (Finset.mem_filter.mp hxData.1).2
  have hbIx : b ∈ G.neighborFinset x ∩ H :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x b).mpr hxData.2.1.symm, hbH⟩
  have hcIx : c ∈ G.neighborFinset x ∩ H :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x c).mpr hxData.2.2.symm, hcH⟩
  have hpairSub : ({b, c} : Finset V) ⊆ G.neighborFinset x ∩ H := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hbIx
    · exact hcIx
  have hIx : G.neighborFinset x ∩ H = {b, c} := by
    symm
    apply Finset.eq_of_subset_of_card_le hpairSub
    rw [hIxCard]
    simp [hbc]
  have haNotIx : a ∉ G.neighborFinset x ∩ H := by
    rw [hIx]
    simp [Ne.symm hba, Ne.symm hca]
  have haIy : a ∈ G.neighborFinset y ∩ H := by
    have haUnion : a ∈ (G.neighborFinset x ∩ H) ∪
        (G.neighborFinset y ∩ H) := by
      rw [hyData.2]
      exact ha
    rcases Finset.mem_union.mp haUnion with haIx | haIy
    · exact (haNotIx haIx).elim
    · exact haIy
  have hay : y ∈ G.neighborFinset a :=
    (G.mem_neighborFinset a y).mpr
      ((G.adj_comm y a).mp ((G.mem_neighborFinset y a).mp
        (Finset.mem_inter.mp haIy).1))
  refine ⟨y, ⟨hyE, hay⟩, ?_⟩
  intro z hz
  have hzE := hz.1
  have hzB : z ∈ B 1 := (Finset.mem_filter.mp hzE).1
  have hzOne := (Finset.mem_filter.mp hzE).2
  have hzPos : 0 < (D.neighborFinset z ∩ B 2).card := by
    simpa [E] using (show 0 < 1 by omega).trans_le (Nat.le_of_eq hzOne.symm)
  obtain ⟨x', hx'Mem⟩ := Finset.card_pos.mp hzPos
  have hx'B : x' ∈ B 2 := (Finset.mem_inter.mp hx'Mem).2
  have hDx'z : D.Adj x' z :=
    ((D.adj_comm z x').mp
      ((D.mem_neighborFinset z x').mp (Finset.mem_inter.mp hx'Mem).1))
  have hcompZ :=
    squareOrderNine_threeHigh_binTwo_defectBinOne_highIncidence_complement
      G hfree hhigh hx'B hzB hDx'z
  have haIz : a ∈ G.neighborFinset z ∩ H :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z a).mpr
      ((G.adj_comm a z).mp ((G.mem_neighborFinset a z).mp hz.2)), ha⟩
  have hIzCard : (G.neighborFinset z ∩ H).card = 1 :=
    (Finset.mem_filter.mp hzB).2
  have hIz : G.neighborFinset z ∩ H = {a} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · simpa using haIz
    · rw [hIzCard]
      simp
  have hbNotIz : b ∉ G.neighborFinset z ∩ H := by rw [hIz]; simp [hba]
  have hcNotIz : c ∉ G.neighborFinset z ∩ H := by rw [hIz]; simp [hca]
  have hbIx' : b ∈ G.neighborFinset x' ∩ H := by
    have : b ∈ (G.neighborFinset x' ∩ H) ∪ (G.neighborFinset z ∩ H) := by
      rw [hcompZ]
      exact hbH
    rcases Finset.mem_union.mp this with h | h
    · exact h
    · exact (hbNotIz h).elim
  have hcIx' : c ∈ G.neighborFinset x' ∩ H := by
    have : c ∈ (G.neighborFinset x' ∩ H) ∪ (G.neighborFinset z ∩ H) := by
      rw [hcompZ]
      exact hcH
    rcases Finset.mem_union.mp this with h | h
    · exact h
    · exact (hcNotIz h).elim
  have hx'eq : x' = x := huniqX x' ⟨hx'B,
    (G.adj_comm x' b).mp ((G.mem_neighborFinset x' b).mp
      (Finset.mem_inter.mp hbIx').1),
    (G.adj_comm x' c).mp ((G.mem_neighborFinset x' c).mp
      (Finset.mem_inter.mp hcIx').1)⟩
  subst x'
  apply huniqY z
  refine ⟨Finset.mem_inter.mpr ⟨(D.mem_neighborFinset x z).mpr hDx'z, hzB⟩, ?_⟩
  exact hcompZ

/-- Each high root has exactly seven ordinary bin-one neighbors.  Thus the
21-vertex two-regular core has three equal high-incidence color classes. -/
theorem squareOrderNine_threeHigh_firstProfile_ordinary_binOne_at_high_card
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
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {a : V} (ha : a ∈ squareOrderHighVertices G 9) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    let O := (B 1).filter fun y => (D.neighborFinset y ∩ B 2).card = 0
    (G.neighborFinset a ∩ O).card = 7 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let E := (B 1).filter fun y =>
    ((secondOrderDefectGraph G).neighborFinset y ∩ B 2).card = 1
  let O := (B 1).filter fun y =>
    ((secondOrderDefectGraph G).neighborFinset y ∩ B 2).card = 0
  have hB1card : (G.neighborFinset a ∩ B 1).card = 8 :=
    (squareOrderNine_threeHigh_firstProfile_highRoot_neighbor_split
      G hfree hmin hcard hp hhigh hc3 hc4 ha).1
  obtain ⟨y, hy, huniq⟩ :=
    squareOrderNine_threeHigh_firstProfile_existsUnique_exceptional_binOne_at_high
      G hfree hmin hcover hcard hp hhigh hc3 hc4 ha
  have hEinter : G.neighborFinset a ∩ E = {y} := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · intro hz
      exact huniq z ⟨hz.2, hz.1⟩
    · intro hzy
      subst z
      exact ⟨hy.2, hy.1⟩
  have hEcard : (G.neighborFinset a ∩ E).card = 1 := by
    rw [hEinter]
    simp
  have hpartition : G.neighborFinset a ∩ B 1 =
      (G.neighborFinset a ∩ E) ∪ (G.neighborFinset a ∩ O) := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨haz, hzB⟩
      have ht :=
        squareOrderNine_threeHigh_firstProfile_binOne_defect_neighbor_dichotomy
          G hfree hmin hcover hcard hp hhigh hc3 hc4 hzB
      dsimp only at ht
      rcases ht with he | ho
      · exact Or.inl ⟨haz, Finset.mem_filter.mpr ⟨hzB, he.2.2⟩⟩
      · exact Or.inr ⟨haz, Finset.mem_filter.mpr ⟨hzB, ho.2.2⟩⟩
    · rintro (⟨haz, hzE⟩ | ⟨haz, hzO⟩)
      · exact ⟨haz, (Finset.mem_filter.mp hzE).1⟩
      · exact ⟨haz, (Finset.mem_filter.mp hzO).1⟩
  have hdisj : Disjoint (G.neighborFinset a ∩ E)
      (G.neighborFinset a ∩ O) := by
    rw [Finset.disjoint_left]
    intro z hzE hzO
    have h1 := (Finset.mem_filter.mp (Finset.mem_inter.mp hzE).2).2
    have h0 := (Finset.mem_filter.mp (Finset.mem_inter.mp hzO).2).2
    omega
  have hcards : (G.neighborFinset a ∩ E).card +
      (G.neighborFinset a ∩ O).card = 8 := by
    rw [← Finset.card_union_of_disjoint hdisj, ← hpartition]
    exact hB1card
  change (G.neighborFinset a ∩ O).card = 7
  omega
end

end Erdos85

#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_binOne_defect_neighbor_dichotomy
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_defectMate_binOne_type
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_exceptional_binOne_card
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_ordinary_binOne_defect_twoRegular
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_ordinary_binOne_card
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_exists_odd_ordinary_binOne_component
#print axioms
  Erdos85.squareOrderNine_defectAdjacent_binOne_highIncidence_singletons_disjoint
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_existsUnique_exceptional_binOne_at_high
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_ordinary_binOne_at_high_card
