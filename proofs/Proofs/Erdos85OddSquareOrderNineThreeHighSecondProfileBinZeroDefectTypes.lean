import Proofs.Erdos85OddSquareOrderNineThreeHighSecondProfileCore
import Proofs.Erdos85DegreeExcessStratification
import Proofs.Erdos85GlobalLocalTriangleCount

/-! # Bin-zero defect types in the q = 9 three-high second profile

Node: B.3 / GAP B-CLASSIFY.  The 50 bin-zero vertices split into regular
type `(B₀,B₁,B₃)=(5,3,0)` and exceptional type `(7,0,1)`.  The five
exceptional vertices are precisely the bin-zero defect neighbors of the
unique bin-three vertex.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- An independent set of non-isolated vertices injects into the edge set by
choosing one incident edge at every vertex. -/
theorem independent_nonisolated_card_le_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (S : Finset V)
    (hind : ∀ ⦃u⦄, u ∈ S → ∀ ⦃v⦄, v ∈ S → u ≠ v → ¬ K.Adj u v)
    (hpos : ∀ u ∈ S, 0 < K.degree u) :
    S.card ≤ K.edgeFinset.card := by
  classical
  have hedge : ∀ u : ↥S,
      (K.incidenceFinset u.1).Nonempty := by
    intro u
    rw [← Finset.card_pos, K.card_incidenceFinset_eq_degree]
    exact hpos u.1 u.2
  let pick : (u : ↥S) → Sym2 V :=
    fun u => (hedge u).choose
  have hpickMem (u : ↥S) :
      pick u ∈ K.incidenceFinset u.1 := (hedge u).choose_spec
  let f : ↥S → ↥K.edgeFinset :=
    fun u => ⟨pick u, K.incidenceFinset_subset u.1 (hpickMem u)⟩
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    by_contra hne
    have hpickEq : pick u = pick v := congrArg Subtype.val huv
    have huInc : pick u ∈ K.incidenceSet u.1 :=
      (K.mem_incidenceFinset u.1 (pick u)).mp (hpickMem u)
    have hvInc : pick u ∈ K.incidenceSet v.1 := by
      rw [hpickEq]
      exact (K.mem_incidenceFinset v.1 (pick v)).mp (hpickMem v)
    have huvAdj : K.Adj u.1 v.1 :=
      K.adj_of_mem_incidenceSet hne huInc hvInc
    exact hind u.2 v.2 hne huvAdj
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe] using hcard

/-- Every q=9 bin-zero vertex has one of four exact
`(antipodal, triangle-free, local-triangle)` profiles. -/
theorem squareOrderNine_binZero_antipodal_triangle_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 0) :
    ((antipodalNeighbors G x).card = 1 ∧
        (triangleFreeNeighbors G x).card = 7 ∧
        (G.induce (G.neighborSet x)).edgeFinset.card = 1) ∨
      ((antipodalNeighbors G x).card = 3 ∧
        (triangleFreeNeighbors G x).card = 5 ∧
        (G.induce (G.neighborSet x)).edgeFinset.card = 2) ∨
      ((antipodalNeighbors G x).card = 5 ∧
        (triangleFreeNeighbors G x).card = 3 ∧
        (G.induce (G.neighborSet x)).edgeFinset.card = 3) ∨
      ((antipodalNeighbors G x).card = 7 ∧
        (triangleFreeNeighbors G x).card = 1 ∧
        (G.induce (G.neighborSet x)).edgeFinset.card = 4) := by
  have hxLow := (Finset.mem_filter.mp hx).1
  have hxNotHigh : x ∉ squareOrderHighVertices G 9 :=
    (Finset.mem_sdiff.mp hxLow).2
  have hxDegree : G.degree x = 9 := by
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree (by norm_num) hmin hcover hcard x with hlo | hhi
    · exact hlo
    · exact (hxNotHigh (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
  have hinc : squareOrderHighIncidenceCount G 9 x = 0 :=
    (Finset.mem_filter.mp hx).2
  have hdefect := squareOrder_defectDegree_add_highIncidence_eq_pred
    G hfree (by norm_num) hmin hcover hcard hxDegree
  rw [hinc] at hdefect
  have hsplit := congrArg Finset.card
    (secondOrderDefectGraph_neighborFinset G x)
  rw [Finset.card_union_of_disjoint
    (disjoint_antipodal_triangleFreeNeighbors G x),
    (secondOrderDefectGraph G).card_neighborFinset_eq_degree] at hsplit
  have hparity := triangleFreeNeighbors_card_mod_two_eq_vertexDegree G hfree x
  rw [hxDegree] at hparity
  have htriangle :=
    squareOrder_low_antipodal_add_highIncidence_add_one_eq_two_mul_localEdges
      G hfree (by norm_num) hmin hcover hcard hxDegree
  rw [hinc] at htriangle
  omega

/-- Every bin-zero vertex in the second three-high profile has defect type
`(5,3,0)` or `(7,0,1)` across bins zero, one, and three. -/
theorem squareOrderNine_threeHigh_secondProfile_binZero_defect_neighbor_dichotomy
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
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 0) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    ((D.neighborFinset x ∩ B 0).card = 5 ∧
        (D.neighborFinset x ∩ B 1).card = 3 ∧
        (D.neighborFinset x ∩ B 3).card = 0) ∨
      ((D.neighborFinset x ∩ B 0).card = 7 ∧
        (D.neighborFinset x ∩ B 1).card = 0 ∧
        (D.neighborFinset x ∩ B 3).card = 1) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  have hB2 : B 2 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 2) (by omega), hc2]
  have hB4 : B 4 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 4) (by omega), hc4]
  have hpnt := squareOrderNine_lowIncidenceBin_pointwise_ledger
    G hfree hmin hcover hcard hx
  dsimp only at hpnt
  rw [hhigh] at hpnt
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
  rw [hB2, hB4] at hpart
  norm_num at hpart
  change
    ((D.neighborFinset x ∩ B 0).card = 5 ∧
        (D.neighborFinset x ∩ B 1).card = 3 ∧
        (D.neighborFinset x ∩ B 3).card = 0) ∨
      ((D.neighborFinset x ∩ B 0).card = 7 ∧
        (D.neighborFinset x ∩ B 1).card = 0 ∧
        (D.neighborFinset x ∩ B 3).card = 1)
  by_cases hthree : (D.neighborFinset x ∩ B 3).card = 0
  · left
    exact ⟨by omega, by omega, hthree⟩
  · right
    exact ⟨by omega, by omega, by omega⟩

/-- Exactly five bin-zero vertices have a bin-three defect neighbor, hence
exactly five have exceptional type `(7,0,1)`. -/
theorem squareOrderNine_threeHigh_secondProfile_special_binZero_card
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
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    ((B 0).filter fun y => (D.neighborFinset y ∩ B 3).card = 1).card = 5 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let E := (B 0).filter fun y =>
    ((secondOrderDefectGraph G).neighborFinset y ∩ B 3).card = 1
  have hB2 : B 2 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 2) (by omega), hc2]
  have he03 : squareOrderNineDefectBinEdgeCount G 0 3 = 5 := by
    rcases squareOrderNine_threeHigh_defectQuotient_census
        G hfree hmin hcover hcard hp hhigh with hfirst | hsecond
    · have he02zero : squareOrderNineDefectBinEdgeCount G 0 2 = 0 := by
        simp [squareOrderNineDefectBinEdgeCount, B, hB2]
      omega
    · exact hsecond.2.2.1
  have hpoint : ∀ y ∈ B 0,
      (D.neighborFinset y ∩ B 3).card = 0 ∨
        (D.neighborFinset y ∩ B 3).card = 1 := by
    intro y hy
    have ht :=
      squareOrderNine_threeHigh_secondProfile_binZero_defect_neighbor_dichotomy
        G hfree hmin hcover hcard hp hhigh hc2 hc4 hy
    dsimp only at ht
    rcases ht with hregular | hspecial
    · exact Or.inl hregular.2.2
    · exact Or.inr hspecial.2.2
  change E.card = 5
  calc
    E.card = ∑ y ∈ B 0, if y ∈ E then 1 else 0 := by
      rw [Finset.card_eq_sum_ones]
      simp [E]
      congr 1
      ext y
      simp
    _ = ∑ y ∈ B 0, (D.neighborFinset y ∩ B 3).card := by
      apply Finset.sum_congr rfl
      intro y hy
      rcases hpoint y hy with hzero | hone
      · have hzero' :
            ((secondOrderDefectGraph G).neighborFinset y ∩ B 3).card = 0 := by
          simpa [D] using hzero
        have hyNotE : y ∉ E := by simp [E, hzero']
        simp [hyNotE, hzero]
      · have hone' :
            ((secondOrderDefectGraph G).neighborFinset y ∩ B 3).card = 1 := by
          simpa [D] using hone
        have hyE : y ∈ E := by simp [E, hy, hone']
        simp [hyE, hone]
    _ = squareOrderNineDefectBinEdgeCount G 0 3 := by rfl
    _ = 5 := he03

/-- The five defect edges from the rare bin-three vertex into its exceptional
bin-zero reservoir have label counts `(antipodal, triangle-free)=(2,3)` or
`(4,1)`.  In particular, the all-triangle-free and all-antipodal patterns are
both impossible. -/
theorem squareOrderNine_threeHigh_secondProfile_binThree_reservoir_edgeLabels
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    ((antipodalNeighbors G x).card = 2 ∧
        (triangleFreeNeighbors G x).card = 3) ∨
      ((antipodalNeighbors G x).card = 4 ∧
        (triangleFreeNeighbors G x).card = 1) := by
  classical
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  have hxLow := (Finset.mem_filter.mp hx).1
  have hxNotHigh : x ∉ squareOrderHighVertices G 9 :=
    (Finset.mem_sdiff.mp hxLow).2
  have hxDegree : G.degree x = 9 := by
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree (by norm_num) hmin hcover hcard x with hlo | hhi
    · exact hlo
    · exact (hxNotHigh (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
  have hxDefect := squareOrderNine_threeHigh_secondProfile_binThree_neighbors
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hxDefect
  have hxOriginal :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_neighborhood_census
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hxOriginal
  have htfSubset : triangleFreeNeighbors G x ⊆ G.neighborFinset x ∩ B 0 := by
    intro y hy
    have hyG : y ∈ G.neighborFinset x :=
      (G.mem_neighborFinset x y).mpr ((mem_triangleFreeNeighbors G x y).mp hy).1
    have hyD : y ∈ D.neighborFinset x := by
      rw [secondOrderDefectGraph_neighborFinset G x]
      exact Finset.mem_union_right _ hy
    have hDcard : D.degree x = 5 := by
      have hledger := squareOrderNine_lowIncidenceBin_pointwise_ledger
        G hfree hmin hcover hcard hx
      dsimp only at hledger
      norm_num at hledger
      exact hledger.1
    have hinter : D.neighborFinset x ∩ B 0 = D.neighborFinset x := by
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.inter_subset_left
      · rw [hxDefect.1, D.card_neighborFinset_eq_degree, hDcard]
    have hyB : y ∈ B 0 := by
      have : y ∈ D.neighborFinset x ∩ B 0 := by
        rw [hinter]
        exact hyD
      exact (Finset.mem_inter.mp this).2
    exact Finset.mem_inter.mpr ⟨hyG, hyB⟩
  have htfLe : (triangleFreeNeighbors G x).card ≤ 3 := by
    exact (Finset.card_le_card htfSubset).trans_eq hxOriginal.2.2
  have hsplit := congrArg Finset.card
    (secondOrderDefectGraph_neighborFinset G x)
  rw [Finset.card_union_of_disjoint
    (disjoint_antipodal_triangleFreeNeighbors G x),
    (secondOrderDefectGraph G).card_neighborFinset_eq_degree] at hsplit
  have hdegreeD : (secondOrderDefectGraph G).degree x = 5 := by
    have hledger := squareOrderNine_lowIncidenceBin_pointwise_ledger
      G hfree hmin hcover hcard hx
    dsimp only at hledger
    norm_num at hledger
    exact hledger.1
  rw [hdegreeD] at hsplit
  have hparity := triangleFreeNeighbors_card_mod_two_eq_vertexDegree G hfree x
  rw [hxDegree] at hparity
  omega

/-- The reservoir-label alternatives are equivalently local triangle
profiles `(antipodal, triangle-free, local edges)=(2,3,3)` or `(4,1,4)` at
the rare bin-three vertex.  The first branch has no triangle beyond the three
forced high-root matches; the second has room for exactly one more. -/
theorem squareOrderNine_threeHigh_secondProfile_binThree_localTriangleProfile
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    ((antipodalNeighbors G x).card = 2 ∧
        (triangleFreeNeighbors G x).card = 3 ∧
        (G.induce (G.neighborSet x)).edgeFinset.card = 3) ∨
      ((antipodalNeighbors G x).card = 4 ∧
        (triangleFreeNeighbors G x).card = 1 ∧
        (G.induce (G.neighborSet x)).edgeFinset.card = 4) := by
  have hlabels :=
    squareOrderNine_threeHigh_secondProfile_binThree_reservoir_edgeLabels
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx
  have hxLow := (Finset.mem_filter.mp hx).1
  have hxNotHigh : x ∉ squareOrderHighVertices G 9 :=
    (Finset.mem_sdiff.mp hxLow).2
  have hxDegree : G.degree x = 9 := by
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree (by norm_num) hmin hcover hcard x with hlo | hhi
    · exact hlo
    · exact (hxNotHigh (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
  have hinc : squareOrderHighIncidenceCount G 9 x = 3 :=
    (Finset.mem_filter.mp hx).2
  have htriangle :=
    squareOrder_low_antipodal_add_highIncidence_add_one_eq_two_mul_localEdges
      G hfree (by norm_num) hmin hcover hcard hxDegree
  rw [hinc] at htriangle
  rcases hlabels with hfirst | hsecond
  · left
    exact ⟨hfirst.1, hfirst.2, by omega⟩
  · right
    exact ⟨hsecond.1, hsecond.2, by omega⟩

/-- At the rare bin-three vertex, the original bin-zero edges which also lie
in the defect graph are exactly the triangle-free incident edges. -/
theorem squareOrderNine_threeHigh_secondProfile_binThree_original_binZero_defect_eq_tf
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0 ∩
        (secondOrderDefectGraph G).neighborFinset x =
      triangleFreeNeighbors G x := by
  classical
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  have hxDefect := squareOrderNine_threeHigh_secondProfile_binThree_neighbors
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hxDefect
  have hdegreeD : D.degree x = 5 := by
    have hledger := squareOrderNine_lowIncidenceBin_pointwise_ledger
      G hfree hmin hcover hcard hx
    dsimp only at hledger
    norm_num at hledger
    exact hledger.1
  have hDinside : D.neighborFinset x ∩ B 0 = D.neighborFinset x := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.inter_subset_left
    · rw [hxDefect.1, D.card_neighborFinset_eq_degree, hdegreeD]
  ext y
  constructor
  · intro hy
    have hy' := Finset.mem_inter.mp hy
    have hyG := (Finset.mem_inter.mp hy'.1).1
    have hyD := hy'.2
    rw [secondOrderDefectGraph_neighborFinset G x] at hyD
    rcases Finset.mem_union.mp hyD with hanti | htf
    · exact (((mem_antipodalNeighbors G x y).mp hanti).2.1
        ((G.mem_neighborFinset x y).mp hyG)).elim
    · exact htf
  · intro htf
    have hyG : y ∈ G.neighborFinset x :=
      (G.mem_neighborFinset x y).mpr ((mem_triangleFreeNeighbors G x y).mp htf).1
    have hyD : y ∈ D.neighborFinset x := by
      rw [secondOrderDefectGraph_neighborFinset G x]
      exact Finset.mem_union_right _ htf
    have hyB : y ∈ B 0 := by
      have : y ∈ D.neighborFinset x ∩ B 0 := by
        rw [hDinside]
        exact hyD
      exact (Finset.mem_inter.mp this).2
    exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hyG, hyB⟩, hyD⟩

/-- Of the three original bin-zero neighbors of the rare bin-three vertex,
either all three are defect/triangle-free, or exactly one is.  Hence the
extra-local-triangle branch has exactly two original bin-zero non-defect
edges. -/
theorem squareOrderNine_threeHigh_secondProfile_binThree_original_binZero_defect_card
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0 ∩
        (secondOrderDefectGraph G).neighborFinset x).card = 3 ∨
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0 ∩
        (secondOrderDefectGraph G).neighborFinset x).card = 1 := by
  rw [squareOrderNine_threeHigh_secondProfile_binThree_original_binZero_defect_eq_tf
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx]
  rcases squareOrderNine_threeHigh_secondProfile_binThree_reservoir_edgeLabels
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx with hfirst | hsecond
  · exact Or.inl hfirst.2
  · exact Or.inr hsecond.2

/-- Let `R` be the original bin-zero neighbors of the rare bin-three vertex
whose incident edge is outside the defect graph.  The exact synchronized
alternatives are `(local triangles, |R|)=(3,0)` or `(4,2)`. -/
theorem squareOrderNine_threeHigh_secondProfile_binThree_nondefect_binZero_pair
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    let R := (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x
    ((G.induce (G.neighborSet x)).edgeFinset.card = 3 ∧ R.card = 0) ∨
      ((G.induce (G.neighborSet x)).edgeFinset.card = 4 ∧ R.card = 2) := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let R := S \ (secondOrderDefectGraph G).neighborFinset x
  have hS : S.card = 3 := by
    have hcensus :=
      squareOrderNine_threeHigh_secondProfile_binThree_original_neighborhood_census
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
    dsimp only at hcensus
    exact hcensus.2.2
  have hprofile :=
    squareOrderNine_threeHigh_secondProfile_binThree_localTriangleProfile
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx
  have hinter :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_binZero_defect_eq_tf
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx
  have hRcard : R.card = S.card - (triangleFreeNeighbors G x).card := by
    rw [Finset.card_sdiff]
    have heq :
        (secondOrderDefectGraph G).neighborFinset x ∩ S =
          triangleFreeNeighbors G x := by
      simpa [S, B, Finset.inter_assoc, Finset.inter_left_comm,
        Finset.inter_comm] using hinter
    rw [heq]
  change
    ((G.induce (G.neighborSet x)).edgeFinset.card = 3 ∧ R.card = 0) ∨
      ((G.induce (G.neighborSet x)).edgeFinset.card = 4 ∧ R.card = 2)
  rcases hprofile with hfirst | hsecond
  · left
    refine ⟨hfirst.2.2, ?_⟩
    rw [hRcard, hS, hfirst.2.1]
  · right
    refine ⟨hsecond.2.2, ?_⟩
    rw [hRcard, hS, hsecond.2.1]

/-- No original bin-zero neighbor of the rare bin-three vertex is adjacent
to a high vertex.  At every high root, the unique common neighbor with the
bin-three vertex is the root's bin-one matching partner. -/
theorem squareOrderNine_threeHigh_secondProfile_binThree_binZero_neighbor_not_highAdjacent
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
    {x y a : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ squareOrderNineLowIncidenceBin G 0)
    (hxy : G.Adj x y) (ha : a ∈ squareOrderHighVertices G 9) :
    ¬ G.Adj a y := by
  intro hay
  let B := squareOrderNineLowIncidenceBin G
  have hpartner :=
    squareOrderNine_threeHigh_secondProfile_binThree_unique_binOne_partner_at_highRoot
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx ha
  have hpartnerNonempty :
      (G.neighborFinset a ∩ G.neighborFinset x ∩ B 1).Nonempty := by
    rw [← Finset.card_pos, hpartner]
    norm_num
  obtain ⟨p, hp⟩ := hpartnerNonempty
  have hpParts := Finset.mem_inter.mp hp
  have hpCommonParts := Finset.mem_inter.mp hpParts.1
  have hpCommon : p ∈ G.neighborFinset a ∩ G.neighborFinset x :=
    Finset.mem_inter.mpr hpCommonParts
  have hyCommon : y ∈ G.neighborFinset a ∩ G.neighborFinset x :=
    Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset a y).mpr hay,
      (G.mem_neighborFinset x y).mpr hxy⟩
  have hax : a ≠ x := by
    intro h
    subst a
    have hxLow := (Finset.mem_filter.mp hx).1
    exact (Finset.mem_sdiff.mp hxLow).2 ha
  have hle := common_le_one_of_not_containsC4 hfree a x hax
  have hpy : p = y := Finset.card_le_one.mp hle p hpCommon y hyCommon
  have hkp : squareOrderHighIncidenceCount G 9 p = 1 :=
    (Finset.mem_filter.mp hpParts.2).2
  have hky : squareOrderHighIncidenceCount G 9 y = 0 :=
    (Finset.mem_filter.mp hy).2
  rw [hpy] at hkp
  omega

/-- In the four-local-triangle branch, the two canonical original bin-zero
neighbors outside the defect graph are adjacent.  Otherwise those two
vertices together with the three highs would be five independent
non-isolated vertices in the four-edge local graph. -/
theorem squareOrderNine_threeHigh_secondProfile_binThree_nondefect_binZero_pair_adjacent
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
    {x y z : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x)
    (hz : z ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x)
    (hyz : y ≠ z)
    (hloc : (G.induce (G.neighborSet x)).edgeFinset.card = 4) :
    G.Adj y z := by
  classical
  by_contra hnotYZ
  let H := squareOrderHighVertices G 9
  let L := G.induce (G.neighborSet x)
  have hyParts := Finset.mem_sdiff.mp hy
  have hzParts := Finset.mem_sdiff.mp hz
  have hxy : G.Adj x y :=
    (G.mem_neighborFinset x y).mp (Finset.mem_inter.mp hyParts.1).1
  have hxz : G.Adj x z :=
    (G.mem_neighborFinset x z).mp (Finset.mem_inter.mp hzParts.1).1
  have hyB := (Finset.mem_inter.mp hyParts.1).2
  have hzB := (Finset.mem_inter.mp hzParts.1).2
  have hxAll : G.neighborFinset x ∩ H = H := by
    have hkx : squareOrderHighIncidenceCount G 9 x = 3 :=
      (Finset.mem_filter.mp hx).2
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.inter_subset_right
    · change H.card ≤ squareOrderHighIncidenceCount G 9 x
      rw [hkx, hhigh]
  have highAdj (a : V) (ha : a ∈ H) : G.Adj x a := by
    have haN : a ∈ G.neighborFinset x := by
      have : a ∈ G.neighborFinset x ∩ H := by rw [hxAll]; exact ha
      exact (Finset.mem_inter.mp this).1
    exact (G.mem_neighborFinset x a).mp haN
  let highEmb : ↥H ↪ ↥(G.neighborSet x) :=
    ⟨fun a => ⟨a.1, highAdj a.1 a.2⟩, by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun q : ↥(G.neighborSet x) => q.1) hab⟩
  let SH : Finset ↥(G.neighborSet x) := Finset.univ.map highEmb
  let y' : ↥(G.neighborSet x) := ⟨y, hxy⟩
  let z' : ↥(G.neighborSet x) := ⟨z, hxz⟩
  let SR : Finset ↥(G.neighborSet x) := {y', z'}
  let S : Finset ↥(G.neighborSet x) := SH ∪ SR
  have hSHcard : SH.card = 3 := by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_coe, hhigh]
  have hSRcard : SR.card = 2 := by
    simp [SR, y', z', hyz]
  have hdisj : Disjoint SH SR := by
    rw [Finset.disjoint_left]
    intro u huH huR
    have huHigh : u.1 ∈ H := by
      simp only [SH, Finset.mem_map, Finset.mem_univ, true_and] at huH
      obtain ⟨a, rfl⟩ := huH
      exact a.2
    have huPair : u = y' ∨ u = z' := by simpa [SR] using huR
    rcases huPair with rfl | rfl
    · have hyLow := (Finset.mem_filter.mp hyB).1
      exact (Finset.mem_sdiff.mp hyLow).2 huHigh
    · have hzLow := (Finset.mem_filter.mp hzB).1
      exact (Finset.mem_sdiff.mp hzLow).2 huHigh
  have hScard : S.card = 5 := by
    change (SH ∪ SR).card = 5
    rw [Finset.card_union_of_disjoint hdisj, hSHcard, hSRcard]
  have hSind : ∀ ⦃u⦄, u ∈ S → ∀ ⦃v⦄, v ∈ S → u ≠ v → ¬ L.Adj u v := by
    intro u hu v hv huv huvAdj
    have hGuv : G.Adj u.1 v.1 := huvAdj
    rcases Finset.mem_union.mp hu with huH | huR <;>
      rcases Finset.mem_union.mp hv with hvH | hvR
    · have huHigh : u.1 ∈ H := by
        simp only [SH, Finset.mem_map, Finset.mem_univ, true_and] at huH
        obtain ⟨a, rfl⟩ := huH
        exact a.2
      have hvHigh : v.1 ∈ H := by
        simp only [SH, Finset.mem_map, Finset.mem_univ, true_and] at hvH
        obtain ⟨a, rfl⟩ := hvH
        exact a.2
      have hu10 : G.degree u.1 = 10 := (Finset.mem_filter.mp huHigh).2
      have hv10 : G.degree v.1 = 10 := (Finset.mem_filter.mp hvHigh).2
      rcases hcover hGuv with hu9 | hv9 <;> omega
    · have huHigh : u.1 ∈ H := by
        simp only [SH, Finset.mem_map, Finset.mem_univ, true_and] at huH
        obtain ⟨a, rfl⟩ := huH
        exact a.2
      have hvPair : v = y' ∨ v = z' := by simpa [SR] using hvR
      rcases hvPair with rfl | rfl
      · exact squareOrderNine_threeHigh_secondProfile_binThree_binZero_neighbor_not_highAdjacent
          G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hyB hxy huHigh hGuv
      · exact squareOrderNine_threeHigh_secondProfile_binThree_binZero_neighbor_not_highAdjacent
          G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hzB hxz huHigh hGuv
    · have hvHigh : v.1 ∈ H := by
        simp only [SH, Finset.mem_map, Finset.mem_univ, true_and] at hvH
        obtain ⟨a, rfl⟩ := hvH
        exact a.2
      have huPair : u = y' ∨ u = z' := by simpa [SR] using huR
      rcases huPair with rfl | rfl
      · exact squareOrderNine_threeHigh_secondProfile_binThree_binZero_neighbor_not_highAdjacent
          G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hyB hxy hvHigh hGuv.symm
      · exact squareOrderNine_threeHigh_secondProfile_binThree_binZero_neighbor_not_highAdjacent
          G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hzB hxz hvHigh hGuv.symm
    · have huPair : u = y' ∨ u = z' := by simpa [SR] using huR
      have hvPair : v = y' ∨ v = z' := by simpa [SR] using hvR
      rcases huPair with rfl | rfl <;> rcases hvPair with rfl | rfl
      · exact huv rfl
      · exact hnotYZ hGuv
      · exact hnotYZ hGuv.symm
      · exact huv rfl
  have hSpos : ∀ u ∈ S, 0 < L.degree u := by
    intro u hu
    rcases Finset.mem_union.mp hu with huH | huR
    · have huHigh : u.1 ∈ H := by
        simp only [SH, Finset.mem_map, Finset.mem_univ, true_and] at huH
        obtain ⟨a, rfl⟩ := huH
        exact a.2
      have hu10 : G.degree u.1 = 10 := (Finset.mem_filter.mp huHigh).2
      have hlocal := (squareOrder_degree_succ_highRoot_structure
        G hfree (by norm_num) hmin hcard hu10).2.2 ⟨x, (highAdj u.1 huHigh).symm⟩
      rw [degree_induce_neighborSet_eq_card_common] at hlocal
      rw [degree_induce_neighborSet_eq_card_common]
      have : (G.neighborFinset x ∩ G.neighborFinset u.1).card = 1 := by
        simpa [Finset.inter_comm] using hlocal
      omega
    · have huPair : u = y' ∨ u = z' := by simpa [SR] using huR
      rcases huPair with rfl | rfl
      · rw [degree_induce_neighborSet_eq_card_common]
        apply Nat.pos_of_ne_zero
        intro hzero
        have htf : y ∈ triangleFreeNeighbors G x :=
          (mem_triangleFreeNeighbors G x y).mpr ⟨hxy, hzero⟩
        exact hyParts.2 (by
          rw [secondOrderDefectGraph_neighborFinset G x]
          exact Finset.mem_union_right _ htf)
      · rw [degree_induce_neighborSet_eq_card_common]
        apply Nat.pos_of_ne_zero
        intro hzero
        have htf : z ∈ triangleFreeNeighbors G x :=
          (mem_triangleFreeNeighbors G x z).mpr ⟨hxz, hzero⟩
        exact hzParts.2 (by
          rw [secondOrderDefectGraph_neighborFinset G x]
          exact Finset.mem_union_right _ htf)
  have hbound := independent_nonisolated_card_le_edges L S hSind hSpos
  rw [hScard, hloc] at hbound
  omega

/-- Every canonical original bin-zero neighbor outside the bin-three defect
neighborhood has regular defect type `(B₀,B₁,B₃)=(5,3,0)`.  The exceptional
type would have a bin-three defect neighbor, necessarily the unique vertex
`x` itself. -/
theorem squareOrderNine_threeHigh_secondProfile_nondefect_binZero_is_regular
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
    {x y : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    (D.neighborFinset y ∩ B 0).card = 5 ∧
      (D.neighborFinset y ∩ B 1).card = 3 ∧
      (D.neighborFinset y ∩ B 3).card = 0 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  have hyParts := Finset.mem_sdiff.mp hy
  have hyB : y ∈ B 0 := (Finset.mem_inter.mp hyParts.1).2
  have hyNotDx : y ∉ D.neighborFinset x := hyParts.2
  have hB3card : (B 3).card = 1 := by
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 3) (by omega), hc3]
  have htype :=
    squareOrderNine_threeHigh_secondProfile_binZero_defect_neighbor_dichotomy
      G hfree hmin hcover hcard hp hhigh hc2 hc4 hyB
  dsimp only at htype
  rcases htype with hregular | hexceptional
  · exact hregular
  · exfalso
    have hinter : D.neighborFinset y ∩ B 3 = B 3 := by
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.inter_subset_right
      · rw [hexceptional.2.2, hB3card]
    have hxDy : x ∈ D.neighborFinset y := by
      have hxInter : x ∈ D.neighborFinset y ∩ B 3 := by
        rw [hinter]
        exact hx
      exact (Finset.mem_inter.mp hxInter).1
    have hyDx : y ∈ D.neighborFinset x :=
      (D.mem_neighborFinset x y).mpr
        ((D.adj_comm y x).mp ((D.mem_neighborFinset y x).mp hxDy))
    exact hyNotDx hyDx

/-- If a bin-one vertex lies in both defect fibers of the forced adjacent
bin-zero pair, at least one of its two incident defect edges is antipodal.
The defect two-path has the bin-three vertex as an external common owner, so
its two edges cannot both be original. -/
theorem squareOrderNine_threeHigh_secondProfile_trianglePair_common_binOne_forces_antipodal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {x y z p : V}
    (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hp : p ∈ squareOrderNineLowIncidenceBin G 1)
    (hyz : y ≠ z)
    (hxy : G.Adj x y) (hxz : G.Adj x z)
    (hDyp : (secondOrderDefectGraph G).Adj y p)
    (hDpz : (secondOrderDefectGraph G).Adj p z) :
    (antipodalGraph G).Adj y p ∨ (antipodalGraph G).Adj p z := by
  have hnotDyz : ¬ (secondOrderDefectGraph G).Adj y z :=
    not_secondOrderDefect_adj_of_commonNeighbor
      G hfree hyz hxy.symm hxz.symm
  have hpx : p ≠ x := by
    intro h
    subst p
    have hkx : squareOrderHighIncidenceCount G 9 x = 3 :=
      (Finset.mem_filter.mp hx).2
    have hk1 : squareOrderHighIncidenceCount G 9 x = 1 :=
      (Finset.mem_filter.mp hp).2
    omega
  have hnotBoth :=
    not_both_originalEdges_of_induced_secondOrderDefect_path_of_commonOwner
      G hfree hDyp hDpz hyz hnotDyz hxy hxz hpx
  change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj y p at hDyp
  change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj p z at hDpz
  rcases hDyp with hanti | htf
  · exact Or.inl hanti
  · rcases hDpz with hanti | htf'
    · exact Or.inr hanti
    · exfalso
      exact hnotBoth ⟨
        ((mem_triangleFreeNeighbors G y p).mp htf).1,
        ((mem_triangleFreeNeighbors G p z).mp htf').1⟩

/-- A bin-zero neighbor of the universal bin-three vertex has no original
bin-one neighbor.  A hypothetical bin-one neighbor and the bin-three vertex
would be two common neighbors of the bin-zero vertex and the bin-one
vertex's unique high root. -/
theorem squareOrderNine_threeHigh_binThree_binZero_neighbor_not_binOneAdjacent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    {x y z : V}
    (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ squareOrderNineLowIncidenceBin G 0)
    (hz : z ∈ squareOrderNineLowIncidenceBin G 1)
    (hxy : G.Adj x y) :
    ¬ G.Adj y z := by
  intro hyz
  let H := squareOrderHighVertices G 9
  have hxCard : (G.neighborFinset x ∩ H).card = 3 :=
    (Finset.mem_filter.mp hx).2
  have hzCard : (G.neighborFinset z ∩ H).card = 1 :=
    (Finset.mem_filter.mp hz).2
  have hxAll : G.neighborFinset x ∩ H = H := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.inter_subset_right
    · rw [hxCard, hhigh]
  obtain ⟨r, hr⟩ := Finset.card_pos.mp (by omega :
    0 < (G.neighborFinset z ∩ H).card)
  have hrParts := Finset.mem_inter.mp hr
  have hrx : G.Adj r x := by
    have : r ∈ G.neighborFinset x ∩ H := by
      rw [hxAll]
      exact hrParts.2
    exact (G.adj_comm x r).mp
      ((G.mem_neighborFinset x r).mp (Finset.mem_inter.mp this).1)
  have hrz : G.Adj r z :=
    (G.adj_comm z r).mp ((G.mem_neighborFinset z r).mp hrParts.1)
  have hyr : y ≠ r := by
    intro hyr
    subst r
    have hyLow := (Finset.mem_filter.mp hy).1
    exact (Finset.mem_sdiff.mp hyLow).2 hrParts.2
  have hxz : x ≠ z := by
    intro hxz
    subst z
    omega
  have hxCommon : x ∈ G.neighborFinset y ∩ G.neighborFinset r :=
    Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset y x).mpr hxy.symm,
      (G.mem_neighborFinset r x).mpr hrx⟩
  have hzCommon : z ∈ G.neighborFinset y ∩ G.neighborFinset r :=
    Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset y z).mpr hyz,
      (G.mem_neighborFinset r z).mpr hrz⟩
  have hle := (not_containsC4_iff_forall_common_le_one G).mp hfree y r hyr
  exact hxz (Finset.card_le_one.mp hle x hxCommon z hzCommon)

/-- Consequently every defect edge from such a bin-zero neighbor into the
bin-one core is antipodal: its triangle-free/original alternative is ruled
out by the preceding two-common-neighbor obstruction. -/
theorem squareOrderNine_threeHigh_binThree_binZero_neighbor_binOne_defect_antipodal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    {x y z : V}
    (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ squareOrderNineLowIncidenceBin G 0)
    (hz : z ∈ squareOrderNineLowIncidenceBin G 1)
    (hxy : G.Adj x y)
    (hDyz : (secondOrderDefectGraph G).Adj y z) :
    (antipodalGraph G).Adj y z := by
  change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj y z at hDyz
  rcases hDyz with hanti | htf
  · exact hanti
  · exfalso
    exact (squareOrderNine_threeHigh_binThree_binZero_neighbor_not_binOneAdjacent
      G hfree hhigh hx hy hz hxy)
      (((mem_triangleFreeNeighbors G y z).mp htf).1)

/-- Each endpoint of the forced nondefect bin-zero pair therefore sends
exactly three antipodal edges into the bin-one core. -/
theorem squareOrderNine_threeHigh_secondProfile_nondefect_binZero_binOne_antipodal_card
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
    {x y : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x) :
    (antipodalNeighbors G y ∩ squareOrderNineLowIncidenceBin G 1).card = 3 := by
  classical
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  have hyParts := Finset.mem_sdiff.mp hy
  have hyB : y ∈ B 0 := (Finset.mem_inter.mp hyParts.1).2
  have hxy : G.Adj x y :=
    (G.mem_neighborFinset x y).mp (Finset.mem_inter.mp hyParts.1).1
  have htype :=
    squareOrderNine_threeHigh_secondProfile_nondefect_binZero_is_regular
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy
  dsimp only at htype
  have heq : D.neighborFinset y ∩ B 1 = antipodalNeighbors G y ∩ B 1 := by
    ext z
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hzD, hzB⟩
      have hanti :=
        squareOrderNine_threeHigh_binThree_binZero_neighbor_binOne_defect_antipodal
          G hfree hhigh hx hyB hzB hxy
          ((D.mem_neighborFinset y z).mp hzD)
      exact ⟨(antipodalGraph_adj G y z).mp hanti, hzB⟩
    · rintro ⟨hzA, hzB⟩
      have hanti : (antipodalGraph G).Adj y z :=
        (antipodalGraph_adj G y z).mpr hzA
      have hD : D.Adj y z := by
        change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj y z
        exact Or.inl hanti
      exact ⟨(D.mem_neighborFinset y z).mpr hD, hzB⟩
  rw [← heq]
  exact htype.2.1

/-- In the q=9 three-high sector, both colors of the second-order defect
graph have edge count divisible by three.  This is a genuinely global
constraint: `G` has 366 edges, its triangular edges occur in triples, and
the defect graph has 297 edges by global excess conservation. -/
theorem squareOrderNine_threeHigh_colored_defect_edge_card_dvd_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hhigh : (squareOrderHighVertices G 9).card = 3) :
    3 ∣ (triangleFreeEdgeGraph G).edgeFinset.card ∧
      3 ∣ (antipodalGraph G).edgeFinset.card := by
  classical
  let T := triangleFreeEdgeGraph G
  let H := triangularEdgeGraph G
  let A := antipodalGraph G
  let D := secondOrderDefectGraph G
  have hGedges : G.edgeFinset.card = 366 := by
    rcases squareOrder_even_cube_add_card_high
        G hfree (by norm_num) hmin hcover (by omega) with ⟨k, hk⟩
    rw [hhigh] at hk
    change 9 * 9 * 9 + 3 = k + k at hk
    have hhand := G.sum_degrees_eq_twice_card_edges
    have hexcess := squareOrder_sum_degreeExcess_eq_card_high
      G hfree (by norm_num) hmin hcover (by omega)
    rw [hhigh] at hexcess
    have hsum : (∑ x : V, G.degree x) = 732 := by
      calc
        (∑ x : V, G.degree x) =
            ∑ x : V, (9 + (G.degree x - 9)) := by
              apply Finset.sum_congr rfl
              intro x _
              have hxmin := hmin x
              omega
        _ = 9 * Fintype.card V +
            ∑ x : V, (G.degree x - 9) := by
              rw [Finset.sum_add_distrib]
              simp [Nat.mul_comm]
        _ = 732 := by rw [hcard, hexcess]
    rw [hsum] at hhand
    omega

  have hTle : T ≤ G := by
    intro x y hxy
    exact ((mem_triangleFreeNeighbors G x y).mp
      ((triangleFreeEdgeGraph_adj G x y).mp hxy)).1
  have hGHpartition :
      G.edgeFinset.card = H.edgeFinset.card + T.edgeFinset.card := by
    have heq : H.edgeFinset = G.edgeFinset \ T.edgeFinset := by
      ext e
      simp [H, T, triangularEdgeGraph]
    rw [heq, Finset.card_sdiff_of_subset (edgeFinset_mono hTle)]
    have hle := Finset.card_le_card (edgeFinset_mono hTle)
    omega
  have hHedges : H.edgeFinset.card =
      3 * (H.cliqueFinset 3).card :=
    (triangularEdgeGraph_locallyLinear_of_not_containsC4 G hfree).card_edgeFinset
  have hTdvd : 3 ∣ T.edgeFinset.card := by
    refine ⟨122 - (H.cliqueFinset 3).card, ?_⟩
    rw [hGedges, hHedges] at hGHpartition
    omega
  have hDedges : D.edgeFinset.card = 297 := by
    have hglobal := two_mul_defectEdges_add_linearExcess_add_squareExcess_eq
      G hfree (d := 9) (q := 8) (by norm_num) hmin (by omega)
    have hexcess := squareOrder_sum_degreeExcess_eq_card_high
      G hfree (by norm_num) hmin hcover (by omega)
    rw [hhigh] at hexcess
    have hsquares :
        (∑ x : V, (G.degree x - 9) * (G.degree x - 9)) = 3 := by
      have hpoint : ∀ x : V,
          (G.degree x - 9) * (G.degree x - 9) = G.degree x - 9 := by
        intro x
        rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
            G hfree (by norm_num) hmin hcover (by omega) x with hx | hx <;>
          simp [hx]
      calc
        (∑ x : V, (G.degree x - 9) * (G.degree x - 9)) =
            ∑ x : V, (G.degree x - 9) := by
              apply Finset.sum_congr rfl
              intro x _
              exact hpoint x
        _ = 3 := hexcess
    rw [hcard, hexcess, hsquares] at hglobal
    dsimp [D]
    omega
  have hDApartition :
      D.edgeFinset.card = A.edgeFinset.card + T.edgeFinset.card := by
    have heq : D.edgeFinset = A.edgeFinset ∪ T.edgeFinset := by
      ext e
      simp [D, A, T, secondOrderDefectGraph]
    have hdisj : Disjoint A.edgeFinset T.edgeFinset := by
      rw [Finset.disjoint_left]
      intro e heA heT
      simp only [SimpleGraph.mem_edgeFinset] at heA heT
      rcases e with ⟨x, y⟩
      exact ((mem_antipodalNeighbors G x y).mp
        ((antipodalGraph_adj G x y).mp heA)).2.1
        (((mem_triangleFreeNeighbors G x y).mp
          ((triangleFreeEdgeGraph_adj G x y).mp heT)).1)
    rw [heq, Finset.card_union_of_disjoint hdisj]
  refine ⟨?_, ?_⟩
  · simpa [T] using hTdvd
  · rcases hTdvd with ⟨t, ht⟩
    refine ⟨99 - t, ?_⟩
    rw [hDedges] at hDApartition
    rw [ht] at hDApartition
    dsimp [A, T, D] at hDApartition ⊢
    omega

/-- For every low vertex in a three-high square-order-nine core, the total
high-incidence weight carried by its original neighbors is exactly three.
This is the pointwise original-adjacency identity `A k = 3 1`. -/
theorem squareOrderNine_threeHigh_sum_highIncidence_over_lowNeighborhood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    {y : V} (hy : y ∉ squareOrderHighVertices G 9) :
    (∑ z ∈ G.neighborFinset y, squareOrderHighIncidenceCount G 9 z) = 3 := by
  classical
  let H := squareOrderHighVertices G 9
  let k := squareOrderHighIncidenceCount G 9
  have hswap := sum_card_neighborFinset_inter_comm G (G.neighborFinset y) H
  change (∑ z ∈ G.neighborFinset y, k z) =
    ∑ a ∈ H, (G.neighborFinset a ∩ G.neighborFinset y).card at hswap
  rw [hswap]
  calc
    (∑ a ∈ H, (G.neighborFinset a ∩ G.neighborFinset y).card) =
        ∑ _a ∈ H, 1 := by
      apply Finset.sum_congr rfl
      intro a ha
      have ha10 : G.degree a = 10 := (Finset.mem_filter.mp ha).2
      have hay : a ≠ y := by
        intro h
        subst a
        exact hy ha
      exact squareOrder_card_common_highRoot_eq_one
        G hfree (by norm_num) hmin hcard ha10 hay
    _ = H.card := by simp
    _ = 3 := hhigh

/-- In the second three-high profile, a bin-zero vertex has three original
bin-one neighbors unless it is adjacent to the unique bin-three vertex; in
that exceptional case it has none. -/
theorem squareOrderNine_threeHigh_secondProfile_binZero_original_binOne_neighbors
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
    {x y : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ squareOrderNineLowIncidenceBin G 0) :
    (G.neighborFinset y ∩ squareOrderNineLowIncidenceBin G 1).card =
      if G.Adj y x then 0 else 3 := by
  classical
  by_cases hyx : G.Adj y x
  · simp only [hyx, if_true]
    rw [Finset.card_eq_zero]
    ext z
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro hzN hzB
    exact (squareOrderNine_threeHigh_binThree_binZero_neighbor_not_binOneAdjacent
      G hfree hhigh hx hy hzB hyx.symm)
      ((G.mem_neighborFinset y z).mp hzN)
  · simp only [hyx, if_false]
    let H := squareOrderHighVertices G 9
    let B := squareOrderNineLowIncidenceBin G
    let k := squareOrderHighIncidenceCount G 9
    have hyNotHigh : y ∉ H :=
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).2
    have hsum : (∑ z ∈ G.neighborFinset y, k z) = 3 :=
      squareOrderNine_threeHigh_sum_highIncidence_over_lowNeighborhood
        G hfree hmin hcard hhigh hyNotHigh
    have hb2 : B 2 = ∅ := by
      rw [← Finset.card_eq_zero,
        squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
          G hp (i := 2) (by omega), hc2]
    have hb3card : (B 3).card = 1 := by
      rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 3) (by omega), hc3]
    have hb4 : B 4 = ∅ := by
      rw [← Finset.card_eq_zero,
        squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
          G hp (i := 4) (by omega), hc4]
    have hpoint : ∀ z ∈ G.neighborFinset y,
        k z = if z ∈ B 1 then 1 else 0 := by
      intro z hz
      by_cases hzH : z ∈ H
      · have hzero : k z = 0 := by
          unfold k squareOrderHighIncidenceCount
          rw [Finset.card_eq_zero]
          ext a
          simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
          intro hza haH
          exact hp.high_independent hzH haH
            ((G.mem_neighborFinset z a).mp hza)
        have hzNotB : z ∉ B 1 := by
          intro hzB
          exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hzB).1).2 hzH
        simp [hzero, hzNotB]
      · have hzLow : z ∈ Finset.univ \ H :=
          Finset.mem_sdiff.mpr ⟨by simp, hzH⟩
        have hkle : k z ≤ 4 := by
          rcases hp.degree_dichotomy z with hlo | hhi
          · have := hp.low_incidence_bound hlo
            change 2 * k z ≤ 9 at this
            omega
          · exact (hzH (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
        have hkNot2 : k z ≠ 2 := by
          intro hk
          have : z ∈ B 2 := Finset.mem_filter.mpr ⟨hzLow, hk⟩
          simpa [hb2] using this
        have hkNot3 : k z ≠ 3 := by
          intro hk
          have hzB3 : z ∈ B 3 := Finset.mem_filter.mpr ⟨hzLow, hk⟩
          have hzx : z = x := Finset.card_le_one.mp (by omega) z hzB3 x hx
          subst z
          exact hyx ((G.mem_neighborFinset y x).mp hz)
        have hkNot4 : k z ≠ 4 := by
          intro hk
          have : z ∈ B 4 := Finset.mem_filter.mpr ⟨hzLow, hk⟩
          simpa [hb4] using this
        have hk01 : k z = 0 ∨ k z = 1 := by omega
        rcases hk01 with hk0 | hk1
        · have hzNotB : z ∉ B 1 := by
            intro hzB
            have hk := (Finset.mem_filter.mp hzB).2
            change k z = 1 at hk
            omega
          simp [hk0, hzNotB]
        · have hzB : z ∈ B 1 := Finset.mem_filter.mpr ⟨hzLow, hk1⟩
          simp [hk1, hzB]
    calc
      (G.neighborFinset y ∩ B 1).card =
          ∑ z ∈ G.neighborFinset y, if z ∈ B 1 then 1 else 0 := by simp
      _ = ∑ z ∈ G.neighborFinset y, k z := by
        apply Finset.sum_congr rfl
        intro z hz
        exact (hpoint z hz).symm
      _ = 3 := hsum

/-- The second three-high profile has exactly 141 oriented original
incidences from bin zero to bin one.  Equivalently, its original low-bin
quotient entry is `47 · 3`: the three bin-zero neighbors of the unique
bin-three vertex receive no bin-one service, and every other one receives
exactly three. -/
theorem squareOrderNine_threeHigh_secondProfile_binZero_binOne_original_incidence
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    (∑ y ∈ squareOrderNineLowIncidenceBin G 0,
      (G.neighborFinset y ∩ squareOrderNineLowIncidenceBin G 1).card) = 141 := by
  classical
  let H := squareOrderHighVertices G 9
  let B := squareOrderNineLowIncidenceBin G
  let k := squareOrderHighIncidenceCount G 9
  have hc0 : squareOrderNineHighIncidenceHistogram G 0 = 53 := by
    rcases squareOrderNine_highIncidence_profile_of_three_high
        G hcard hp hhigh with hfirst | hsecond
    · rw [hfirst.2.2.2.1] at hc3
      omega
    · exact hsecond.1
  have hkzero : ∀ y ∈ H, k y = 0 := by
    intro y hyH
    unfold k squareOrderHighIncidenceCount
    rw [Finset.card_eq_zero]
    ext a
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro hya haH
    exact hp.high_independent hyH haH ((G.mem_neighborFinset y a).mp hya)
  have hhistPartition :
      (Finset.univ.filter fun y => k y = 0) = H ∪ B 0 := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hky
      by_cases hyH : y ∈ H
      · exact Or.inl hyH
      · exact Or.inr (Finset.mem_filter.mpr
          ⟨Finset.mem_sdiff.mpr ⟨by simp, hyH⟩, hky⟩)
    · rintro (hyH | hyB)
      · exact hkzero y hyH
      · exact (Finset.mem_filter.mp hyB).2
  have hdisj : Disjoint H (B 0) := by
    rw [Finset.disjoint_left]
    intro y hyH hyB
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hyB).1).2 hyH
  have hB0card : (B 0).card = 50 := by
    have hcardUnion := congrArg Finset.card hhistPartition
    rw [Finset.card_union_of_disjoint hdisj] at hcardUnion
    change squareOrderNineHighIncidenceHistogram G 0 = H.card + (B 0).card at hcardUnion
    rw [hc0, hhigh] at hcardUnion
    omega
  have hxCensus :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_neighborhood_census
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hxCensus
  have hxB0card : (G.neighborFinset x ∩ B 0).card = 3 := hxCensus.2.2
  calc
    (∑ y ∈ B 0, (G.neighborFinset y ∩ B 1).card) =
        ∑ y ∈ B 0, if y ∈ G.neighborFinset x then 0 else 3 := by
      apply Finset.sum_congr rfl
      intro y hyB0
      have hpoint :=
        squareOrderNine_threeHigh_secondProfile_binZero_original_binOne_neighbors
          G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hyB0
      by_cases hyx : G.Adj y x
      · have hxyMem : y ∈ G.neighborFinset x :=
          (G.mem_neighborFinset x y).mpr hyx.symm
        simpa [hyx, hxyMem] using hpoint
      · have hxyNotMem : y ∉ G.neighborFinset x := by
          intro h
          exact hyx ((G.adj_comm x y).mp ((G.mem_neighborFinset x y).mp h))
        simpa [hyx, hxyNotMem] using hpoint
    _ = 3 * (B 0 \ G.neighborFinset x).card := by
      have heq : (B 0).filter (fun y => ¬ G.Adj x y) =
          B 0 \ G.neighborFinset x := by
        ext y
        simp [G.mem_neighborFinset]
      rw [← heq]
      simp [Finset.sum_ite, Nat.mul_comm, G.mem_neighborFinset]
    _ = 141 := by
      rw [Finset.card_sdiff]
      · rw [hB0card]
        rw [hxB0card]

/-- Original neighbors of a low q=9 vertex partition into its high
neighbors and the five low-incidence bins. -/
theorem squareOrderNine_originalNeighbor_lowBin_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hp : SquareOrderNonregularSectorProfile G 9)
    {x : V} (hx : x ∉ squareOrderHighVertices G 9) :
    (∑ j ∈ Finset.range 5,
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G j).card) +
        squareOrderHighIncidenceCount G 9 x = G.degree x := by
  classical
  let H := squareOrderHighVertices G 9
  let k := squareOrderHighIncidenceCount G 9
  let S := G.neighborFinset x \ H
  have hlow {y : V} (hy : y ∈ S) : G.degree y = 9 := by
    have hyNotHigh := (Finset.mem_sdiff.mp hy).2
    rcases hp.degree_dichotomy y with hlo | hhi
    · exact hlo
    · exact (hyNotHigh (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
  have hklt {y : V} (hy : y ∈ S) : k y < 5 := by
    have hb := hp.low_incidence_bound (hlow hy)
    change 2 * k y ≤ 9 at hb
    omega
  have hfiber (j : ℕ) :
      {y ∈ S | k y = j} =
        G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G j := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hyS, hky⟩
      have hyParts := Finset.mem_sdiff.mp hyS
      exact ⟨hyParts.1, Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨by simp, hyParts.2⟩, hky⟩⟩
    · rintro ⟨hyN, hyB⟩
      have hyLow := (Finset.mem_filter.mp hyB).1
      exact ⟨Finset.mem_sdiff.mpr
        ⟨hyN, (Finset.mem_sdiff.mp hyLow).2⟩,
        (Finset.mem_filter.mp hyB).2⟩
  have hmaps : (S : Set V).MapsTo k (Finset.range 5) := by
    intro y hy
    exact Finset.mem_range.mpr (hklt hy)
  have hpartition :
      (∑ j ∈ Finset.range 5,
        (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G j).card) =
          S.card := by
    calc
      _ = ∑ j ∈ Finset.range 5, #{y ∈ S | k y = j} := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hfiber]
      _ = S.card := (Finset.card_eq_sum_card_fiberwise hmaps).symm
  rw [hpartition]
  dsimp [S]
  rw [Finset.card_sdiff]
  rw [Finset.inter_comm H (G.neighborFinset x), G.card_neighborFinset_eq_degree]
  change G.degree x - k x + k x = G.degree x
  rw [Nat.sub_add_cancel]
  exact Finset.card_le_card Finset.inter_subset_left

/-- The second three-high profile contains exactly fifty low bin-zero
vertices (the zero-incidence histogram also contains the three highs). -/
theorem squareOrderNine_threeHigh_secondProfile_binZero_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1) :
    (squareOrderNineLowIncidenceBin G 0).card = 50 := by
  classical
  let H := squareOrderHighVertices G 9
  let B := squareOrderNineLowIncidenceBin G
  let k := squareOrderHighIncidenceCount G 9
  have hc0 : squareOrderNineHighIncidenceHistogram G 0 = 53 := by
    rcases squareOrderNine_highIncidence_profile_of_three_high
        G hcard hp hhigh with hfirst | hsecond
    · rw [hfirst.2.2.2.1] at hc3
      omega
    · exact hsecond.1
  have hkzero : ∀ y ∈ H, k y = 0 := by
    intro y hyH
    unfold k squareOrderHighIncidenceCount
    rw [Finset.card_eq_zero]
    ext a
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro hya haH
    exact hp.high_independent hyH haH ((G.mem_neighborFinset y a).mp hya)
  have hpartition : (Finset.univ.filter fun y => k y = 0) = H ∪ B 0 := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hky
      by_cases hyH : y ∈ H
      · exact Or.inl hyH
      · exact Or.inr (Finset.mem_filter.mpr
          ⟨Finset.mem_sdiff.mpr ⟨by simp, hyH⟩, hky⟩)
    · rintro (hyH | hyB)
      · exact hkzero y hyH
      · exact (Finset.mem_filter.mp hyB).2
  have hdisj : Disjoint H (B 0) := by
    rw [Finset.disjoint_left]
    intro y hyH hyB
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hyB).1).2 hyH
  have hcards := congrArg Finset.card hpartition
  rw [Finset.card_union_of_disjoint hdisj] at hcards
  change squareOrderNineHighIncidenceHistogram G 0 = H.card + (B 0).card at hcards
  rw [hc0, hhigh] at hcards
  change (B 0).card = 50
  omega

/-- Complete oriented original-adjacency quotient on the nonempty low bins
of the second three-high profile.  The entries are
`B₀B₀=306, B₀B₁=141, B₀B₃=3, B₁B₁=72, B₁B₃=3`; symmetry supplies the
transposed entries. -/
theorem squareOrderNine_threeHigh_secondProfile_original_lowBin_quotient
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    let B := squareOrderNineLowIncidenceBin G
    (∑ y ∈ B 0, (G.neighborFinset y ∩ B 0).card) = 306 ∧
      (∑ y ∈ B 0, (G.neighborFinset y ∩ B 1).card) = 141 ∧
      (∑ y ∈ B 0, (G.neighborFinset y ∩ B 3).card) = 3 ∧
      (∑ y ∈ B 1, (G.neighborFinset y ∩ B 1).card) = 72 ∧
      (∑ y ∈ B 1, (G.neighborFinset y ∩ B 3).card) = 3 := by
  classical
  dsimp only
  let H := squareOrderHighVertices G 9
  let B := squareOrderNineLowIncidenceBin G
  have hb2 : B 2 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 2) (by omega), hc2]
  have hb4 : B 4 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 4) (by omega), hc4]
  have hB0card : (B 0).card = 50 :=
    squareOrderNine_threeHigh_secondProfile_binZero_card
      G hcard hp hhigh hc3
  have hmarked :=
    squareOrderNine_threeHigh_secondProfile_marked_core_cardinalities
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hmarked
  have hB1card : (B 1).card = 27 := hmarked.1
  have hB3card : (B 3).card = 1 := by
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 3) (by omega), hc3]
  have hxCensus :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_neighborhood_census
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hxCensus
  have hxB0 : (G.neighborFinset x ∩ B 0).card = 3 := hxCensus.2.2
  have hxB1 : (G.neighborFinset x ∩ B 1).card = 3 := hxCensus.2.1
  have h03 : (∑ y ∈ B 0, (G.neighborFinset y ∩ B 3).card) = 3 := by
    have hswap := sum_card_neighborFinset_inter_comm G (B 0) (B 3)
    rw [hswap]
    have hsingle : B 3 = {x} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hx, fun y hy => Finset.card_le_one.mp (by omega) y hy x hx⟩
    rw [hsingle]
    simpa [G.adj_comm, Finset.inter_comm] using hxB0
  have h13 : (∑ y ∈ B 1, (G.neighborFinset y ∩ B 3).card) = 3 := by
    have hswap := sum_card_neighborFinset_inter_comm G (B 1) (B 3)
    rw [hswap]
    have hsingle : B 3 = {x} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hx, fun y hy => Finset.card_le_one.mp (by omega) y hy x hx⟩
    rw [hsingle]
    simpa [G.adj_comm, Finset.inter_comm] using hxB1
  have h01 : (∑ y ∈ B 0, (G.neighborFinset y ∩ B 1).card) = 141 :=
    squareOrderNine_threeHigh_secondProfile_binZero_binOne_original_incidence
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  have hrow0point : ∀ y ∈ B 0,
      (G.neighborFinset y ∩ B 0).card +
        (G.neighborFinset y ∩ B 1).card +
        (G.neighborFinset y ∩ B 3).card = 9 := by
    intro y hy
    have hyLow := (Finset.mem_filter.mp hy).1
    have hyNotHigh : y ∉ H := (Finset.mem_sdiff.mp hyLow).2
    have hyDegree : G.degree y = 9 := by
      rcases hp.degree_dichotomy y with hlo | hhi
      · exact hlo
      · exact (hyNotHigh (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
    have hky : squareOrderHighIncidenceCount G 9 y = 0 :=
      (Finset.mem_filter.mp hy).2
    have hpnt := squareOrderNine_originalNeighbor_lowBin_partition G hp hyNotHigh
    change (∑ j ∈ Finset.range 5,
      (G.neighborFinset y ∩ B j).card) +
        squareOrderHighIncidenceCount G 9 y = G.degree y at hpnt
    norm_num [Finset.sum_range_succ, hb2, hb4, hky, hyDegree] at hpnt
    omega
  have hrow0 :
      (∑ y ∈ B 0, (G.neighborFinset y ∩ B 0).card) +
        (∑ y ∈ B 0, (G.neighborFinset y ∩ B 1).card) +
        (∑ y ∈ B 0, (G.neighborFinset y ∩ B 3).card) = 450 := by
    calc
      _ = ∑ y ∈ B 0,
          ((G.neighborFinset y ∩ B 0).card +
            (G.neighborFinset y ∩ B 1).card +
            (G.neighborFinset y ∩ B 3).card) := by
              simp [Finset.sum_add_distrib]
      _ = ∑ _y ∈ B 0, 9 := by
        apply Finset.sum_congr rfl
        intro y hy
        exact hrow0point y hy
      _ = 450 := by simp [hB0card]
  have h00 : (∑ y ∈ B 0, (G.neighborFinset y ∩ B 0).card) = 306 := by
    omega
  have h10 : (∑ y ∈ B 1, (G.neighborFinset y ∩ B 0).card) = 141 := by
    rw [← sum_card_neighborFinset_inter_comm G (B 0) (B 1)]
    exact h01
  have hrow1point : ∀ y ∈ B 1,
      (G.neighborFinset y ∩ B 0).card +
        (G.neighborFinset y ∩ B 1).card +
        (G.neighborFinset y ∩ B 3).card = 8 := by
    intro y hy
    have hyLow := (Finset.mem_filter.mp hy).1
    have hyNotHigh : y ∉ H := (Finset.mem_sdiff.mp hyLow).2
    have hyDegree : G.degree y = 9 := by
      rcases hp.degree_dichotomy y with hlo | hhi
      · exact hlo
      · exact (hyNotHigh (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
    have hky : squareOrderHighIncidenceCount G 9 y = 1 :=
      (Finset.mem_filter.mp hy).2
    have hpnt := squareOrderNine_originalNeighbor_lowBin_partition G hp hyNotHigh
    change (∑ j ∈ Finset.range 5,
      (G.neighborFinset y ∩ B j).card) +
        squareOrderHighIncidenceCount G 9 y = G.degree y at hpnt
    norm_num [Finset.sum_range_succ, hb2, hb4, hky, hyDegree] at hpnt
    omega
  have hrow1 :
      (∑ y ∈ B 1, (G.neighborFinset y ∩ B 0).card) +
        (∑ y ∈ B 1, (G.neighborFinset y ∩ B 1).card) +
        (∑ y ∈ B 1, (G.neighborFinset y ∩ B 3).card) = 216 := by
    calc
      _ = ∑ y ∈ B 1,
          ((G.neighborFinset y ∩ B 0).card +
            (G.neighborFinset y ∩ B 1).card +
            (G.neighborFinset y ∩ B 3).card) := by
              simp [Finset.sum_add_distrib]
      _ = ∑ _y ∈ B 1, 8 := by
        apply Finset.sum_congr rfl
        intro y hy
        exact hrow1point y hy
      _ = 216 := by simp [hB1card]
  have h11 : (∑ y ∈ B 1, (G.neighborFinset y ∩ B 1).card) = 72 := by
    omega
  exact ⟨h00, h01, h03, h11, h13⟩

/-- Undirected form of the complete second-profile original low-bin
quotient: 153 edges inside B₀, 141 across B₀--B₁, three across B₀--B₃,
36 edges inside B₁, and three across B₁--B₃. -/
theorem squareOrderNine_threeHigh_secondProfile_original_lowBin_edge_quotient
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    let B := squareOrderNineLowIncidenceBin G
    (G.induce (↑(B 0) : Set V)).edgeFinset.card = 153 ∧
      (∑ y ∈ B 0, (G.neighborFinset y ∩ B 1).card) = 141 ∧
      (∑ y ∈ B 0, (G.neighborFinset y ∩ B 3).card) = 3 ∧
      (G.induce (↑(B 1) : Set V)).edgeFinset.card = 36 ∧
      (∑ y ∈ B 1, (G.neighborFinset y ∩ B 3).card) = 3 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let K0 := G.induce (↑(B 0) : Set V)
  let K1 := G.induce (↑(B 1) : Set V)
  have hq := squareOrderNine_threeHigh_secondProfile_original_lowBin_quotient
    G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hq
  have hsum0 :
      (∑ y ∈ B 0, (G.neighborFinset y ∩ B 0).card) =
        ∑ y : ↥(↑(B 0) : Set V), K0.degree y := by
    rw [← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro y _hy
    exact (degree_induce_finset_eq_card_inter G (B 0) y).symm
  have hsum1 :
      (∑ y ∈ B 1, (G.neighborFinset y ∩ B 1).card) =
        ∑ y : ↥(↑(B 1) : Set V), K1.degree y := by
    rw [← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro y _hy
    exact (degree_induce_finset_eq_card_inter G (B 1) y).symm
  have hK0 : K0.edgeFinset.card = 153 := by
    have hhand := K0.sum_degrees_eq_twice_card_edges
    rw [← hsum0, hq.1] at hhand
    omega
  have hK1 : K1.edgeFinset.card = 36 := by
    have hhand := K1.sum_degrees_eq_twice_card_edges
    rw [← hsum1, hq.2.2.2.1] at hhand
    omega
  exact ⟨hK0, hq.2.1, hq.2.2.1, hK1, hq.2.2.2.2⟩

/-- The three bin-zero original neighbors of the rare bin-three vertex give
three disjoint eight-support rows in the B₀ block of the original adjacency
matrix.  Their total support mass is therefore 24. -/
theorem squareOrderNine_threeHigh_secondProfile_special_binZero_row_packing
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    (∀ y ∈ S, (G.neighborFinset y ∩ B 0).card = 8) ∧
      (∀ y ∈ S, ∀ z ∈ S, y ≠ z →
        Disjoint (G.neighborFinset y ∩ B 0)
          (G.neighborFinset z ∩ B 0)) ∧
      (∑ y ∈ S, (G.neighborFinset y ∩ B 0).card) = 24 := by
  classical
  dsimp only
  let H := squareOrderHighVertices G 9
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  have hb2 : B 2 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 2) (by omega), hc2]
  have hb3card : (B 3).card = 1 := by
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 3) (by omega), hc3]
  have hb4 : B 4 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 4) (by omega), hc4]
  have hScard : S.card = 3 := by
    have hcensus :=
      squareOrderNine_threeHigh_secondProfile_binThree_original_neighborhood_census
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
    exact hcensus.2.2
  have hrow : ∀ y ∈ S, (G.neighborFinset y ∩ B 0).card = 8 := by
    intro y hyS
    have hyParts := Finset.mem_inter.mp hyS
    have hyB0 := hyParts.2
    have hyx : G.Adj y x :=
      (G.adj_comm x y).mp ((G.mem_neighborFinset x y).mp hyParts.1)
    have hyB1zero :=
      squareOrderNine_threeHigh_secondProfile_binZero_original_binOne_neighbors
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hyB0
    simp [hyx] at hyB1zero
    have hyB1card : (G.neighborFinset y ∩ B 1).card = 0 := by
      rw [hyB1zero]
      simp
    have hyLow := (Finset.mem_filter.mp hyB0).1
    have hyNotHigh : y ∉ H := (Finset.mem_sdiff.mp hyLow).2
    have hyDegree : G.degree y = 9 := by
      rcases hp.degree_dichotomy y with hlo | hhi
      · exact hlo
      · exact (hyNotHigh (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
    have hky : squareOrderHighIncidenceCount G 9 y = 0 :=
      (Finset.mem_filter.mp hyB0).2
    have hyB3card : (G.neighborFinset y ∩ B 3).card = 1 := by
      have hsingle : B 3 = {x} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hx, fun z hz => Finset.card_le_one.mp (by omega) z hz x hx⟩
      rw [hsingle]
      simp [G.mem_neighborFinset, hyx]
    have hpnt := squareOrderNine_originalNeighbor_lowBin_partition G hp hyNotHigh
    change (∑ j ∈ Finset.range 5, (G.neighborFinset y ∩ B j).card) +
      squareOrderHighIncidenceCount G 9 y = G.degree y at hpnt
    norm_num [Finset.sum_range_succ, hb2, hb4, hky, hyDegree,
      hyB1card, hyB3card] at hpnt
    omega
  have hdisj : ∀ y ∈ S, ∀ z ∈ S, y ≠ z →
      Disjoint (G.neighborFinset y ∩ B 0)
        (G.neighborFinset z ∩ B 0) := by
    intro y hyS z hzS hyz
    rw [Finset.disjoint_left]
    intro w hwy hwz
    have hyParts := Finset.mem_inter.mp hyS
    have hzParts := Finset.mem_inter.mp hzS
    have hwyParts := Finset.mem_inter.mp hwy
    have hwzParts := Finset.mem_inter.mp hwz
    have hxCommon : x ∈ G.neighborFinset y ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset y x).mpr
          ((G.adj_comm x y).mp ((G.mem_neighborFinset x y).mp hyParts.1)),
        (G.mem_neighborFinset z x).mpr
          ((G.adj_comm x z).mp ((G.mem_neighborFinset x z).mp hzParts.1))⟩
    have hwCommon : w ∈ G.neighborFinset y ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr ⟨hwyParts.1, hwzParts.1⟩
    have hxw : x ≠ w := by
      intro h
      subst w
      have hxk := (Finset.mem_filter.mp hx).2
      have hwk := (Finset.mem_filter.mp hwyParts.2).2
      omega
    have hle := (not_containsC4_iff_forall_common_le_one G).mp hfree y z hyz
    exact hxw (Finset.card_le_one.mp hle x hxCommon w hwCommon)
  refine ⟨hrow, hdisj, ?_⟩
  calc
    (∑ y ∈ S, (G.neighborFinset y ∩ B 0).card) =
        ∑ _y ∈ S, 8 := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hrow y hy
    _ = 24 := by simp [hScard]

/-- Deleting the special triple from its three disjoint B₀ row supports
leaves `24 - 2e` ordinary targets, where `e` is the number of original edges
inside the special triple.  This is the exact support form needed to read the
two local-triangle branches as 24 versus 22 targets. -/
theorem squareOrderNine_threeHigh_secondProfile_special_binZero_ordinary_support
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let W := S.biUnion fun y => G.neighborFinset y ∩ B 0
    (W \ S).card + 2 * (G.induce (↑S : Set V)).edgeFinset.card = 24 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let F : V → Finset V := fun y => G.neighborFinset y ∩ B 0
  let W := S.biUnion F
  let K := G.induce (↑S : Set V)
  change (W \ S).card + 2 * K.edgeFinset.card = 24
  have hpack :=
    squareOrderNine_threeHigh_secondProfile_special_binZero_row_packing
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hpack
  have hpair : ∀ y ∈ S, ∀ z ∈ S, y ≠ z → Disjoint (F y) (F z) := by
    exact hpack.2.1
  have hWcard : W.card = 24 := by
    rw [Finset.card_biUnion hpair]
    exact hpack.2.2
  have hinterEq : W ∩ S = S.biUnion (fun y => F y ∩ S) := by
    ext z
    simp [W, F, and_assoc, and_left_comm, and_comm]
  have hpairInter : ∀ y ∈ S, ∀ z ∈ S, y ≠ z →
      Disjoint (F y ∩ S) (F z ∩ S) := by
    intro y hy z hz hyz
    exact (hpair y hy z hz hyz).mono Finset.inter_subset_left
      Finset.inter_subset_left
  have hinterCard : (W ∩ S).card =
      ∑ y ∈ S, (G.neighborFinset y ∩ S).card := by
    rw [hinterEq, Finset.card_biUnion hpairInter]
    apply Finset.sum_congr rfl
    intro y _hy
    simp only [F]
    have hsub : S ⊆ B 0 := Finset.inter_subset_right
    rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hsub]
  have hdegreeSum : (∑ y ∈ S, (G.neighborFinset y ∩ S).card) =
      ∑ y : ↥(↑S : Set V), K.degree y := by
    rw [← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro y _hy
    exact (degree_induce_finset_eq_card_inter G S y).symm
  have hhand := K.sum_degrees_eq_twice_card_edges
  rw [← hdegreeSum, ← hinterCard] at hhand
  have hintersection : (S ∩ W).card = 2 * K.edgeFinset.card := by
    rw [Finset.inter_comm]
    exact hhand
  have hle := Finset.card_le_card (Finset.inter_subset_right : S ∩ W ⊆ W)
  rw [hintersection, hWcard] at hle
  rw [Finset.card_sdiff]
  rw [hWcard]
  rw [hintersection]
  omega

/-- The two local-triangle branches have exactly 24 and 22 ordinary B₀
targets, respectively, for the three special disjoint support rows. -/
theorem squareOrderNine_threeHigh_secondProfile_special_binZero_target_dichotomy
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let W := S.biUnion fun y => G.neighborFinset y ∩ B 0
    ((G.induce (G.neighborSet x)).edgeFinset.card = 3 ∧ (W \ S).card = 24) ∨
      ((G.induce (G.neighborSet x)).edgeFinset.card = 4 ∧ (W \ S).card = 22) := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let W := S.biUnion fun y => G.neighborFinset y ∩ B 0
  let D := secondOrderDefectGraph G
  let R := S \ D.neighborFinset x
  let K := G.induce (↑S : Set V)
  change ((G.induce (G.neighborSet x)).edgeFinset.card = 3 ∧
      (W \ S).card = 24) ∨
    ((G.induce (G.neighborSet x)).edgeFinset.card = 4 ∧
      (W \ S).card = 22)
  have hord :=
    squareOrderNine_threeHigh_secondProfile_special_binZero_ordinary_support
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  change (W \ S).card + 2 * K.edgeFinset.card = 24 at hord
  have hbranch :=
    squareOrderNine_threeHigh_secondProfile_binThree_nondefect_binZero_pair
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx
  change ((G.induce (G.neighborSet x)).edgeFinset.card = 3 ∧ R.card = 0) ∨
    ((G.induce (G.neighborSet x)).edgeFinset.card = 4 ∧ R.card = 2) at hbranch
  have hedgeR {y z : V} (hy : y ∈ S) (hz : z ∈ S)
      (hyz : G.Adj y z) : y ∈ R := by
    refine Finset.mem_sdiff.mpr ⟨hy, ?_⟩
    intro hyD
    have hDxy : D.Adj x y := (D.mem_neighborFinset x y).mp hyD
    change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj x y at hDxy
    rcases hDxy with hanti | htf
    · have hxy : G.Adj x y :=
        (G.mem_neighborFinset x y).mp (Finset.mem_inter.mp hy).1
      exact ((mem_antipodalNeighbors G x y).mp
        ((antipodalGraph_adj G x y).mp hanti)).2.1 hxy
    · have hcommonZero := ((mem_triangleFreeNeighbors G x y).mp
        ((triangleFreeEdgeGraph_adj G x y).mp htf)).2
      have hzCommon : z ∈ G.neighborFinset x ∩ G.neighborFinset y :=
        Finset.mem_inter.mpr ⟨
          (Finset.mem_inter.mp hz).1,
          (G.mem_neighborFinset y z).mpr hyz⟩
      rw [Finset.card_eq_zero] at hcommonZero
      rw [hcommonZero] at hzCommon
      exact Finset.notMem_empty z hzCommon
  have hKle : K.edgeFinset.card ≤ 1 := by
    have hScard : S.card = 3 := by
      have hcensus :=
        squareOrderNine_threeHigh_secondProfile_binThree_original_neighborhood_census
          G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
      exact hcensus.2.2
    have hdegLe : ∀ y : ↥(↑S : Set V), K.degree y ≤ 1 := by
      intro y
      rw [degree_induce_finset_eq_card_inter]
      have hyS : y.1 ∈ S := y.2
      have hyx : y.1 ≠ x := by
        intro h
        have hxS : x ∈ S := h ▸ hyS
        exact G.loopless.irrefl x
          ((G.mem_neighborFinset x x).mp (Finset.mem_inter.mp hxS).1)
      have hcommon := (not_containsC4_iff_forall_common_le_one G).mp
        hfree y.1 x hyx
      apply (Finset.card_le_card ?_).trans hcommon
      intro z hz
      have hzParts := Finset.mem_inter.mp hz
      exact Finset.mem_inter.mpr ⟨hzParts.1,
        (Finset.mem_inter.mp hzParts.2).1⟩
    have hsumLe : (∑ y : ↥(↑S : Set V), K.degree y) ≤ 3 := by
      calc
        _ ≤ ∑ _y : ↥(↑S : Set V), 1 := Finset.sum_le_sum fun y _ => hdegLe y
        _ = 3 := by simp [Fintype.card_coe, hScard]
    rw [K.sum_degrees_eq_twice_card_edges] at hsumLe
    omega
  rcases hbranch with hfirst | hsecond
  · left
    refine ⟨hfirst.1, ?_⟩
    have hKzero : K.edgeFinset.card = 0 := by
      have hdegZero : ∀ y : ↥(↑S : Set V), K.degree y = 0 := by
        intro y
        rw [← K.card_neighborFinset_eq_degree, Finset.card_eq_zero]
        ext z
        simp only [Finset.notMem_empty, iff_false]
        intro hyz
        have hyzK : K.Adj y z := (K.mem_neighborFinset y z).mp hyz
        have hyzG : G.Adj y.1 z.1 := hyzK
        have hyR := hedgeR y.2 z.2 hyzG
        have hRempty : R = ∅ := Finset.card_eq_zero.mp hfirst.2
        rw [hRempty] at hyR
        exact Finset.notMem_empty y.1 hyR
      have hsumzero : (∑ y : ↥(↑S : Set V), K.degree y) = 0 := by
        simp [hdegZero]
      rw [K.sum_degrees_eq_twice_card_edges] at hsumzero
      omega
    rw [hKzero] at hord
    simpa using hord
  · right
    refine ⟨hsecond.1, ?_⟩
    have hRtwo : R.card = 2 := hsecond.2
    obtain ⟨y, hyR⟩ := Finset.card_pos.mp (by omega : 0 < R.card)
    have hRerase : (R.erase y).card = 1 := by
      rw [Finset.card_erase_of_mem hyR, hRtwo]
    obtain ⟨z, hzErase⟩ := Finset.card_pos.mp (by omega : 0 < (R.erase y).card)
    have hzR : z ∈ R := (Finset.mem_erase.mp hzErase).2
    have hyzNe : y ≠ z := by
      intro h
      subst z
      exact (Finset.mem_erase.mp hzErase).1 rfl
    have hyz :=
      squareOrderNine_threeHigh_secondProfile_binThree_nondefect_binZero_pair_adjacent
        G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hyR hzR hyzNe
          hsecond.1
    have hyS := (Finset.mem_sdiff.mp hyR).1
    have hzS := (Finset.mem_sdiff.mp hzR).1
    have hpos : 0 < K.edgeFinset.card := by
      let y' : ↥(↑S : Set V) := ⟨y, hyS⟩
      let z' : ↥(↑S : Set V) := ⟨z, hzS⟩
      have hadj : K.Adj y' z' := hyz
      have hdegpos : 0 < K.degree y' := by
        rw [← K.card_neighborFinset_eq_degree, Finset.card_pos]
        exact ⟨z', (K.mem_neighborFinset y' z').mpr hadj⟩
      have hterm : K.degree y' ≤ ∑ u : ↥(↑S : Set V), K.degree u :=
        Finset.single_le_sum (f := fun u => K.degree u)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ y')
      have hhand := K.sum_degrees_eq_twice_card_edges
      rw [hhand] at hterm
      omega
    have hKone : K.edgeFinset.card = 1 := by omega
    rw [hKone] at hord
    omega

/-- After deleting the three special bin-zero rows, the remaining B₀ block
is a 47-vertex graph.  Its vertices have induced degree five precisely on
the special support target set and degree six elsewhere; the two branches
therefore have `(24,23,129)` and `(22,25,130)` degree/edge censuses. -/
theorem squareOrderNine_threeHigh_secondProfile_ordinary_binZero_residual_census
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let U := (S.biUnion fun y => G.neighborFinset y ∩ B 0) \ S
    let K := G.induce (↑T : Set V)
    T.card = 47 ∧ U ⊆ T ∧
      (∀ y : ↥(↑T : Set V), K.degree y = if y.1 ∈ U then 5 else 6) ∧
      ((U.card = 24 ∧ (T \ U).card = 23 ∧ K.edgeFinset.card = 129) ∨
        (U.card = 22 ∧ (T \ U).card = 25 ∧ K.edgeFinset.card = 130)) := by
  classical
  dsimp only
  let H := squareOrderHighVertices G 9
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let W := S.biUnion fun y => G.neighborFinset y ∩ B 0
  let U := W \ S
  let K := G.induce (↑T : Set V)
  change T.card = 47 ∧ U ⊆ T ∧
    (∀ y : ↥(↑T : Set V), K.degree y = if y.1 ∈ U then 5 else 6) ∧
    ((U.card = 24 ∧ (T \ U).card = 23 ∧ K.edgeFinset.card = 129) ∨
      (U.card = 22 ∧ (T \ U).card = 25 ∧ K.edgeFinset.card = 130))
  have hB0card : (B 0).card = 50 :=
    squareOrderNine_threeHigh_secondProfile_binZero_card G hcard hp hhigh hc3
  have hScard : S.card = 3 := by
    have hcensus :=
      squareOrderNine_threeHigh_secondProfile_binThree_original_neighborhood_census
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
    exact hcensus.2.2
  have hSsub : S ⊆ B 0 := Finset.inter_subset_right
  have hTcard : T.card = 47 := by
    rw [Finset.card_sdiff_of_subset hSsub, hB0card, hScard]
  have hWsub : W ⊆ B 0 := by
    intro y hyW
    simp only [W, Finset.mem_biUnion] at hyW
    obtain ⟨z, _hzS, hyF⟩ := hyW
    exact (Finset.mem_inter.mp hyF).2
  have hUsub : U ⊆ T := by
    intro y hyU
    have hyParts := Finset.mem_sdiff.mp hyU
    exact Finset.mem_sdiff.mpr ⟨hWsub hyParts.1, hyParts.2⟩
  have hb2 : B 2 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 2) (by omega), hc2]
  have hb3card : (B 3).card = 1 := by
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 3) (by omega), hc3]
  have hb4 : B 4 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 4) (by omega), hc4]
  have hB0degree : ∀ y ∈ T, (G.neighborFinset y ∩ B 0).card = 6 := by
    intro y hyT
    have hyParts := Finset.mem_sdiff.mp hyT
    have hyB0 := hyParts.1
    have hyNotS := hyParts.2
    have hyNotAdj : ¬ G.Adj y x := by
      intro hyx
      apply hyNotS
      exact Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset x y).mpr hyx.symm, hyB0⟩
    have hyB1 :=
      squareOrderNine_threeHigh_secondProfile_binZero_original_binOne_neighbors
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hyB0
    simp [hyNotAdj] at hyB1
    change (G.neighborFinset y ∩ B 1).card = 3 at hyB1
    have hyLow := (Finset.mem_filter.mp hyB0).1
    have hyNotHigh : y ∉ H := (Finset.mem_sdiff.mp hyLow).2
    have hyDegree : G.degree y = 9 := by
      rcases hp.degree_dichotomy y with hlo | hhi
      · exact hlo
      · exact (hyNotHigh (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
    have hky : squareOrderHighIncidenceCount G 9 y = 0 :=
      (Finset.mem_filter.mp hyB0).2
    have hyB3zero : (G.neighborFinset y ∩ B 3).card = 0 := by
      rw [Finset.card_eq_zero]
      ext z
      simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
      intro hyz hzB3
      have hzx : z = x := Finset.card_le_one.mp (by omega) z hzB3 x hx
      subst z
      exact hyNotAdj ((G.mem_neighborFinset y x).mp hyz)
    have hpnt := squareOrderNine_originalNeighbor_lowBin_partition G hp hyNotHigh
    change (∑ j ∈ Finset.range 5, (G.neighborFinset y ∩ B j).card) +
      squareOrderHighIncidenceCount G 9 y = G.degree y at hpnt
    norm_num [Finset.sum_range_succ, hb2, hb4, hky, hyDegree,
      hyB1, hyB3zero] at hpnt
    omega
  have hspecialLe : ∀ y ∈ T, (G.neighborFinset y ∩ S).card ≤ 1 := by
    intro y hyT
    have hyParts := Finset.mem_sdiff.mp hyT
    have hyNotS := hyParts.2
    have hyx : y ≠ x := by
      intro h
      subst y
      have hxB0 := hyParts.1
      have hkx := (Finset.mem_filter.mp hx).2
      have hk0 := (Finset.mem_filter.mp hxB0).2
      omega
    have hcommon := (not_containsC4_iff_forall_common_le_one G).mp hfree y x hyx
    apply (Finset.card_le_card ?_).trans hcommon
    intro z hz
    have hzParts := Finset.mem_inter.mp hz
    exact Finset.mem_inter.mpr ⟨hzParts.1,
      (Finset.mem_inter.mp hzParts.2).1⟩
  have hmemU : ∀ y ∈ T, y ∈ U ↔ 0 < (G.neighborFinset y ∩ S).card := by
    intro y hyT
    have hyNotS := (Finset.mem_sdiff.mp hyT).2
    constructor
    · intro hyU
      have hyW := (Finset.mem_sdiff.mp hyU).1
      simp only [W, Finset.mem_biUnion] at hyW
      obtain ⟨z, hzS, hyF⟩ := hyW
      have hzy : G.Adj z y :=
        (G.mem_neighborFinset z y).mp (Finset.mem_inter.mp hyF).1
      rw [Finset.card_pos]
      exact ⟨z, Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset y z).mpr hzy.symm, hzS⟩⟩
    · intro hpos
      obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
      have hzParts := Finset.mem_inter.mp hz
      refine Finset.mem_sdiff.mpr ⟨?_, hyNotS⟩
      simp only [W, Finset.mem_biUnion]
      exact ⟨z, hzParts.2, Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset z y).mpr
          ((G.mem_neighborFinset y z).mp hzParts.1).symm,
          (Finset.mem_sdiff.mp hyT).1⟩⟩
  have hdegree : ∀ y : ↥(↑T : Set V),
      K.degree y = if y.1 ∈ U then 5 else 6 := by
    intro y
    rw [degree_induce_finset_eq_card_inter]
    have hB0 := hB0degree y.1 y.2
    have hsub : S ⊆ B 0 := hSsub
    have heq : G.neighborFinset y.1 ∩ T =
        (G.neighborFinset y.1 ∩ B 0) \ S := by
      ext z
      constructor
      · intro hz
        have hzParts := Finset.mem_inter.mp hz
        have hzT := Finset.mem_sdiff.mp hzParts.2
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hzParts.1, hzT.1⟩, hzT.2⟩
      · intro hz
        have hzParts := Finset.mem_sdiff.mp hz
        have hzNB := Finset.mem_inter.mp hzParts.1
        exact Finset.mem_inter.mpr
          ⟨hzNB.1, Finset.mem_sdiff.mpr ⟨hzNB.2, hzParts.2⟩⟩
    rw [heq, Finset.card_sdiff]
    have hinter : S ∩ (G.neighborFinset y.1 ∩ B 0) =
        G.neighborFinset y.1 ∩ S := by
      ext z
      constructor
      · intro hz
        have hzParts := Finset.mem_inter.mp hz
        exact Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hzParts.2).1, hzParts.1⟩
      · intro hz
        have hzParts := Finset.mem_inter.mp hz
        exact Finset.mem_inter.mpr ⟨hzParts.2,
          Finset.mem_inter.mpr ⟨hzParts.1, hSsub hzParts.2⟩⟩
    rw [hinter, hB0]
    have hle := hspecialLe y.1 y.2
    by_cases hyU : y.1 ∈ U
    · have hpos := (hmemU y.1 y.2).mp hyU
      simp [hyU]
      omega
    · have hzero : (G.neighborFinset y.1 ∩ S).card = 0 := by
        by_contra hne
        have hpos : 0 < (G.neighborFinset y.1 ∩ S).card := Nat.pos_of_ne_zero hne
        exact hyU ((hmemU y.1 y.2).mpr hpos)
      simp [hyU, hzero]
  have htarget :=
    squareOrderNine_threeHigh_secondProfile_special_binZero_target_dichotomy
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx
  change ((G.induce (G.neighborSet x)).edgeFinset.card = 3 ∧ U.card = 24) ∨
    ((G.induce (G.neighborSet x)).edgeFinset.card = 4 ∧ U.card = 22) at htarget
  have hcompCard (u : ℕ) (hu : U.card = u) : (T \ U).card = 47 - u := by
    rw [Finset.card_sdiff_of_subset hUsub, hTcard, hu]
  have hedgeCard (u e : ℕ) (hu : U.card = u)
      (heq : 5 * u + 6 * (47 - u) = 2 * e) : K.edgeFinset.card = e := by
    have hfilter : T.filter (fun y => y ∈ U) = U := by
      ext y
      simp only [Finset.mem_filter]
      constructor
      · exact fun hy => hy.2
      · intro hyU
        exact ⟨hUsub hyU, hyU⟩
    have hfilterNot : T.filter (fun y => y ∉ U) = T \ U := by
      ext y
      simp
    have hsum : (∑ y : ↥(↑T : Set V), K.degree y) =
        5 * U.card + 6 * (T \ U).card := by
      calc
        _ = ∑ y : ↥(↑T : Set V),
            (if y.1 ∈ U then 5 else 6) := by
              apply Finset.sum_congr rfl
              intro y _
              exact hdegree y
        _ = ∑ y ∈ T, (if y ∈ U then 5 else 6) :=
          (Finset.sum_subtype T (fun _ => Iff.rfl)
            (fun y : V => if y ∈ U then 5 else 6)).symm
        _ = 5 * U.card + 6 * (T \ U).card := by
          simp [Finset.sum_ite, hfilter, hfilterNot, Nat.mul_comm]
    have hhand := K.sum_degrees_eq_twice_card_edges
    rw [hsum, hu, hcompCard u hu] at hhand
    omega
  refine ⟨hTcard, hUsub, hdegree, ?_⟩
  rcases htarget with hfirst | hsecond
  · left
    have hcomp := hcompCard 24 hfirst.2
    have hedge := hedgeCard 24 129 hfirst.2 (by norm_num)
    exact ⟨hfirst.2, by simpa using hcomp, hedge⟩
  · right
    have hcomp := hcompCard 22 hsecond.2
    have hedge := hedgeCard 22 130 hsecond.2 (by norm_num)
    exact ⟨hsecond.2, by simpa using hcomp, hedge⟩

/-- Pointwise original-neighbor refinement on B₁.  The three B₁ neighbors
of the rare B₃ vertex have `(B₀,B₁,B₃)=(7,0,1)`; the other twenty-four have
`(5,3,0)`. -/
theorem squareOrderNine_threeHigh_secondProfile_binOne_original_degrees
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
    {x y : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ squareOrderNineLowIncidenceBin G 1) :
    let B := squareOrderNineLowIncidenceBin G
    (G.neighborFinset y ∩ B 1).card = (if G.Adj y x then 0 else 3) ∧
      (G.neighborFinset y ∩ B 0).card = (if G.Adj y x then 7 else 5) := by
  classical
  dsimp only
  let H := squareOrderHighVertices G 9
  let B := squareOrderNineLowIncidenceBin G
  let k := squareOrderHighIncidenceCount G 9
  have hyLow := (Finset.mem_filter.mp hy).1
  have hyNotHigh : y ∉ H := (Finset.mem_sdiff.mp hyLow).2
  have hsum : (∑ z ∈ G.neighborFinset y, k z) = 3 :=
    squareOrderNine_threeHigh_sum_highIncidence_over_lowNeighborhood
      G hfree hmin hcard hhigh hyNotHigh
  have hb2 : B 2 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 2) (by omega), hc2]
  have hb3card : (B 3).card = 1 := by
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 3) (by omega), hc3]
  have hb4 : B 4 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 4) (by omega), hc4]
  have hpoint : ∀ z ∈ G.neighborFinset y,
      k z = (if z ∈ B 1 then 1 else 0) +
        3 * (if z ∈ B 3 then 1 else 0) := by
    intro z hz
    by_cases hzH : z ∈ H
    · have hzero : k z = 0 := by
        unfold k squareOrderHighIncidenceCount
        rw [Finset.card_eq_zero]
        ext a
        simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
        intro hza haH
        exact hp.high_independent hzH haH ((G.mem_neighborFinset z a).mp hza)
      have hzNotB1 : z ∉ B 1 := by
        intro hzB
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hzB).1).2 hzH
      have hzNotB3 : z ∉ B 3 := by
        intro hzB
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hzB).1).2 hzH
      simp [hzero, hzNotB1, hzNotB3]
    · have hzLow : z ∈ Finset.univ \ H :=
          Finset.mem_sdiff.mpr ⟨by simp, hzH⟩
      have hkle : k z ≤ 4 := by
        rcases hp.degree_dichotomy z with hlo | hhi
        · have hb := hp.low_incidence_bound hlo
          change 2 * k z ≤ 9 at hb
          omega
        · exact (hzH (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
      have hkNot2 : k z ≠ 2 := by
        intro hk
        have : z ∈ B 2 := Finset.mem_filter.mpr ⟨hzLow, hk⟩
        simpa [hb2] using this
      have hkNot4 : k z ≠ 4 := by
        intro hk
        have : z ∈ B 4 := Finset.mem_filter.mpr ⟨hzLow, hk⟩
        simpa [hb4] using this
      have hk013 : k z = 0 ∨ k z = 1 ∨ k z = 3 := by omega
      rcases hk013 with hk0 | hk1 | hk3
      · have hzNotB1 : z ∉ B 1 := by
          intro hzB
          have hk := (Finset.mem_filter.mp hzB).2
          change k z = 1 at hk
          omega
        have hzNotB3 : z ∉ B 3 := by
          intro hzB
          have hk := (Finset.mem_filter.mp hzB).2
          change k z = 3 at hk
          omega
        simp [hk0, hzNotB1, hzNotB3]
      · have hzB1 : z ∈ B 1 := Finset.mem_filter.mpr ⟨hzLow, hk1⟩
        have hzNotB3 : z ∉ B 3 := by
          intro hzB
          have hk := (Finset.mem_filter.mp hzB).2
          change k z = 3 at hk
          omega
        simp [hk1, hzB1, hzNotB3]
      · have hzB3 : z ∈ B 3 := Finset.mem_filter.mpr ⟨hzLow, hk3⟩
        have hzNotB1 : z ∉ B 1 := by
          intro hzB
          have hk := (Finset.mem_filter.mp hzB).2
          change k z = 1 at hk
          omega
        simp [hk3, hzB3, hzNotB1]
  have hweighted : (G.neighborFinset y ∩ B 1).card +
      3 * (G.neighborFinset y ∩ B 3).card = 3 := by
    have hdecomp : (∑ z ∈ G.neighborFinset y, k z) =
        (∑ z ∈ G.neighborFinset y, if z ∈ B 1 then 1 else 0) +
          3 * (∑ z ∈ G.neighborFinset y, if z ∈ B 3 then 1 else 0) := by
      calc
        _ = ∑ z ∈ G.neighborFinset y,
            ((if z ∈ B 1 then 1 else 0) +
              3 * (if z ∈ B 3 then 1 else 0)) := by
                apply Finset.sum_congr rfl
                intro z hz
                exact hpoint z hz
        _ = (∑ z ∈ G.neighborFinset y, if z ∈ B 1 then 1 else 0) +
            ∑ z ∈ G.neighborFinset y,
              3 * (if z ∈ B 3 then 1 else 0) := Finset.sum_add_distrib
        _ = _ := by rw [Finset.mul_sum]
    rw [hsum] at hdecomp
    simpa using hdecomp.symm
  have hB3 : (G.neighborFinset y ∩ B 3).card =
      if G.Adj y x then 1 else 0 := by
    have hsingle : B 3 = {x} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hx, fun z hz => Finset.card_le_one.mp (by omega) z hz x hx⟩
    rw [hsingle]
    by_cases hyx : G.Adj y x <;> simp [hyx, G.mem_neighborFinset]
  have hB1 : (G.neighborFinset y ∩ B 1).card =
      if G.Adj y x then 0 else 3 := by
    rw [hB3] at hweighted
    split_ifs at hweighted ⊢ <;> omega
  have hyDegree : G.degree y = 9 := by
    rcases hp.degree_dichotomy y with hlo | hhi
    · exact hlo
    · exact (hyNotHigh (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
  have hky : k y = 1 := (Finset.mem_filter.mp hy).2
  have hpnt := squareOrderNine_originalNeighbor_lowBin_partition G hp hyNotHigh
  change (∑ j ∈ Finset.range 5, (G.neighborFinset y ∩ B j).card) +
    k y = G.degree y at hpnt
  norm_num [Finset.sum_range_succ, hb2, hb4, hky, hyDegree] at hpnt
  refine ⟨hB1, ?_⟩
  by_cases hyx : G.Adj y x
  · simp [hyx] at hB1 hB3 ⊢
    rw [hB1, hB3] at hpnt
    simp at hpnt
    omega
  · simp [hyx] at hB1 hB3 ⊢
    rw [hB1, hB3] at hpnt
    simp at hpnt
    omega

/-- The three marked B₁ rows have pairwise-disjoint seven-point supports in
B₀, for a total of 21 positions. -/
theorem squareOrderNine_threeHigh_secondProfile_marked_binOne_row_packing
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    let B := squareOrderNineLowIncidenceBin G
    let M := G.neighborFinset x ∩ B 1
    M.card = 3 ∧
      (∀ y ∈ M, (G.neighborFinset y ∩ B 0).card = 7) ∧
      (∀ y ∈ M, ∀ z ∈ M, y ≠ z →
        Disjoint (G.neighborFinset y ∩ B 0)
          (G.neighborFinset z ∩ B 0)) ∧
      (∑ y ∈ M, (G.neighborFinset y ∩ B 0).card) = 21 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let M := G.neighborFinset x ∩ B 1
  have hMcard : M.card = 3 :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_binOne_neighbors
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  have hrow : ∀ y ∈ M, (G.neighborFinset y ∩ B 0).card = 7 := by
    intro y hyM
    have hyParts := Finset.mem_inter.mp hyM
    have hyx : G.Adj y x :=
      (G.adj_comm x y).mp ((G.mem_neighborFinset x y).mp hyParts.1)
    have hdeg := squareOrderNine_threeHigh_secondProfile_binOne_original_degrees
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hyParts.2
    dsimp only at hdeg
    simpa [hyx] using hdeg.2
  have hdisj : ∀ y ∈ M, ∀ z ∈ M, y ≠ z →
      Disjoint (G.neighborFinset y ∩ B 0)
        (G.neighborFinset z ∩ B 0) := by
    intro y hyM z hzM hyz
    rw [Finset.disjoint_left]
    intro w hwy hwz
    have hyParts := Finset.mem_inter.mp hyM
    have hzParts := Finset.mem_inter.mp hzM
    have hwyParts := Finset.mem_inter.mp hwy
    have hwzParts := Finset.mem_inter.mp hwz
    have hxCommon : x ∈ G.neighborFinset y ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset y x).mpr
          ((G.adj_comm x y).mp ((G.mem_neighborFinset x y).mp hyParts.1)),
        (G.mem_neighborFinset z x).mpr
          ((G.adj_comm x z).mp ((G.mem_neighborFinset x z).mp hzParts.1))⟩
    have hwCommon : w ∈ G.neighborFinset y ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr ⟨hwyParts.1, hwzParts.1⟩
    have hxw : x ≠ w := by
      intro h
      subst w
      have hkx := (Finset.mem_filter.mp hx).2
      have hkw := (Finset.mem_filter.mp hwyParts.2).2
      omega
    have hle := (not_containsC4_iff_forall_common_le_one G).mp hfree y z hyz
    exact hxw (Finset.card_le_one.mp hle x hxCommon w hwCommon)
  refine ⟨hMcard, hrow, hdisj, ?_⟩
  calc
    (∑ y ∈ M, (G.neighborFinset y ∩ B 0).card) = ∑ _y ∈ M, 7 := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hrow y hy
    _ = 21 := by simp [hMcard]

/-- The three special B₀ rows and three marked B₁ rows have six mutually
disjoint supports in B₀, covering 45 vertices in total.  After removing the
special triple itself, only two ordinary B₀ vertices remain uncovered in the
three-triangle branch and four in the four-triangle branch. -/
theorem squareOrderNine_threeHigh_secondProfile_six_row_support_saturation
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let M := G.neighborFinset x ∩ B 1
    let WS := S.biUnion fun y => G.neighborFinset y ∩ B 0
    let WM := M.biUnion fun y => G.neighborFinset y ∩ B 0
    let T := B 0 \ S
    let O := (WS ∪ WM) \ S
    (WS ∪ WM).card = 45 ∧ O ⊆ T ∧
      (((G.induce (G.neighborSet x)).edgeFinset.card = 3 ∧
          O.card = 45 ∧ (T \ O).card = 2) ∨
        ((G.induce (G.neighborSet x)).edgeFinset.card = 4 ∧
          O.card = 43 ∧ (T \ O).card = 4)) := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let M := G.neighborFinset x ∩ B 1
  let FS : V → Finset V := fun y => G.neighborFinset y ∩ B 0
  let WS := S.biUnion FS
  let WM := M.biUnion FS
  let T := B 0 \ S
  let O := (WS ∪ WM) \ S
  change (WS ∪ WM).card = 45 ∧ O ⊆ T ∧
    (((G.induce (G.neighborSet x)).edgeFinset.card = 3 ∧
        O.card = 45 ∧ (T \ O).card = 2) ∨
      ((G.induce (G.neighborSet x)).edgeFinset.card = 4 ∧
        O.card = 43 ∧ (T \ O).card = 4))
  have hSpack :=
    squareOrderNine_threeHigh_secondProfile_special_binZero_row_packing
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hSpack
  have hMpack :=
    squareOrderNine_threeHigh_secondProfile_marked_binOne_row_packing
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hMpack
  have hSdisj : ∀ y ∈ S, ∀ z ∈ S, y ≠ z → Disjoint (FS y) (FS z) :=
    hSpack.2.1
  have hMdisj : ∀ y ∈ M, ∀ z ∈ M, y ≠ z → Disjoint (FS y) (FS z) :=
    hMpack.2.2.1
  have hWScard : WS.card = 24 := by
    rw [Finset.card_biUnion hSdisj]
    exact hSpack.2.2
  have hWMcard : WM.card = 21 := by
    rw [Finset.card_biUnion hMdisj]
    exact hMpack.2.2.2
  have hcross : Disjoint WS WM := by
    rw [Finset.disjoint_left]
    intro w hwS hwM
    simp only [WS, Finset.mem_biUnion] at hwS
    simp only [WM, Finset.mem_biUnion] at hwM
    obtain ⟨y, hyS, hwy⟩ := hwS
    obtain ⟨z, hzM, hwz⟩ := hwM
    have hyParts := Finset.mem_inter.mp hyS
    have hzParts := Finset.mem_inter.mp hzM
    have hwyParts := Finset.mem_inter.mp hwy
    have hwzParts := Finset.mem_inter.mp hwz
    have hyz : y ≠ z := by
      intro h
      subst z
      have hky0 := (Finset.mem_filter.mp hyParts.2).2
      have hky1 := (Finset.mem_filter.mp hzParts.2).2
      omega
    have hxCommon : x ∈ G.neighborFinset y ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset y x).mpr
          ((G.adj_comm x y).mp ((G.mem_neighborFinset x y).mp hyParts.1)),
        (G.mem_neighborFinset z x).mpr
          ((G.adj_comm x z).mp ((G.mem_neighborFinset x z).mp hzParts.1))⟩
    have hwCommon : w ∈ G.neighborFinset y ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr ⟨hwyParts.1, hwzParts.1⟩
    have hxw : x ≠ w := by
      intro h
      subst w
      have hkx := (Finset.mem_filter.mp hx).2
      have hkw := (Finset.mem_filter.mp hwyParts.2).2
      omega
    have hle := (not_containsC4_iff_forall_common_le_one G).mp hfree y z hyz
    exact hxw (Finset.card_le_one.mp hle x hxCommon w hwCommon)
  have hUnionCard : (WS ∪ WM).card = 45 := by
    rw [Finset.card_union_of_disjoint hcross, hWScard, hWMcard]
  have hWSsub : WS ⊆ B 0 := by
    intro y hy
    simp only [WS, Finset.mem_biUnion] at hy
    obtain ⟨z, _hz, hyF⟩ := hy
    exact (Finset.mem_inter.mp hyF).2
  have hWMsub : WM ⊆ B 0 := by
    intro y hy
    simp only [WM, Finset.mem_biUnion] at hy
    obtain ⟨z, _hz, hyF⟩ := hy
    exact (Finset.mem_inter.mp hyF).2
  have hOsub : O ⊆ T := by
    intro y hy
    have hyParts := Finset.mem_sdiff.mp hy
    have hyUnion := Finset.mem_union.mp hyParts.1
    rcases hyUnion with hyWS | hyWM
    · exact Finset.mem_sdiff.mpr ⟨hWSsub hyWS, hyParts.2⟩
    · exact Finset.mem_sdiff.mpr ⟨hWMsub hyWM, hyParts.2⟩
  have hMnotS : Disjoint WM S := by
    rw [Finset.disjoint_left]
    intro y hyWM hyS
    simp only [WM, Finset.mem_biUnion] at hyWM
    obtain ⟨z, hzM, hyF⟩ := hyWM
    have hySParts := Finset.mem_inter.mp hyS
    have hzMParts := Finset.mem_inter.mp hzM
    have hyFParts := Finset.mem_inter.mp hyF
    have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hySParts.1
    have hyz : G.Adj y z :=
      (G.adj_comm z y).mp ((G.mem_neighborFinset z y).mp hyFParts.1)
    exact (squareOrderNine_threeHigh_binThree_binZero_neighbor_not_binOneAdjacent
      G hfree hhigh hx hySParts.2 hzMParts.2 hxy) hyz
  have htarget :=
    squareOrderNine_threeHigh_secondProfile_special_binZero_target_dichotomy
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx
  change ((G.induce (G.neighborSet x)).edgeFinset.card = 3 ∧
      (WS \ S).card = 24) ∨
    ((G.induce (G.neighborSet x)).edgeFinset.card = 4 ∧
      (WS \ S).card = 22) at htarget
  have hTcard : T.card = 47 := by
    have hB0card := squareOrderNine_threeHigh_secondProfile_binZero_card
      G hcard hp hhigh hc3
    have hScard :=
      (squareOrderNine_threeHigh_secondProfile_binThree_original_neighborhood_census
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx).2.2
    rw [Finset.card_sdiff_of_subset Finset.inter_subset_right, hB0card, hScard]
  have hOcard (n : ℕ) (hWSordinary : (WS \ S).card = n) :
      O.card = n + 21 := by
    have heq : O = (WS \ S) ∪ WM := by
      ext y
      simp only [O, Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hyUnion, hyNotS⟩
        rcases hyUnion with hyWS | hyWM
        · exact Or.inl ⟨hyWS, hyNotS⟩
        · exact Or.inr hyWM
      · rintro (⟨hyWS, hyNotS⟩ | hyWM)
        · exact ⟨Or.inl hyWS, hyNotS⟩
        · exact ⟨Or.inr hyWM,
            fun hyS => Finset.disjoint_left.mp hMnotS hyWM hyS⟩
    have hdisj : Disjoint (WS \ S) WM :=
      hcross.mono Finset.sdiff_subset Finset.Subset.rfl
    rw [heq, Finset.card_union_of_disjoint hdisj, hWSordinary, hWMcard]
  refine ⟨hUnionCard, hOsub, ?_⟩
  rcases htarget with hfirst | hsecond
  · left
    have hOc := hOcard 24 hfirst.2
    have hholes : (T \ O).card = 2 := by
      rw [Finset.card_sdiff_of_subset hOsub, hTcard, hOc]
    exact ⟨hfirst.1, by omega, hholes⟩
  · right
    have hOc := hOcard 22 hsecond.2
    have hholes : (T \ O).card = 4 := by
      rw [Finset.card_sdiff_of_subset hOsub, hTcard, hOc]
    exact ⟨hsecond.1, by omega, hholes⟩

/-- A bin-one vertex antipodal to a special bin-zero neighbor of the rare
bin-three vertex cannot be one of the three marked bin-one vertices.  It
therefore has the unmarked original profile `(B₀,B₁)=(5,3)`, and its
five-point bin-zero support is disjoint from the special vertex's bin-zero
row. -/
theorem squareOrderNine_threeHigh_secondProfile_special_antipodal_binOne_fiber
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
    {x y b : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0)
    (hb : b ∈ antipodalNeighbors G y ∩
      squareOrderNineLowIncidenceBin G 1) :
    let B := squareOrderNineLowIncidenceBin G
    let M := G.neighborFinset x ∩ B 1
    b ∉ M ∧
      (G.neighborFinset b ∩ B 0).card = 5 ∧
      (G.neighborFinset b ∩ B 1).card = 3 ∧
      Disjoint (G.neighborFinset y ∩ B 0)
        (G.neighborFinset b ∩ B 0) := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let M := G.neighborFinset x ∩ B 1
  have hyParts := Finset.mem_inter.mp hy
  have hbParts := Finset.mem_inter.mp hb
  have hanti := (mem_antipodalNeighbors G y b).mp hbParts.1
  have hzero : (G.neighborFinset y ∩ G.neighborFinset b).card = 0 :=
    hanti.2.2
  have hnotMarked : b ∉ M := by
    intro hbM
    have hbMParts := Finset.mem_inter.mp hbM
    have hxCommon : x ∈ G.neighborFinset y ∩ G.neighborFinset b :=
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset y x).mpr
          ((G.adj_comm x y).mp
            ((G.mem_neighborFinset x y).mp hyParts.1)),
        (G.mem_neighborFinset b x).mpr
          ((G.adj_comm x b).mp
            ((G.mem_neighborFinset x b).mp hbMParts.1))⟩
    have hempty := Finset.card_eq_zero.mp hzero
    simpa [hempty] using hxCommon
  have hbx : ¬ G.Adj b x := by
    intro hbx
    exact hnotMarked (Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset x b).mpr ((G.adj_comm b x).mp hbx), hbParts.2⟩)
  have hdeg := squareOrderNine_threeHigh_secondProfile_binOne_original_degrees
    G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hbParts.2
  dsimp only at hdeg
  have hB0 : (G.neighborFinset b ∩ B 0).card = 5 := by
    simpa [hbx] using hdeg.2
  have hB1 : (G.neighborFinset b ∩ B 1).card = 3 := by
    simpa [hbx] using hdeg.1
  have hdisj : Disjoint (G.neighborFinset y ∩ B 0)
      (G.neighborFinset b ∩ B 0) := by
    rw [Finset.disjoint_left]
    intro w hwy hwb
    have hwCommon : w ∈ G.neighborFinset y ∩ G.neighborFinset b :=
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hwy).1,
        (Finset.mem_inter.mp hwb).1⟩
    have hempty := Finset.card_eq_zero.mp hzero
    simpa [hempty] using hwCommon
  exact ⟨hnotMarked, hB0, hB1, hdisj⟩

/-- The unmarked bin-one rows meet an ordinary special-row support as a
partial transversal.  There are 24 such rows, each meets the support at
most once, and their total number of hits is exactly three times the support
size.  In particular, an eight-point ordinary support is met once by every
unmarked row, while a seven-point support has exactly three missing rows. -/
theorem squareOrderNine_threeHigh_secondProfile_unmarked_special_support_ledger
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
    {x y : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let F := (G.neighborFinset y ∩ B 0) \ S
    U1.card = 24 ∧
      (∀ b ∈ U1, (G.neighborFinset b ∩ F).card ≤ 1) ∧
      (∑ b ∈ U1, (G.neighborFinset b ∩ F).card) = 3 * F.card := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let F := (G.neighborFinset y ∩ B 0) \ S
  have hyParts := Finset.mem_inter.mp hy
  have hmarked :=
    squareOrderNine_threeHigh_secondProfile_marked_core_cardinalities
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hmarked
  have hMcard :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_binOne_neighbors
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  have hMsub : M ⊆ B 1 := Finset.inter_subset_right
  have hU1card : U1.card = 24 := by
    rw [Finset.card_sdiff_of_subset hMsub, hmarked.1, hMcard]
  have hrowLe : ∀ b ∈ U1, (G.neighborFinset b ∩ F).card ≤ 1 := by
    intro b hb
    rw [Finset.card_le_one]
    intro w hw z hz
    have hwParts := Finset.mem_inter.mp hw
    have hzParts := Finset.mem_inter.mp hz
    have hwF := Finset.mem_sdiff.mp hwParts.2
    have hzF := Finset.mem_sdiff.mp hzParts.2
    have hwy := (G.adj_comm y w).mp
      ((G.mem_neighborFinset y w).mp (Finset.mem_inter.mp hwF.1).1)
    have hzy := (G.adj_comm y z).mp
      ((G.mem_neighborFinset y z).mp (Finset.mem_inter.mp hzF.1).1)
    have hwb := (G.mem_neighborFinset b w).mp hwParts.1
    have hzb := (G.mem_neighborFinset b z).mp hzParts.1
    by_contra hwz
    have hyb : y ≠ b := by
      intro h
      subst b
      have hyB0 := (Finset.mem_filter.mp hyParts.2).2
      have hyB1 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hb).1).2
      omega
    have hwCommon : w ∈ G.neighborFinset y ∩ G.neighborFinset b :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y w).mpr hwy.symm,
        (G.mem_neighborFinset b w).mpr hwb⟩
    have hzCommon : z ∈ G.neighborFinset y ∩ G.neighborFinset b :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y z).mpr hzy.symm,
        (G.mem_neighborFinset b z).mpr hzb⟩
    have hle := (not_containsC4_iff_forall_common_le_one G).mp hfree y b hyb
    exact hwz (Finset.card_le_one.mp hle w hwCommon z hzCommon)
  have htarget : ∀ w ∈ F, (G.neighborFinset w ∩ U1).card = 3 := by
    intro w hwF
    have hwParts := Finset.mem_sdiff.mp hwF
    have hwBase := Finset.mem_inter.mp hwParts.1
    have hwNotAdjX : ¬ G.Adj w x := by
      intro hwx
      exact hwParts.2 (Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset x w).mpr hwx.symm, hwBase.2⟩)
    have hservice :=
      squareOrderNine_threeHigh_secondProfile_binZero_original_binOne_neighbors
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hwBase.2
    have hservice3 : (G.neighborFinset w ∩ B 1).card = 3 := by
      simpa [hwNotAdjX] using hservice
    have heq : G.neighborFinset w ∩ U1 = G.neighborFinset w ∩ B 1 := by
      apply Finset.Subset.antisymm
      · intro z hz
        have hzParts := Finset.mem_inter.mp hz
        exact Finset.mem_inter.mpr ⟨hzParts.1,
          (Finset.mem_sdiff.mp hzParts.2).1⟩
      · intro z hz
        have hzParts := Finset.mem_inter.mp hz
        refine Finset.mem_inter.mpr ⟨hzParts.1,
          Finset.mem_sdiff.mpr ⟨hzParts.2, ?_⟩⟩
        intro hzM
        have hzMParts := Finset.mem_inter.mp hzM
        have hxCommon : x ∈ G.neighborFinset y ∩ G.neighborFinset z :=
          Finset.mem_inter.mpr ⟨
            (G.mem_neighborFinset y x).mpr
              ((G.adj_comm x y).mp
                ((G.mem_neighborFinset x y).mp hyParts.1)),
            (G.mem_neighborFinset z x).mpr
              ((G.adj_comm x z).mp
                ((G.mem_neighborFinset x z).mp hzMParts.1))⟩
        have hwCommon : w ∈ G.neighborFinset y ∩ G.neighborFinset z :=
          Finset.mem_inter.mpr ⟨
            (G.mem_neighborFinset y w).mpr
              ((G.mem_neighborFinset y w).mp hwBase.1),
            (G.mem_neighborFinset z w).mpr
              ((G.adj_comm w z).mp
                ((G.mem_neighborFinset w z).mp hzParts.1))⟩
        have hyz : y ≠ z := by
          intro h
          subst z
          have hyB0 := (Finset.mem_filter.mp hyParts.2).2
          have hyB1 := (Finset.mem_filter.mp hzMParts.2).2
          omega
        have hxw : x ≠ w := by
          intro h
          subst w
          have hkx := (Finset.mem_filter.mp hx).2
          have hkw := (Finset.mem_filter.mp hwBase.2).2
          omega
        have hle := (not_containsC4_iff_forall_common_le_one G).mp hfree y z hyz
        exact hxw (Finset.card_le_one.mp hle x hxCommon w hwCommon)
    rw [heq, hservice3]
  have hswap := sum_card_neighborFinset_inter_comm G U1 F
  have hsumTarget : (∑ w ∈ F, (G.neighborFinset w ∩ U1).card) =
      3 * F.card := by
    calc
      _ = ∑ _w ∈ F, 3 := by
        apply Finset.sum_congr rfl
        intro w hw
        exact htarget w hw
      _ = 3 * F.card := by simp [Nat.mul_comm]
  exact ⟨hU1card, hrowLe, hswap.trans hsumTarget⟩

/-- Equality cases of the unmarked-row ledger.  An eight-point ordinary
special support is a transversal of all 24 unmarked rows.  A seven-point
support is missed by exactly three of those rows. -/
theorem squareOrderNine_threeHigh_secondProfile_unmarked_special_support_equality
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
    {x y : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let F := (G.neighborFinset y ∩ B 0) \ S
    (F.card = 8 → ∀ b ∈ U1, (G.neighborFinset b ∩ F).card = 1) ∧
      (F.card = 7 →
        (U1.filter fun b => (G.neighborFinset b ∩ F).card = 0).card = 3) := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let F := (G.neighborFinset y ∩ B 0) \ S
  let f : V → ℕ := fun b => (G.neighborFinset b ∩ F).card
  have hledger :=
    squareOrderNine_threeHigh_secondProfile_unmarked_special_support_ledger
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hy
  dsimp only at hledger
  change U1.card = 24 ∧
    (∀ b ∈ U1, f b ≤ 1) ∧
    (∑ b ∈ U1, f b) = 3 * F.card at hledger
  have hbinary : ∀ b ∈ U1, f b = if f b = 0 then 0 else 1 := by
    intro b hb
    have hle := hledger.2.1 b hb
    split_ifs with hz
    · exact hz
    · omega
  have hnonzero : (∑ b ∈ U1, f b) =
      (U1.filter fun b => f b ≠ 0).card := by
    calc
      _ = ∑ b ∈ U1, if f b = 0 then 0 else 1 := by
        apply Finset.sum_congr rfl
        intro b hb
        exact hbinary b hb
      _ = ∑ b ∈ U1, if f b ≠ 0 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro b _hb
        by_cases hz : f b = 0 <;> simp [hz]
      _ = _ := Finset.sum_boole (fun b => f b ≠ 0) U1
  constructor
  · intro hF8 b hb
    have hsum24 : (∑ b ∈ U1, f b) = 24 := by
      rw [hledger.2.2, hF8]
    have hfilterCard : (U1.filter fun b => f b ≠ 0).card = U1.card := by
      rw [← hnonzero, hsum24, hledger.1]
    have hfilterEq : U1.filter (fun b => f b ≠ 0) = U1 :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    have hne : f b ≠ 0 := by
      have : b ∈ U1.filter (fun z => f z ≠ 0) := by rw [hfilterEq]; exact hb
      exact (Finset.mem_filter.mp this).2
    have hle := hledger.2.1 b hb
    change f b = 1
    omega
  · intro hF7
    have hsum21 : (∑ b ∈ U1, f b) = 21 := by
      rw [hledger.2.2, hF7]
    have hnonzeroCard : (U1.filter fun b => f b ≠ 0).card = 21 := by
      rw [← hnonzero, hsum21]
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := U1) (p := fun b => f b = 0)
    have hzeroCard : (U1.filter fun b => f b = 0).card = 3 := by
      rw [hledger.1] at hpartition
      rw [hnonzeroCard] at hpartition
      omega
    exact hzeroCard

/-- For a nondefect special endpoint whose ordinary support has size seven,
the three missing unmarked bin-one rows are exactly its three antipodal
bin-one fibers. -/
theorem squareOrderNine_threeHigh_secondProfile_antipodal_fiber_eq_missing_rows
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
    {x y : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset x)
    (hF7 : ((G.neighborFinset y ∩ squareOrderNineLowIncidenceBin G 0) \
      (G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0)).card = 7) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let F := (G.neighborFinset y ∩ B 0) \ S
    antipodalNeighbors G y ∩ B 1 =
      U1.filter fun b => (G.neighborFinset b ∩ F).card = 0 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let F := (G.neighborFinset y ∩ B 0) \ S
  let A := antipodalNeighbors G y ∩ B 1
  let Z := U1.filter fun b => (G.neighborFinset b ∩ F).card = 0
  have hyBase := (Finset.mem_sdiff.mp hy).1
  have hAcard : A.card = 3 :=
    squareOrderNine_threeHigh_secondProfile_nondefect_binZero_binOne_antipodal_card
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hy
  have hequality :=
    squareOrderNine_threeHigh_secondProfile_unmarked_special_support_equality
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hyBase
  dsimp only at hequality
  have hZcard : Z.card = 3 := hequality.2 hF7
  have hsub : A ⊆ Z := by
    intro b hbA
    have hbParts := Finset.mem_inter.mp hbA
    have hfiber :=
      squareOrderNine_threeHigh_secondProfile_special_antipodal_binOne_fiber
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hyBase hbA
    dsimp only at hfiber
    have hbU1 : b ∈ U1 := Finset.mem_sdiff.mpr ⟨hbParts.2, hfiber.1⟩
    refine Finset.mem_filter.mpr ⟨hbU1, ?_⟩
    rw [Finset.card_eq_zero]
    ext w
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro hwb hwF
    have hwFParts := Finset.mem_sdiff.mp hwF
    exact Finset.disjoint_left.mp hfiber.2.2.2 hwFParts.1
      (Finset.mem_inter.mpr ⟨hwb, (Finset.mem_inter.mp hwFParts.1).2⟩)
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hAcard, hZcard])

/-- Dual form of the unmarked-row transversal.  The ordinary targets in a
special bin-zero row define pairwise-disjoint three-point blocks on the 24
unmarked bin-one vertices.  Their union is exactly the set of rows which do
not miss that special support. -/
theorem squareOrderNine_threeHigh_secondProfile_special_support_triple_blocks
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
    {x y : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hy : y ∈ G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 0) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let F := (G.neighborFinset y ∩ B 0) \ S
    let Q := fun w => G.neighborFinset w ∩ U1
    (∀ w ∈ F, (Q w).card = 3) ∧
      (∀ w ∈ F, ∀ z ∈ F, w ≠ z → Disjoint (Q w) (Q z)) ∧
      F.biUnion Q =
        U1.filter fun b => (G.neighborFinset b ∩ F).card ≠ 0 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let F := (G.neighborFinset y ∩ B 0) \ S
  let Q := fun w => G.neighborFinset w ∩ U1
  have hyParts := Finset.mem_inter.mp hy
  have hQcard : ∀ w ∈ F, (Q w).card = 3 := by
    intro w hwF
    have hwParts := Finset.mem_sdiff.mp hwF
    have hwBase := Finset.mem_inter.mp hwParts.1
    have hwNotAdjX : ¬ G.Adj w x := by
      intro hwx
      exact hwParts.2 (Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset x w).mpr hwx.symm, hwBase.2⟩)
    have hservice :=
      squareOrderNine_threeHigh_secondProfile_binZero_original_binOne_neighbors
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hwBase.2
    have hservice3 : (G.neighborFinset w ∩ B 1).card = 3 := by
      simpa [hwNotAdjX] using hservice
    have heq : Q w = G.neighborFinset w ∩ B 1 := by
      apply Finset.Subset.antisymm
      · intro b hb
        have hbParts := Finset.mem_inter.mp hb
        exact Finset.mem_inter.mpr ⟨hbParts.1,
          (Finset.mem_sdiff.mp hbParts.2).1⟩
      · intro b hb
        have hbParts := Finset.mem_inter.mp hb
        refine Finset.mem_inter.mpr ⟨hbParts.1,
          Finset.mem_sdiff.mpr ⟨hbParts.2, ?_⟩⟩
        intro hbM
        have hbMParts := Finset.mem_inter.mp hbM
        have hxCommon : x ∈ G.neighborFinset y ∩ G.neighborFinset b :=
          Finset.mem_inter.mpr ⟨
            (G.mem_neighborFinset y x).mpr
              ((G.adj_comm x y).mp
                ((G.mem_neighborFinset x y).mp hyParts.1)),
            (G.mem_neighborFinset b x).mpr
              ((G.adj_comm x b).mp
                ((G.mem_neighborFinset x b).mp hbMParts.1))⟩
        have hwCommon : w ∈ G.neighborFinset y ∩ G.neighborFinset b :=
          Finset.mem_inter.mpr ⟨hwBase.1,
            (G.mem_neighborFinset b w).mpr
              ((G.adj_comm w b).mp
                ((G.mem_neighborFinset w b).mp hbParts.1))⟩
        have hyb : y ≠ b := by
          intro h
          subst b
          have hky := (Finset.mem_filter.mp hyParts.2).2
          have hkb := (Finset.mem_filter.mp hbMParts.2).2
          omega
        have hxw : x ≠ w := by
          intro h
          subst w
          have hkx := (Finset.mem_filter.mp hx).2
          have hkw := (Finset.mem_filter.mp hwBase.2).2
          omega
        have hle := (not_containsC4_iff_forall_common_le_one G).mp hfree y b hyb
        exact hxw (Finset.card_le_one.mp hle x hxCommon w hwCommon)
    rw [heq, hservice3]
  have hpair : ∀ w ∈ F, ∀ z ∈ F, w ≠ z → Disjoint (Q w) (Q z) := by
    intro w hw z hz hwz
    rw [Finset.disjoint_left]
    intro b hbw hbz
    have hwParts := Finset.mem_sdiff.mp hw
    have hzParts := Finset.mem_sdiff.mp hz
    have hbwParts := Finset.mem_inter.mp hbw
    have hbzParts := Finset.mem_inter.mp hbz
    have hyCommon : y ∈ G.neighborFinset w ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset w y).mpr
          ((G.adj_comm y w).mp
            ((G.mem_neighborFinset y w).mp
              (Finset.mem_inter.mp hwParts.1).1)),
        (G.mem_neighborFinset z y).mpr
          ((G.adj_comm y z).mp
            ((G.mem_neighborFinset y z).mp
              (Finset.mem_inter.mp hzParts.1).1))⟩
    have hbCommon : b ∈ G.neighborFinset w ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr ⟨hbwParts.1, hbzParts.1⟩
    have hyb : y ≠ b := by
      intro h
      subst b
      have hky := (Finset.mem_filter.mp hyParts.2).2
      have hkb := (Finset.mem_filter.mp
        (Finset.mem_sdiff.mp hbwParts.2).1).2
      omega
    have hle := (not_containsC4_iff_forall_common_le_one G).mp hfree w z hwz
    exact hyb (Finset.card_le_one.mp hle y hyCommon b hbCommon)
  refine ⟨hQcard, hpair, ?_⟩
  ext b
  simp only [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨w, hwF, hbw⟩
    have hbwParts := Finset.mem_inter.mp hbw
    refine ⟨hbwParts.2, ?_⟩
    rw [Finset.card_ne_zero]
    refine ⟨w, ?_⟩
    exact Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset b w).mpr
        ((G.adj_comm w b).mp
          ((G.mem_neighborFinset w b).mp hbwParts.1)), hwF⟩
  · rintro ⟨hbU1, hbNonzero⟩
    rw [Finset.card_ne_zero] at hbNonzero
    obtain ⟨w, hw⟩ := hbNonzero
    have hwParts := Finset.mem_inter.mp hw
    exact ⟨w, hwParts.2, Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset w b).mpr
        ((G.adj_comm b w).mp
          ((G.mem_neighborFinset b w).mp hwParts.1)), hbU1⟩⟩

/-- Each marked bin-one row produces a seven-edge matching on the unmarked
bin-one core: its seven bin-zero targets each have exactly two unmarked
bin-one neighbors, and these pairs are mutually disjoint. -/
theorem squareOrderNine_threeHigh_secondProfile_marked_support_pair_matching
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
    {x m : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hm : m ∈ G.neighborFinset x ∩ squareOrderNineLowIncidenceBin G 1) :
    let B := squareOrderNineLowIncidenceBin G
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let F := G.neighborFinset m ∩ B 0
    let Q := fun w => G.neighborFinset w ∩ U1
    F.card = 7 ∧
      (∀ w ∈ F, (Q w).card = 2) ∧
      (∀ w ∈ F, ∀ z ∈ F, w ≠ z → Disjoint (Q w) (Q z)) ∧
      (F.biUnion Q).card = 14 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let F := G.neighborFinset m ∩ B 0
  let Q := fun w => G.neighborFinset w ∩ U1
  have hmParts := Finset.mem_inter.mp hm
  have hmx : G.Adj m x :=
    (G.adj_comm x m).mp ((G.mem_neighborFinset x m).mp hmParts.1)
  have hmdeg := squareOrderNine_threeHigh_secondProfile_binOne_original_degrees
    G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hmParts.2
  dsimp only at hmdeg
  have hFcard : F.card = 7 := by simpa [hmx] using hmdeg.2
  have hQcard : ∀ w ∈ F, (Q w).card = 2 := by
    intro w hwF
    have hwParts := Finset.mem_inter.mp hwF
    have hwm : G.Adj w m :=
      (G.adj_comm m w).mp ((G.mem_neighborFinset m w).mp hwParts.1)
    have hwNotAdjX : ¬ G.Adj w x := by
      intro hwx
      exact (squareOrderNine_threeHigh_binThree_binZero_neighbor_not_binOneAdjacent
        G hfree hhigh hx hwParts.2 hmParts.2 hwx.symm) hwm
    have hservice :=
      squareOrderNine_threeHigh_secondProfile_binZero_original_binOne_neighbors
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hwParts.2
    have hB1card : (G.neighborFinset w ∩ B 1).card = 3 := by
      simpa [hwNotAdjX] using hservice
    have hmarkedEq : (G.neighborFinset w ∩ B 1) ∩ M = {m} := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hwzN, hzB1⟩, hzM⟩
        have hzMParts := Finset.mem_inter.mp hzM
        by_contra hzm
        have hxCommon : x ∈ G.neighborFinset m ∩ G.neighborFinset z :=
          Finset.mem_inter.mpr ⟨
            (G.mem_neighborFinset m x).mpr hmx,
            (G.mem_neighborFinset z x).mpr
              ((G.adj_comm x z).mp
                ((G.mem_neighborFinset x z).mp hzMParts.1))⟩
        have hwCommon : w ∈ G.neighborFinset m ∩ G.neighborFinset z :=
          Finset.mem_inter.mpr ⟨
            (G.mem_neighborFinset m w).mpr hwm.symm,
            (G.mem_neighborFinset z w).mpr
              ((G.adj_comm w z).mp ((G.mem_neighborFinset w z).mp hwzN))⟩
        have hxw : x ≠ w := by
          intro h
          subst w
          have hkx := (Finset.mem_filter.mp hx).2
          have hkw := (Finset.mem_filter.mp hwParts.2).2
          omega
        have hle := (not_containsC4_iff_forall_common_le_one G).mp hfree m z
          (Ne.symm hzm)
        exact hxw (Finset.card_le_one.mp hle x hxCommon w hwCommon)
      · intro hzm
        subst z
        exact ⟨⟨(G.mem_neighborFinset w m).mpr hwm, hmParts.2⟩,
          Finset.mem_inter.mpr ⟨hmParts.1, hmParts.2⟩⟩
    have hQeq : Q w = (G.neighborFinset w ∩ B 1) \ M := by
      ext z
      simp only [Q, U1, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    have hmarkedEq' : M ∩ (G.neighborFinset w ∩ B 1) = {m} := by
      rw [Finset.inter_comm]
      exact hmarkedEq
    rw [hQeq, Finset.card_sdiff, hmarkedEq', hB1card]
    simp
  have hpair : ∀ w ∈ F, ∀ z ∈ F, w ≠ z → Disjoint (Q w) (Q z) := by
    intro w hw z hz hwz
    rw [Finset.disjoint_left]
    intro b hbw hbz
    have hwParts := Finset.mem_inter.mp hw
    have hzParts := Finset.mem_inter.mp hz
    have hbwParts := Finset.mem_inter.mp hbw
    have hbzParts := Finset.mem_inter.mp hbz
    have hmCommon : m ∈ G.neighborFinset w ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset w m).mpr
          ((G.adj_comm m w).mp ((G.mem_neighborFinset m w).mp hwParts.1)),
        (G.mem_neighborFinset z m).mpr
          ((G.adj_comm m z).mp ((G.mem_neighborFinset m z).mp hzParts.1))⟩
    have hbCommon : b ∈ G.neighborFinset w ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr ⟨hbwParts.1, hbzParts.1⟩
    have hmb : m ≠ b := by
      intro h
      subst b
      exact (Finset.mem_sdiff.mp hbwParts.2).2 hm
    have hle := (not_containsC4_iff_forall_common_le_one G).mp hfree w z hwz
    exact hmb (Finset.card_le_one.mp hle m hmCommon b hbCommon)
  refine ⟨hFcard, hQcard, hpair, ?_⟩
  rw [Finset.card_biUnion hpair]
  calc
    (∑ w ∈ F, (Q w).card) = ∑ _w ∈ F, 2 := by
      apply Finset.sum_congr rfl
      intro w hw
      exact hQcard w hw
    _ = 14 := by simp [hFcard]

/-- Removing the three marked vertices from the 27-vertex two-regular
bin-one defect core leaves exactly 21 defect edges.  The marked set is
defect-independent and contributes exactly six crossing edges. -/
theorem squareOrderNine_threeHigh_secondProfile_unmarked_binOne_defect_edges
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    (D.induce (↑U1 : Set V)).edgeFinset.card = 21 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let K := D.induce (↑U1 : Set V)
  have hmarked :=
    squareOrderNine_threeHigh_secondProfile_marked_core_cardinalities
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hmarked
  have hMsub : M ⊆ B 1 := Finset.inter_subset_right
  have hMcard : M.card = 3 := hmarked.2
  have hU1card : U1.card = 24 := by
    rw [Finset.card_sdiff_of_subset hMsub, hmarked.1, hMcard]
  have hBsplit : B 1 = M ∪ U1 := by
    ext z
    simp only [M, U1, Finset.mem_union, Finset.mem_inter,
      Finset.mem_sdiff]
    tauto
  have hMUdisj : Disjoint M U1 := by
    rw [Finset.disjoint_left]
    intro z hzM hzU
    exact (Finset.mem_sdiff.mp hzU).2 hzM
  have hsplit (z : V) :
      (D.neighborFinset z ∩ M).card +
        (D.neighborFinset z ∩ U1).card =
          (D.neighborFinset z ∩ B 1).card := by
    rw [hBsplit, Finset.inter_union_distrib_left,
      Finset.card_union_of_disjoint
        (hMUdisj.mono (Finset.inter_subset_right)
          (Finset.inter_subset_right))]
  have hmarkedInternalZero : ∀ m ∈ M,
      (D.neighborFinset m ∩ M).card = 0 := by
    intro m hm
    rw [Finset.card_eq_zero]
    ext z
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro hDmz hzM
    have hmParts := Finset.mem_inter.mp hm
    have hzParts := Finset.mem_inter.mp hzM
    have hmz : m ≠ z := by
      intro h
      subst z
      exact D.loopless.irrefl m ((D.mem_neighborFinset m m).mp hDmz)
    exact (squareOrderNine_threeHigh_secondProfile_binThree_partners_not_defectAdjacent
      G hfree hmz
        ((G.adj_comm x m).mp ((G.mem_neighborFinset x m).mp hmParts.1))
        ((G.adj_comm x z).mp ((G.mem_neighborFinset x z).mp hzParts.1)))
      ((D.mem_neighborFinset m z).mp hDmz)
  have hmarkedCross : ∀ m ∈ M,
      (D.neighborFinset m ∩ U1).card = 2 := by
    intro m hm
    have hmB := (Finset.mem_inter.mp hm).2
    have htype := squareOrderNine_threeHigh_secondProfile_binOne_defect_neighbors
      G hfree hmin hcover hcard hp hhigh hc2 hc4 hmB
    dsimp only at htype
    have hs := hsplit m
    rw [hmarkedInternalZero m hm, htype.2.1] at hs
    omega
  have hcrossM : (∑ m ∈ M, (D.neighborFinset m ∩ U1).card) = 6 := by
    calc
      _ = ∑ _m ∈ M, 2 := by
        apply Finset.sum_congr rfl
        intro m hm
        exact hmarkedCross m hm
      _ = 6 := by simp [hMcard]
  have hcrossU : (∑ z ∈ U1, (D.neighborFinset z ∩ M).card) = 6 := by
    rw [sum_card_neighborFinset_inter_comm D U1 M]
    exact hcrossM
  have hunmarkedTotal : ∀ z ∈ U1,
      (D.neighborFinset z ∩ B 1).card = 2 := by
    intro z hz
    have hzB := (Finset.mem_sdiff.mp hz).1
    have htype := squareOrderNine_threeHigh_secondProfile_binOne_defect_neighbors
      G hfree hmin hcover hcard hp hhigh hc2 hc4 hzB
    dsimp only at htype
    exact htype.2.1
  have hsumSplit :
      (∑ z ∈ U1, (D.neighborFinset z ∩ M).card) +
        (∑ z ∈ U1, (D.neighborFinset z ∩ U1).card) = 48 := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ z ∈ U1, ((D.neighborFinset z ∩ M).card +
          (D.neighborFinset z ∩ U1).card)) =
          ∑ z ∈ U1, (D.neighborFinset z ∩ B 1).card := by
            apply Finset.sum_congr rfl
            intro z _hz
            exact hsplit z
      _ = ∑ _z ∈ U1, 2 := by
            apply Finset.sum_congr rfl
            intro z hz
            exact hunmarkedTotal z hz
      _ = 48 := by simp [hU1card]
  have hinternalSum :
      (∑ z ∈ U1, (D.neighborFinset z ∩ U1).card) = 42 := by
    rw [hcrossU] at hsumSplit
    omega
  have hdegreeBridge :
      (∑ z ∈ U1, (D.neighborFinset z ∩ U1).card) =
        ∑ z : ↥(↑U1 : Set V), K.degree z := by
    rw [← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro z _hz
    exact (degree_induce_finset_eq_card_inter D U1 z).symm
  have hdegreeSum :
      (∑ z : ↥(↑U1 : Set V), K.degree z) = 42 := by
    rw [← hdegreeBridge]
    exact hinternalSum
  change K.edgeFinset.card = 21
  have hhand := K.sum_degrees_eq_twice_card_edges
  rw [hdegreeSum] at hhand
  omega

/-- The 24 unmarked bin-one vertices induce a cubic graph in the original
graph, hence exactly 36 original edges.  Marked bin-one vertices have no
bin-one neighbors, so deleting them loses no neighbor of an unmarked row. -/
theorem squareOrderNine_threeHigh_secondProfile_unmarked_binOne_original_cubic
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    let B := squareOrderNineLowIncidenceBin G
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let K := G.induce (↑U1 : Set V)
    U1.card = 24 ∧ (∀ z : ↥(↑U1 : Set V), K.degree z = 3) ∧
      K.edgeFinset.card = 36 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let K := G.induce (↑U1 : Set V)
  have hmarked :=
    squareOrderNine_threeHigh_secondProfile_marked_core_cardinalities
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hmarked
  have hMsub : M ⊆ B 1 := Finset.inter_subset_right
  have hU1card : U1.card = 24 := by
    rw [Finset.card_sdiff_of_subset hMsub, hmarked.1, hmarked.2]
  have hdegree : ∀ z : ↥(↑U1 : Set V), K.degree z = 3 := by
    intro z
    have hzU : z.1 ∈ U1 := z.2
    have hzParts := Finset.mem_sdiff.mp hzU
    have hzx : ¬ G.Adj z.1 x := by
      intro hzx
      exact hzParts.2 (Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset x z.1).mpr hzx.symm, hzParts.1⟩)
    have hzdeg := squareOrderNine_threeHigh_secondProfile_binOne_original_degrees
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hzParts.1
    dsimp only at hzdeg
    have hB1card : (G.neighborFinset z.1 ∩ B 1).card = 3 := by
      simpa [hzx] using hzdeg.1
    have heq : G.neighborFinset z.1 ∩ U1 = G.neighborFinset z.1 ∩ B 1 := by
      apply Finset.Subset.antisymm
      · intro w hw
        have hwParts := Finset.mem_inter.mp hw
        exact Finset.mem_inter.mpr ⟨hwParts.1,
          (Finset.mem_sdiff.mp hwParts.2).1⟩
      · intro w hw
        have hwParts := Finset.mem_inter.mp hw
        refine Finset.mem_inter.mpr ⟨hwParts.1,
          Finset.mem_sdiff.mpr ⟨hwParts.2, ?_⟩⟩
        intro hwM
        have hwMParts := Finset.mem_inter.mp hwM
        have hwx : G.Adj w x :=
          (G.adj_comm x w).mp
            ((G.mem_neighborFinset x w).mp hwMParts.1)
        have hwdeg := squareOrderNine_threeHigh_secondProfile_binOne_original_degrees
          G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hwMParts.2
        dsimp only at hwdeg
        have hwzero : (G.neighborFinset w ∩ B 1).card = 0 := by
          simpa [hwx] using hwdeg.1
        have hzmem : z.1 ∈ G.neighborFinset w ∩ B 1 :=
          Finset.mem_inter.mpr ⟨
            (G.mem_neighborFinset w z.1).mpr
              ((G.adj_comm z.1 w).mp
                ((G.mem_neighborFinset z.1 w).mp hwParts.1)), hzParts.1⟩
        have hempty := Finset.card_eq_zero.mp hwzero
        simpa [hempty] using hzmem
    rw [degree_induce_finset_eq_card_inter, heq, hB1card]
  have hdegreeSum : (∑ z : ↥(↑U1 : Set V), K.degree z) = 72 := by
    simp_rw [hdegree]
    simp [hU1card]
  have hedges : K.edgeFinset.card = 36 := by
    have hhand := K.sum_degrees_eq_twice_card_edges
    rw [hdegreeSum] at hhand
    omega
  exact ⟨hU1card, hdegree, hedges⟩

/-- The three high roots partition the 24 unmarked bin-one vertices into
three eight-point fibers.  Each high has nine bin-one neighbors, exactly one
of which is the marked partner shared with the rare bin-three vertex. -/
theorem squareOrderNine_threeHigh_secondProfile_unmarked_high_fiber_partition
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    let H := squareOrderHighVertices G 9
    let B := squareOrderNineLowIncidenceBin G
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let F := fun a => G.neighborFinset a ∩ U1
    H.card = 3 ∧
      (∀ a ∈ H, (F a).card = 8) ∧
      (∀ a ∈ H, ∀ b ∈ H, a ≠ b → Disjoint (F a) (F b)) ∧
      H.biUnion F = U1 := by
  classical
  dsimp only
  let H := squareOrderHighVertices G 9
  let B := squareOrderNineLowIncidenceBin G
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let F := fun a => G.neighborFinset a ∩ U1
  have hfiber : ∀ a ∈ H, (F a).card = 8 := by
    intro a ha
    have hsplit := squareOrderNine_threeHigh_secondProfile_highRoot_neighbor_split
      G hfree hmin hcard hp hhigh hc2 hc4 ha
    have hB1card : (G.neighborFinset a ∩ B 1).card = 9 := hsplit.1
    have hpartner :=
      squareOrderNine_threeHigh_secondProfile_binThree_unique_binOne_partner_at_highRoot
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx ha
    have hinter : M ∩ (G.neighborFinset a ∩ B 1) =
        G.neighborFinset a ∩ G.neighborFinset x ∩ B 1 := by
      ext z
      simp only [M, Finset.mem_inter]
      tauto
    have hFeq : F a = (G.neighborFinset a ∩ B 1) \ M := by
      ext z
      simp only [F, U1, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    rw [hFeq, Finset.card_sdiff, hinter, hpartner, hB1card]
  have hpair : ∀ a ∈ H, ∀ b ∈ H, a ≠ b → Disjoint (F a) (F b) := by
    intro a ha b hb hab
    rw [Finset.disjoint_left]
    intro z hza hzb
    have hzaParts := Finset.mem_inter.mp hza
    have hzbParts := Finset.mem_inter.mp hzb
    have hzB1 := (Finset.mem_sdiff.mp hzaParts.2).1
    have haMem : a ∈ G.neighborFinset z ∩ H :=
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset z a).mpr
          ((G.adj_comm a z).mp
            ((G.mem_neighborFinset a z).mp hzaParts.1)), ha⟩
    have hbMem : b ∈ G.neighborFinset z ∩ H :=
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset z b).mpr
          ((G.adj_comm b z).mp
            ((G.mem_neighborFinset b z).mp hzbParts.1)), hb⟩
    have hkz : (G.neighborFinset z ∩ H).card = 1 :=
      (Finset.mem_filter.mp hzB1).2
    have hle : (G.neighborFinset z ∩ H).card ≤ 1 := by omega
    exact hab (Finset.card_le_one.mp hle a haMem b hbMem)
  have hunion : H.biUnion F = U1 := by
    ext z
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨a, _ha, hza⟩
      exact (Finset.mem_inter.mp hza).2
    · intro hzU
      have hzB1 := (Finset.mem_sdiff.mp hzU).1
      have hkz : (G.neighborFinset z ∩ H).card = 1 :=
        (Finset.mem_filter.mp hzB1).2
      have hnonempty : (G.neighborFinset z ∩ H).Nonempty := by
        rw [← Finset.card_pos, hkz]
        norm_num
      obtain ⟨a, ha⟩ := hnonempty
      have haParts := Finset.mem_inter.mp ha
      refine ⟨a, haParts.2, Finset.mem_inter.mpr ⟨?_, hzU⟩⟩
      exact (G.mem_neighborFinset a z).mpr
        ((G.adj_comm z a).mp ((G.mem_neighborFinset z a).mp haParts.1))
  exact ⟨hhigh, hfiber, hpair, hunion⟩

/-- The 47 ordinary bin-zero targets split into 21 targets lying in a marked
bin-one support, with two unmarked bin-one neighbors each, and 26 remaining
targets, with three unmarked neighbors each.  Consequently the bin-zero
centers contribute exactly 99 unordered pairs of unmarked bin-one vertices. -/
theorem squareOrderNine_threeHigh_secondProfile_binZero_unmarked_pair_census
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
    P.card = 21 ∧ (T \ P).card = 26 ∧
      (∀ y ∈ P, (G.neighborFinset y ∩ U1).card = 2) ∧
      (∀ y ∈ T \ P, (G.neighborFinset y ∩ U1).card = 3) ∧
      (∑ y ∈ T, Nat.choose (G.neighborFinset y ∩ U1).card 2) = 99 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let P := M.biUnion fun m => G.neighborFinset m ∩ B 0
  have hpack := squareOrderNine_threeHigh_secondProfile_marked_binOne_row_packing
    G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hpack
  have hPcard : P.card = 21 := by
    rw [Finset.card_biUnion hpack.2.2.1]
    exact hpack.2.2.2
  have hPsub : P ⊆ T := by
    intro y hyP
    simp only [P, Finset.mem_biUnion] at hyP
    obtain ⟨m, hmM, hym⟩ := hyP
    have hmParts := Finset.mem_inter.mp hmM
    have hymParts := Finset.mem_inter.mp hym
    refine Finset.mem_sdiff.mpr ⟨hymParts.2, ?_⟩
    intro hyS
    have hySParts := Finset.mem_inter.mp hyS
    have hxy : G.Adj x y :=
      (G.mem_neighborFinset x y).mp hySParts.1
    have hymAdj : G.Adj y m :=
      (G.adj_comm m y).mp ((G.mem_neighborFinset m y).mp hymParts.1)
    exact (squareOrderNine_threeHigh_binThree_binZero_neighbor_not_binOneAdjacent
      G hfree hhigh hx hySParts.2 hmParts.2 hxy) hymAdj
  have hTcard : T.card = 47 := by
    have hB0card := squareOrderNine_threeHigh_secondProfile_binZero_card
      G hcard hp hhigh hc3
    have hScard :=
      (squareOrderNine_threeHigh_secondProfile_binThree_original_neighborhood_census
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx).2.2
    rw [Finset.card_sdiff_of_subset Finset.inter_subset_right, hB0card, hScard]
  have hcompCard : (T \ P).card = 26 := by
    rw [Finset.card_sdiff_of_subset hPsub, hTcard, hPcard]
  have hPon : ∀ y ∈ P, (G.neighborFinset y ∩ U1).card = 2 := by
    intro y hyP
    simp only [P, Finset.mem_biUnion] at hyP
    obtain ⟨m, hmM, hym⟩ := hyP
    have hmatch :=
      squareOrderNine_threeHigh_secondProfile_marked_support_pair_matching
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hmM
    dsimp only at hmatch
    exact hmatch.2.1 y hym
  have hPoff : ∀ y ∈ T \ P,
      (G.neighborFinset y ∩ U1).card = 3 := by
    intro y hy
    have hyParts := Finset.mem_sdiff.mp hy
    have hyT := Finset.mem_sdiff.mp hyParts.1
    have hyNotAdjX : ¬ G.Adj y x := by
      intro hyx
      exact hyT.2 (Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset x y).mpr hyx.symm, hyT.1⟩)
    have hservice :=
      squareOrderNine_threeHigh_secondProfile_binZero_original_binOne_neighbors
        G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx hyT.1
    have hB1card : (G.neighborFinset y ∩ B 1).card = 3 := by
      simpa [hyNotAdjX] using hservice
    have heq : G.neighborFinset y ∩ U1 = G.neighborFinset y ∩ B 1 := by
      apply Finset.Subset.antisymm
      · intro m hm
        have hmParts := Finset.mem_inter.mp hm
        exact Finset.mem_inter.mpr ⟨hmParts.1,
          (Finset.mem_sdiff.mp hmParts.2).1⟩
      · intro m hm
        have hmParts := Finset.mem_inter.mp hm
        refine Finset.mem_inter.mpr ⟨hmParts.1,
          Finset.mem_sdiff.mpr ⟨hmParts.2, ?_⟩⟩
        intro hmM
        exact hyParts.2 (by
          simp only [P, Finset.mem_biUnion]
          exact ⟨m, hmM, Finset.mem_inter.mpr ⟨
            (G.mem_neighborFinset m y).mpr
              ((G.adj_comm y m).mp
                ((G.mem_neighborFinset y m).mp hmParts.1)), hyT.1⟩⟩)
    rw [heq, hB1card]
  have hTsplit : T = P ∪ (T \ P) := by
    ext y
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hyT
      by_cases hyP : y ∈ P
      · exact Or.inl hyP
      · exact Or.inr ⟨hyT, hyP⟩
    · rintro (hyP | ⟨hyT, _hyNotP⟩)
      · exact hPsub hyP
      · exact hyT
  have hdisj : Disjoint P (T \ P) := by
    rw [Finset.disjoint_left]
    intro y hyP hyComp
    exact (Finset.mem_sdiff.mp hyComp).2 hyP
  have hpairs :
      (∑ y ∈ T, Nat.choose (G.neighborFinset y ∩ U1).card 2) = 99 := by
    rw [hTsplit, Finset.sum_union hdisj]
    have hsumP :
        (∑ y ∈ P, Nat.choose (G.neighborFinset y ∩ U1).card 2) = 21 := by
      calc
        _ = ∑ _y ∈ P, Nat.choose 2 2 := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [hPon y hy]
        _ = 21 := by simp [hPcard]
    have hsumC :
        (∑ y ∈ T \ P, Nat.choose (G.neighborFinset y ∩ U1).card 2) = 78 := by
      calc
        _ = ∑ _y ∈ T \ P, Nat.choose 3 2 := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [hPoff y hy]
        _ = 78 := by norm_num [hcompCard]
    rw [hsumP, hsumC]
  exact ⟨hPcard, hcompCard, hPon, hPoff, hpairs⟩

/-- Numeric capstone for the 24-vertex unmarked bin-one pair budget.  The
bin-zero centers contribute 99 pairs, bin-one centers 72, high centers 84,
and the induced defect graph has 21 edges; these exhaust all `C(24,2)=276`
unordered pairs. -/
theorem squareOrderNine_threeHigh_secondProfile_unmarked_pair_budget
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    let D := secondOrderDefectGraph G
    let H := squareOrderHighVertices G 9
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let K := G.induce (↑U1 : Set V)
    let L := D.induce (↑U1 : Set V)
    let F := fun a => G.neighborFinset a ∩ U1
    U1.card = 24 ∧
      (∑ y ∈ T, Nat.choose (G.neighborFinset y ∩ U1).card 2) = 99 ∧
      (∑ z : ↥(↑U1 : Set V), Nat.choose (K.degree z) 2) = 72 ∧
      (∑ a ∈ H, Nat.choose (F a).card 2) = 84 ∧
      L.edgeFinset.card = 21 ∧
      99 + 72 + 84 + L.edgeFinset.card = Nat.choose U1.card 2 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let H := squareOrderHighVertices G 9
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let K := G.induce (↑U1 : Set V)
  let L := D.induce (↑U1 : Set V)
  let F := fun a => G.neighborFinset a ∩ U1
  have hcubic :=
    squareOrderNine_threeHigh_secondProfile_unmarked_binOne_original_cubic
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hcubic
  change U1.card = 24 ∧ (∀ z : ↥(↑U1 : Set V), K.degree z = 3) ∧
    K.edgeFinset.card = 36 at hcubic
  have hB0 :=
    squareOrderNine_threeHigh_secondProfile_binZero_unmarked_pair_census
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hB0
  change _ ∧ _ ∧ _ ∧ _ ∧
    (∑ y ∈ T, Nat.choose (G.neighborFinset y ∩ U1).card 2) = 99 at hB0
  have hfibers :=
    squareOrderNine_threeHigh_secondProfile_unmarked_high_fiber_partition
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hfibers
  change H.card = 3 ∧ (∀ a ∈ H, (F a).card = 8) ∧
    (∀ a ∈ H, ∀ b ∈ H, a ≠ b → Disjoint (F a) (F b)) ∧
    H.biUnion F = U1 at hfibers
  have hdefect :=
    squareOrderNine_threeHigh_secondProfile_unmarked_binOne_defect_edges
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hdefect
  change L.edgeFinset.card = 21 at hdefect
  have hB1pairs :
      (∑ z : ↥(↑U1 : Set V), Nat.choose (K.degree z) 2) = 72 := by
    simp_rw [hcubic.2.1]
    rw [Finset.sum_const]
    simp only [Finset.card_univ, nsmul_eq_mul]
    have hcardSubtype : Fintype.card ↥(↑U1 : Set V) = 24 := by
      simpa using hcubic.1
    rw [hcardSubtype]
    norm_num [Nat.choose]
  have hHpairs : (∑ a ∈ H, Nat.choose (F a).card 2) = 84 := by
    calc
      _ = ∑ _a ∈ H, Nat.choose 8 2 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hfibers.2.1 a ha]
      _ = 84 := by
        rw [Finset.sum_const, hfibers.1]
        norm_num [Nat.choose]
  have htotal : 99 + 72 + 84 + L.edgeFinset.card = Nat.choose U1.card 2 := by
    rw [hdefect, hcubic.1]
    norm_num [Nat.choose]
  exact ⟨hcubic.1, hB0.2.2.2.2, hB1pairs, hHpairs, hdefect, htotal⟩

/-- High-color transversality on the unmarked bin-one core.  Two distinct
vertices in the same high fiber cannot have a low common original neighbor,
and they cannot be adjacent in the second-order defect graph. -/
theorem squareOrderNine_threeHigh_secondProfile_same_high_fiber_separation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {u v a w : V}
    (huv : u ≠ v)
    (ha : a ∈ squareOrderHighVertices G 9)
    (hau : G.Adj a u) (hav : G.Adj a v)
    (hwLow : w ∉ squareOrderHighVertices G 9) :
    ¬ (G.Adj w u ∧ G.Adj w v) ∧
      ¬ (secondOrderDefectGraph G).Adj u v := by
  constructor
  · rintro ⟨hwu, hwv⟩
    have haCommon : a ∈ G.neighborFinset u ∩ G.neighborFinset v :=
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset u a).mpr hau.symm,
        (G.mem_neighborFinset v a).mpr hav.symm⟩
    have hwCommon : w ∈ G.neighborFinset u ∩ G.neighborFinset v :=
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset u w).mpr hwu.symm,
        (G.mem_neighborFinset v w).mpr hwv.symm⟩
    have haw : a ≠ w := by
      intro h
      subst w
      exact hwLow ha
    have hle := common_le_one_of_not_containsC4 hfree u v huv
    exact haw (Finset.card_le_one.mp hle a haCommon w hwCommon)
  · exact not_secondOrderDefect_adj_of_commonNeighbor
      G hfree huv hau.symm hav.symm

/-- Every unmarked bin-one row has at most one original neighbor in each
high-color fiber, and its three fiber-intersection sizes sum to three.  This
is the incidence form of the color-resolved perfect-matching structure of
the cubic unmarked core. -/
theorem squareOrderNine_threeHigh_secondProfile_unmarked_core_color_ledger
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
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3) :
    let H := squareOrderHighVertices G 9
    let B := squareOrderNineLowIncidenceBin G
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let F := fun a => G.neighborFinset a ∩ U1
    ∀ z ∈ U1,
      (∀ a ∈ H, (G.neighborFinset z ∩ F a).card ≤ 1) ∧
      (∑ a ∈ H, (G.neighborFinset z ∩ F a).card) = 3 := by
  classical
  dsimp only
  let H := squareOrderHighVertices G 9
  let B := squareOrderNineLowIncidenceBin G
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let F := fun a => G.neighborFinset a ∩ U1
  have hpartition :=
    squareOrderNine_threeHigh_secondProfile_unmarked_high_fiber_partition
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hpartition
  change H.card = 3 ∧ (∀ a ∈ H, (F a).card = 8) ∧
    (∀ a ∈ H, ∀ b ∈ H, a ≠ b → Disjoint (F a) (F b)) ∧
    H.biUnion F = U1 at hpartition
  have hcubic :=
    squareOrderNine_threeHigh_secondProfile_unmarked_binOne_original_cubic
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hcubic
  change U1.card = 24 ∧
    (∀ q : ↥(↑U1 : Set V), (G.induce (↑U1 : Set V)).degree q = 3) ∧
    (G.induce (↑U1 : Set V)).edgeFinset.card = 36 at hcubic
  intro z hzU
  have hzB := (Finset.mem_sdiff.mp hzU).1
  have hzLow : z ∉ H :=
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hzB).1).2
  have hle : ∀ a ∈ H, (G.neighborFinset z ∩ F a).card ≤ 1 := by
    intro a ha
    rw [Finset.card_le_one]
    intro u hu v hv
    by_contra huv
    have huParts := Finset.mem_inter.mp hu
    have hvParts := Finset.mem_inter.mp hv
    have huF := Finset.mem_inter.mp huParts.2
    have hvF := Finset.mem_inter.mp hvParts.2
    have hsep := squareOrderNine_threeHigh_secondProfile_same_high_fiber_separation
      G hfree huv ha
        ((G.mem_neighborFinset a u).mp huF.1)
        ((G.mem_neighborFinset a v).mp hvF.1) hzLow
    exact hsep.1 ⟨
      (G.mem_neighborFinset z u).mp huParts.1,
      (G.mem_neighborFinset z v).mp hvParts.1⟩
  have hpair : ∀ a ∈ H, ∀ b ∈ H, a ≠ b →
      Disjoint (G.neighborFinset z ∩ F a) (G.neighborFinset z ∩ F b) := by
    intro a ha b hb hab
    exact (hpartition.2.2.1 a ha b hb hab).mono
      Finset.inter_subset_right Finset.inter_subset_right
  have hunion : H.biUnion (fun a => G.neighborFinset z ∩ F a) =
      G.neighborFinset z ∩ U1 := by
    ext u
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · rintro ⟨a, ha, hzu, huF⟩
      exact ⟨hzu, (Finset.mem_inter.mp huF).2⟩
    · rintro ⟨hzu, huU⟩
      have huUnion : u ∈ H.biUnion F := by
        rw [hpartition.2.2.2]
        exact huU
      simp only [Finset.mem_biUnion] at huUnion
      obtain ⟨a, ha, huF⟩ := huUnion
      exact ⟨a, ha, hzu, huF⟩
  have hcard3 : (G.neighborFinset z ∩ U1).card = 3 := by
    have hdeg := hcubic.2.1 (⟨z, hzU⟩ : ↥(↑U1 : Set V))
    rw [degree_induce_finset_eq_card_inter] at hdeg
    simpa only using hdeg
  refine ⟨hle, ?_⟩
  rw [← Finset.card_biUnion hpair, hunion, hcard3]

end

end Erdos85

#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binZero_defect_neighbor_dichotomy
#print axioms Erdos85.independent_nonisolated_card_le_edges
#print axioms Erdos85.squareOrderNine_binZero_antipodal_triangle_profile
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_special_binZero_card
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binThree_reservoir_edgeLabels
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binThree_localTriangleProfile
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binThree_original_binZero_defect_eq_tf
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binThree_original_binZero_defect_card
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binThree_nondefect_binZero_pair
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binThree_binZero_neighbor_not_highAdjacent
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binThree_nondefect_binZero_pair_adjacent
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_nondefect_binZero_is_regular
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_trianglePair_common_binOne_forces_antipodal
#print axioms Erdos85.squareOrderNine_threeHigh_binThree_binZero_neighbor_not_binOneAdjacent
#print axioms Erdos85.squareOrderNine_threeHigh_binThree_binZero_neighbor_binOne_defect_antipodal
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_nondefect_binZero_binOne_antipodal_card
#print axioms Erdos85.squareOrderNine_threeHigh_colored_defect_edge_card_dvd_three
#print axioms Erdos85.squareOrderNine_threeHigh_sum_highIncidence_over_lowNeighborhood
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binZero_original_binOne_neighbors
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binZero_binOne_original_incidence
#print axioms Erdos85.squareOrderNine_originalNeighbor_lowBin_partition
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binZero_card
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_original_lowBin_quotient
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_original_lowBin_edge_quotient
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_special_binZero_row_packing
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_special_binZero_ordinary_support
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_special_binZero_target_dichotomy
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_ordinary_binZero_residual_census
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binOne_original_degrees
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_marked_binOne_row_packing
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_six_row_support_saturation
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_special_antipodal_binOne_fiber
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_unmarked_special_support_ledger
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_unmarked_special_support_equality
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_antipodal_fiber_eq_missing_rows
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_special_support_triple_blocks
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_marked_support_pair_matching
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_unmarked_binOne_defect_edges
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_unmarked_binOne_original_cubic
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_unmarked_high_fiber_partition
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binZero_unmarked_pair_census
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_unmarked_pair_budget
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_same_high_fiber_separation
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_unmarked_core_color_ledger
