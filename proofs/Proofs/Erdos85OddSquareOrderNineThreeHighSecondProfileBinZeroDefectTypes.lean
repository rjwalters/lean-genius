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
