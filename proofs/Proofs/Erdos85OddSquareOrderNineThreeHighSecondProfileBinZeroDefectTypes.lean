import Proofs.Erdos85OddSquareOrderNineThreeHighSecondProfileCore

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

end

end Erdos85

#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binZero_defect_neighbor_dichotomy
#print axioms Erdos85.independent_nonisolated_card_le_edges
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_special_binZero_card
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binThree_reservoir_edgeLabels
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binThree_localTriangleProfile
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binThree_original_binZero_defect_eq_tf
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binThree_original_binZero_defect_card
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binThree_nondefect_binZero_pair
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binThree_binZero_neighbor_not_highAdjacent
