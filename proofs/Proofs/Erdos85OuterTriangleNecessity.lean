import Proofs.Erdos85OrderFortyNineOuterDefect
import Proofs.Erdos85AntipodalCycleReservoir
import Proofs.Erdos85DefectCliquePlateauRigidity

/-!
# A five-point defect clique forces an original triangle

In a six-regular `C₄`-free graph on forty vertices, a triangle-free vertex
has only three antipodes (vertices beyond distance two).  A five-point clique
in the second-order defect graph cannot exist if every edge is triangle-free:
the original graph induced on the clique is a matching, so parity leaves an
unmatched clique vertex, whose four clique-mates would all have to be among
its three antipodes.

Applied to the five-point branches of the unique-high outer graph, this
proves that the outer graph necessarily contains a triangle.  No cage
classification or finite enumeration is required.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Odd defect-clique triangle pressure.**  In the positive-excess regular
band, an odd second-order-defect clique contains a vertex whose number of
triangle-free incident edges is at most `e + 3 - |C|`.

Indeed the original graph induced on a defect clique is a matching.  The
odd clique therefore has an unmatched vertex, and all its other clique
vertices must be antipodes of that vertex. -/
theorem exists_triangleFreeNeighbors_card_le_of_odd_defectClique
    {W : Type*} [Fintype W] [DecidableEq W]
    (R : SimpleGraph W) [DecidableRel R.Adj]
    [DecidableRel (antipodalGraph R).Adj]
    [DecidableRel (triangleFreeEdgeGraph R).Adj]
    (hfree : ¬ containsC4 W R) {d e : ℕ}
    (hreg : ∀ x, R.degree x = d)
    (hcard : Fintype.card W = d * (d - 1) + 3 + e)
    (C : Finset W) (hCodd : Odd C.card)
    (hclique : (secondOrderDefectGraph R).IsClique (C : Set W)) :
    ∃ x ∈ C, (triangleFreeNeighbors R x).card ≤ e + 3 - C.card := by
  classical
  have hsafe := commonNeighborIndependent_of_secondOrderDefect_isClique
    R hfree C hclique
  let O := C ∩ C.biUnion (fun x => R.neighborFinset x)
  have hOeven : Even O.card := hsafe.even_card_overlap R C
  have hOsub : O ⊆ C := Finset.inter_subset_left
  have hOlt : O.card < C.card := by
    have hOle := Finset.card_le_card hOsub
    by_contra hnot
    have heq : O.card = C.card := by omega
    obtain ⟨a, ha⟩ := hOeven
    obtain ⟨b, hb⟩ := hCodd
    omega
  have hdiffPos : 0 < (C \ O).card := by
    rw [Finset.card_sdiff_of_subset hOsub]
    omega
  obtain ⟨x, hxDiff⟩ := Finset.card_pos.mp hdiffPos
  have hxC : x ∈ C := (Finset.mem_sdiff.mp hxDiff).1
  have hxO : x ∉ O := (Finset.mem_sdiff.mp hxDiff).2
  have hxNoAdj : ∀ y ∈ C, ¬ R.Adj x y := by
    intro y hyC hxy
    apply hxO
    refine Finset.mem_inter.mpr ⟨hxC, ?_⟩
    rw [Finset.mem_biUnion]
    exact ⟨y, hyC, (R.mem_neighborFinset y x).mpr hxy.symm⟩
  have hsub : C.erase x ⊆ antipodalNeighbors R x := by
    intro y hy
    have hyC := Finset.mem_of_mem_erase hy
    have hyx : y ≠ x := Finset.ne_of_mem_erase hy
    have hD := hclique hxC hyC hyx.symm
    change (antipodalGraph R ⊔ triangleFreeEdgeGraph R).Adj x y at hD
    rcases hD with hanti | htf
    · exact hanti
    · exact (hxNoAdj y hyC ((mem_triangleFreeNeighbors R x y).mp htf).1).elim
  have hsumAT : (antipodalNeighbors R x).card +
      (triangleFreeNeighbors R x).card = e + 2 := by
    calc
      (antipodalNeighbors R x).card +
          (triangleFreeNeighbors R x).card =
          ((secondOrderDefectGraph R).neighborFinset x).card := by
            rw [secondOrderDefectGraph_neighborFinset,
              Finset.card_union_of_disjoint
                (disjoint_antipodal_triangleFreeNeighbors R x)]
      _ = (secondOrderDefectGraph R).degree x :=
        (secondOrderDefectGraph R).card_neighborFinset_eq_degree x
      _ = e + 2 := secondOrderDefectGraph_degree_eq_excess_add_two
        R hfree hreg hcard x
  have hErase : (C.erase x).card = C.card - 1 :=
    Finset.card_erase_of_mem hxC
  have hle := Finset.card_le_card hsub
  rw [hErase] at hle
  have hCpos : 0 < C.card := Finset.card_pos.mpr ⟨x, hxC⟩
  have hsum : C.card + (triangleFreeNeighbors R x).card ≤ e + 3 := by
    omega
  refine ⟨x, hxC, ?_⟩
  exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hsum)

/-- A six-regular `C₄`-free graph of order forty in which every edge is
triangle-free has no five-vertex clique in its second-order defect graph. -/
theorem no_five_secondOrderDefect_clique_of_all_edges_triangleFree
    {W : Type*} [Fintype W] [DecidableEq W]
    (R : SimpleGraph W) [DecidableRel R.Adj]
    [DecidableRel (antipodalGraph R).Adj]
    [DecidableRel (triangleFreeEdgeGraph R).Adj]
    (hfree : ¬ containsC4 W R)
    (hreg : ∀ x, R.degree x = 6)
    (hcard : Fintype.card W = 40)
    (hTF : ∀ x, triangleFreeNeighbors R x = R.neighborFinset x)
    (C : Finset W) (hCcard : C.card = 5)
    (hclique : (secondOrderDefectGraph R).IsClique (C : Set W)) :
    False := by
  classical
  have hsafe := commonNeighborIndependent_of_secondOrderDefect_isClique
    R hfree C hclique
  let O := C ∩ C.biUnion (fun x => R.neighborFinset x)
  have hOeven : Even O.card := by
    exact hsafe.even_card_overlap R C
  have hOsub : O ⊆ C := Finset.inter_subset_left
  have hOle : O.card ≤ 4 := by
    have hle := Finset.card_le_card hOsub
    rw [hCcard] at hle
    obtain ⟨k, hk⟩ := hOeven
    omega
  have hdiffPos : 0 < (C \ O).card := by
    rw [Finset.card_sdiff_of_subset hOsub]
    omega
  obtain ⟨x, hxDiff⟩ := Finset.card_pos.mp hdiffPos
  have hxC : x ∈ C := (Finset.mem_sdiff.mp hxDiff).1
  have hxO : x ∉ O := (Finset.mem_sdiff.mp hxDiff).2
  have hxNoAdj : ∀ y ∈ C, ¬ R.Adj x y := by
    intro y hyC hxy
    apply hxO
    refine Finset.mem_inter.mpr ⟨hxC, ?_⟩
    rw [Finset.mem_biUnion]
    exact ⟨y, hyC, (R.mem_neighborFinset y x).mpr hxy.symm⟩
  have hsub : C.erase x ⊆ antipodalNeighbors R x := by
    intro y hy
    have hyC := Finset.mem_of_mem_erase hy
    have hyx : y ≠ x := Finset.ne_of_mem_erase hy
    have hD := hclique hxC hyC hyx.symm
    change (antipodalGraph R ⊔ triangleFreeEdgeGraph R).Adj x y at hD
    rcases hD with hanti | htf
    · exact hanti
    · have hxy : R.Adj x y :=
        ((mem_triangleFreeNeighbors R x y).mp htf).1
      exact (hxNoAdj y hyC hxy).elim
  have hAntiDeg : (antipodalGraph R).degree x = 3 := by
    have h := antipodalGraph_degree_eq_excess_add_two_sub_triangleFree
      R hfree (d := 6) (e := 7) (by omega) hreg (by omega) x
    rw [hTF x, R.card_neighborFinset_eq_degree, hreg x] at h
    norm_num at h ⊢
    exact h
  have hAntiCard : (antipodalNeighbors R x).card = 3 := by
    rw [← antipodalGraph_neighborFinset R x,
      (antipodalGraph R).card_neighborFinset_eq_degree, hAntiDeg]
  have hfour : (C.erase x).card = 4 := by
    rw [Finset.card_erase_of_mem hxC, hCcard]
  have := Finset.card_le_card hsub
  rw [hfour, hAntiCard] at this
  omega

/-- **Outer triangles are forced.**  In the unique-high order-49 sector,
the induced forty-vertex outer graph cannot be triangle-free. -/
theorem orderFortyNine_outerGraph_has_triangleFreeEdge_failure
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (hunique : ∀ {w : V}, G.degree w = 8 → w = v) :
    ¬ ∀ x, triangleFreeNeighbors (squareOrderOuterGraph G v) x =
      (squareOrderOuterGraph G v).neighborFinset x := by
  intro hTF
  let R := squareOrderOuterGraph G v
  letI : DecidableRel (antipodalGraph R).Adj := Classical.decRel _
  letI : DecidableRel (triangleFreeEdgeGraph R).Adj := Classical.decRel _
  have hstructure := squareOrder_degree_succ_highRoot_structure
    G hfree (by omega : 2 ≤ 7) hmin (by simpa using hcard) hv
  have houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7 := by
    intro a ha
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin hcard a with ha7 | ha8
    · exact ha7
    · have hav : a = v := hunique ha8
      rw [secondLayer] at ha
      rcases Finset.mem_biUnion.mp ha with ⟨s, _, has⟩
      exact ((Finset.mem_sdiff.mp has).2 (by simp [hav])).elim
  have hRreg : ∀ x, R.degree x = 6 := by
    simpa [R] using squareOrderOuterGraph_regular
      G hfree (by omega : 2 ≤ 7) (by simpa using hcard) hv
        hstructure.2.1 hstructure.2.2 houterDegree
  have hRcard : Fintype.card {x : V // x ∈ secondLayer G v} = 40 := by
    simpa using orderFortyNine_card_secondLayer_degreeEight_eq_forty
      G hfree hmin hcard hv
  have hNnonempty : (G.neighborFinset v).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hz : (G.neighborFinset v).card = 0 := by rw [hempty]; simp
    rw [G.card_neighborFinset_eq_degree, hv] at hz
    omega
  let s : {z : V // z ∈ G.neighborSet v} :=
    ⟨Classical.choose hNnonempty,
      (G.mem_neighborFinset v _).mp
        (Classical.choose_spec hNnonempty)⟩
  let C := orderFortyNineOuterBranch G v s
  have hCcard : C.card = 5 :=
    card_orderFortyNineOuterBranch_eq_five G hfree hmin hcard hv s
  have hCclique : (secondOrderDefectGraph R).IsClique (C : Set _) := by
    intro a ha b hb hab
    exact orderFortyNine_outerDefect_adj_of_sameBranch G hfree s a b
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hab
  exact no_five_secondOrderDefect_clique_of_all_edges_triangleFree
    R (squareOrderOuterGraph_not_containsC4 G hfree) hRreg hRcard
      (by simpa [R] using hTF) C hCcard hCclique

/-- Graph-facing form: the induced outer graph contains a triangle. -/
theorem orderFortyNine_outerGraph_contains_triangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (hunique : ∀ {w : V}, G.degree w = 8 → w = v) :
    ∃ x y z : {a : V // a ∈ secondLayer G v},
      (squareOrderOuterGraph G v).Adj x y ∧
      (squareOrderOuterGraph G v).Adj y z ∧
      (squareOrderOuterGraph G v).Adj z x := by
  let R := squareOrderOuterGraph G v
  by_contra hno
  push Not at hno
  apply orderFortyNine_outerGraph_has_triangleFreeEdge_failure
    G hfree hmin hcard hv hunique
  intro x
  ext y
  constructor
  · intro hy
    exact (R.mem_neighborFinset x y).mpr
      ((mem_triangleFreeNeighbors R x y).mp hy).1
  · intro hy
    apply (mem_triangleFreeNeighbors R x y).mpr
    refine ⟨(R.mem_neighborFinset x y).mp hy, ?_⟩
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    rcases Finset.mem_inter.mp hz with ⟨hzx, hzy⟩
    exact hno x y z (R.mem_neighborFinset x y |>.mp hy)
      (R.mem_neighborFinset y z |>.mp hzy)
      (R.mem_neighborFinset x z |>.mp hzx).symm

end

end Erdos85
