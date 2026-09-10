import Proofs.Erdos85DefectSurvivorAntipodal
import Proofs.Erdos85FiniteSparseDefectOverlap
import Proofs.Erdos85OrderFortyNineLocalEdgePartition
import Proofs.Erdos85OrderFortyNineHighIncidenceCensus

/-! Actual q7 local ledger, combining the existing high/all-low triangle
partition with the surviving defect-neighbor identity. -/
namespace Erdos85
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Surviving defect-neighbor count plus one is high incidence plus twice
the actual all-low local triangle count. No profile or triangle count is assumed. -/
theorem orderFortyNine_survivors_add_one_eq_high_add_two_lowLow
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x : V} (hx : G.degree x = 7) :
    ((secondOrderDefectGraph G).neighborFinset x \ G.neighborFinset x).card + 1 =
      (G.neighborFinset x ∩ orderFortyNineHighVertices G).card +
        2 * orderFortyNineLowLowLocalEdgeCount G x := by
  have hcover : ∀ {u v}, G.Adj u v → G.degree u = 7 ∨ G.degree v = 7 := by
    intro u v huv
    rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin hcard u with hu | hu
    · exact Or.inl hu
    · exact Or.inr (orderFortyNine_neighbor_degree_seven_of_degreeEight
        G hfree hmin hcard hu huv)
  have hledger := squareOrder_low_survivors_add_highIncidence_add_one_eq_two_mul_localEdges
    G hfree (d := 7) (by omega) hmin hcover (by simpa using hcard) hx
  have hinc : squareOrderHighIncidenceCount G 7 x =
      (G.neighborFinset x ∩ orderFortyNineHighVertices G).card := by rfl
  rw [hinc] at hledger
  have hpartition := orderFortyNine_high_add_lowLow_eq_localTriangleEdges
    G hfree hmin hcard hx
  omega

/-- Empty-support vertices with one all-low triangle leave one survivor. -/
theorem orderFortyNine_survivors_eq_one_of_high_zero_lowLow_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x : V} (hx : G.degree x = 7)
    (hhigh : (G.neighborFinset x ∩ orderFortyNineHighVertices G).card = 0)
    (hlow : orderFortyNineLowLowLocalEdgeCount G x = 1) :
    ((secondOrderDefectGraph G).neighborFinset x \ G.neighborFinset x).card = 1 := by
  have h := orderFortyNine_survivors_add_one_eq_high_add_two_lowLow G hfree hmin hcard hx
  omega

/-- Vertices with positive support and no all-low triangle have support minus
one surviving defect neighbors. -/
theorem orderFortyNine_survivors_add_one_eq_high_of_lowLow_zero
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x : V} (hx : G.degree x = 7)
    (hlow : orderFortyNineLowLowLocalEdgeCount G x = 0) :
    ((secondOrderDefectGraph G).neighborFinset x \ G.neighborFinset x).card + 1 =
      (G.neighborFinset x ∩ orderFortyNineHighVertices G).card := by
  simpa [hlow] using
    orderFortyNine_survivors_add_one_eq_high_add_two_lowLow G hfree hmin hcard hx
/-- Equality in the empty-support lower bound forces every local triangle
count. The sum here is triangle incidence, hence three times the global
all-low triangle count when that separate counting identity is supplied. -/
theorem orderFortyNine_lowLow_eq_indicator_of_minimal_sum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hsum : (∑ x ∈ orderFortyNineLowVertices G, orderFortyNineLowLowLocalEdgeCount G x) =
      ((orderFortyNineLowVertices G).filter fun x =>
        (G.neighborFinset x ∩ orderFortyNineHighVertices G).card = 0).card)
    {x : V} (hx : G.degree x = 7) :
    orderFortyNineLowLowLocalEdgeCount G x =
      if (G.neighborFinset x ∩ orderFortyNineHighVertices G).card = 0 then 1 else 0 := by
  classical
  let f : V → ℕ := fun v =>
    if (G.neighborFinset v ∩ orderFortyNineHighVertices G).card = 0 then 1 else 0
  have hbase : ∀ v ∈ orderFortyNineLowVertices G,
      f v ≤ orderFortyNineLowLowLocalEdgeCount G v := by
    intro v hv
    have hvlow : G.degree v = 7 := by
      rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin hcard v with h | h
      · exact h
      · have hn := (Finset.mem_sdiff.mp hv).2
        exact (hn (by simp [orderFortyNineHighVertices, h])).elim
    dsimp [f]
    split_ifs with hzero
    · have h := orderFortyNine_lowLowLocalEdgeCount_pos_of_no_high
        G hfree hmin hcard hvlow hzero
      omega
    · omega
  have hsumf : (∑ v ∈ orderFortyNineLowVertices G, f v) =
      ((orderFortyNineLowVertices G).filter fun v =>
        (G.neighborFinset v ∩ orderFortyNineHighVertices G).card = 0).card := by
    simp [f]
  have hxmem : x ∈ orderFortyNineLowVertices G := by
    simp [orderFortyNineLowVertices, orderFortyNineHighVertices, hx]
  change orderFortyNineLowLowLocalEdgeCount G x = f x
  by_contra hne
  have hlt : f x < orderFortyNineLowLowLocalEdgeCount G x := by
    have h := hbase x hxmem
    omega
  have hstrict := Finset.sum_lt_sum hbase ⟨x, hxmem, hlt⟩
  omega
/-- At minimum total low-triangle incidence, only triple-support low vertices
can contribute to the mixed overlap. This is an actual q7 graph bound. -/
theorem orderFortyNine_sparse_overlap_of_minimal_sum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hsum : (∑ x ∈ orderFortyNineLowVertices G, orderFortyNineLowLowLocalEdgeCount G x) =
      orderFortyNineHighIncidenceCount G 0) :
    Matrix.trace ((secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ *
      (secondOrderDefectGraph G).adjMatrix ℤ) ≤
      2 * (orderFortyNineHighIncidenceCount G 3 : ℤ) ∧
    (orderFortyNineHighIncidenceCount G 3 ≤ 2 →
      ¬ Int.ModEq 5 (Matrix.trace ((secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ)) 1) := by
  classical
  let E := (orderFortyNineLowVertices G).filter fun x =>
    (G.neighborFinset x ∩ orderFortyNineHighVertices G).card = 3
  have hlow {v : V} (hv : v ∈ orderFortyNineLowVertices G) : G.degree v = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin hcard v with h | h
    · exact h
    · exact ((Finset.mem_sdiff.mp hv).2 (by simp [orderFortyNineHighVertices, h])).elim
  have hsparse : ∀ v, v ∉ E →
      ((secondOrderDefectGraph G).neighborFinset v \ G.neighborFinset v).card ≤ 1 := by
    intro v hv
    rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin hcard v with h7 | h8
    · have hm : v ∈ orderFortyNineLowVertices G := by
        simp [orderFortyNineLowVertices, orderFortyNineHighVertices, h7]
      have hn3 : (G.neighborFinset v ∩ orderFortyNineHighVertices G).card ≠ 3 := by
        intro h3
        exact hv (Finset.mem_filter.mpr ⟨hm, h3⟩)
      have hbound := orderFortyNine_highNeighborCount_le_three G hfree hmin hcard h7
      have ht := orderFortyNine_lowLow_eq_indicator_of_minimal_sum G hfree hmin hcard hsum h7
      have hl := orderFortyNine_survivors_add_one_eq_high_add_two_lowLow G hfree hmin hcard h7
      split_ifs at ht <;> omega
    · have hz := (orderFortyNine_degreeEight_defectDegree_and_neighborExcess_zero
        G hfree hmin hcard h8).1
      have hle := Finset.card_le_card
        (Finset.sdiff_subset : (secondOrderDefectGraph G).neighborFinset v \ G.neighborFinset v ⊆
          (secondOrderDefectGraph G).neighborFinset v)
      rw [(secondOrderDefectGraph G).card_neighborFinset_eq_degree, hz] at hle
      omega
  have hexception : ∀ v ∈ E,
      ((secondOrderDefectGraph G).neighborFinset v \ G.neighborFinset v).card ≤ 2 := by
    intro v hv
    obtain ⟨hm, h3⟩ := Finset.mem_filter.mp hv
    have h7 := hlow hm
    have ht := orderFortyNine_lowLow_eq_indicator_of_minimal_sum G hfree hmin hcard hsum h7
    have hl := orderFortyNine_survivors_add_one_eq_high_add_two_lowLow G hfree hmin hcard h7
    rw [h3] at ht hl
    norm_num at ht
    omega
  refine ⟨finite_sparse_defect_overlap_trace_le G hfree E hsparse hexception, ?_⟩
  intro hc
  exact finite_sparse_defect_overlap_trace_not_mod_five_one G hfree E hsparse hexception hc
end Erdos85
