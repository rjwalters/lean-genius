import Proofs.Erdos85OrderFortyNineHighPartnerBound
import Proofs.Erdos85OrderFortyNineLocalEdgePartition

/-!
# Census of low vertices by high incidence at order 49

The high vertices form a pairwise-balanced design on the low vertices, with
block sizes at most three.  This file packages the resulting four-bin census
and specializes it to the previously uncovered `h = 9` stratum.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A finite natural-valued function bounded by three is exactly accounted
for by its four fibers, both in cardinality and in its first two moments. -/
theorem finset_census_le_three
    {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℕ) (hle : ∀ x ∈ S, f x ≤ 3) :
    let n0 := (S.filter fun x => f x = 0).card
    let n1 := (S.filter fun x => f x = 1).card
    let n2 := (S.filter fun x => f x = 2).card
    let n3 := (S.filter fun x => f x = 3).card
    S.card = n0 + n1 + n2 + n3 ∧
      (∑ x ∈ S, f x) = n1 + 2 * n2 + 3 * n3 ∧
      (∑ x ∈ S, (f x) ^ 2) = n1 + 4 * n2 + 9 * n3 := by
  dsimp
  have hpoint (x : α) (hx : x ∈ S) :
      (1 : ℕ) =
          (if f x = 0 then 1 else 0) +
          (if f x = 1 then 1 else 0) +
          (if f x = 2 then 1 else 0) +
          (if f x = 3 then 1 else 0) ∧
        f x =
          (if f x = 1 then 1 else 0) +
          2 * (if f x = 2 then 1 else 0) +
          3 * (if f x = 3 then 1 else 0) ∧
        (f x) ^ 2 =
          (if f x = 1 then 1 else 0) +
          4 * (if f x = 2 then 1 else 0) +
          9 * (if f x = 3 then 1 else 0) := by
    have hf := hle x hx
    interval_cases hfx : f x <;> simp [hfx]
  constructor
  · rw [Finset.card_eq_sum_ones]
    calc
      (∑ _x ∈ S, 1) = ∑ x ∈ S,
          ((if f x = 0 then 1 else 0) +
          (if f x = 1 then 1 else 0) +
          (if f x = 2 then 1 else 0) +
          (if f x = 3 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact (hpoint x hx).1
      _ = (S.filter fun x => f x = 0).card +
          (S.filter fun x => f x = 1).card +
          (S.filter fun x => f x = 2).card +
          (S.filter fun x => f x = 3).card := by
        simp_rw [Finset.sum_add_distrib]
        rw [Finset.card_filter, Finset.card_filter,
          Finset.card_filter, Finset.card_filter]
  constructor
  · calc
      (∑ x ∈ S, f x) = ∑ x ∈ S,
          ((if f x = 1 then 1 else 0) +
          2 * (if f x = 2 then 1 else 0) +
          3 * (if f x = 3 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact (hpoint x hx).2.1
      _ = (S.filter fun x => f x = 1).card +
          2 * (S.filter fun x => f x = 2).card +
          3 * (S.filter fun x => f x = 3).card := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
  · calc
      (∑ x ∈ S, (f x) ^ 2) = ∑ x ∈ S,
          ((if f x = 1 then 1 else 0) +
          4 * (if f x = 2 then 1 else 0) +
          9 * (if f x = 3 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact (hpoint x hx).2.2
      _ = (S.filter fun x => f x = 1).card +
          4 * (S.filter fun x => f x = 2).card +
          9 * (S.filter fun x => f x = 3).card := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]

/-- The degree-seven sector at order 49. -/
def orderFortyNineLowVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  (Finset.univ : Finset V) \ orderFortyNineHighVertices G

/-- Number of low vertices incident with exactly `i` high vertices. -/
def orderFortyNineHighIncidenceCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i : ℕ) : ℕ :=
  ((orderFortyNineLowVertices G).filter fun x =>
    (G.neighborFinset x ∩ orderFortyNineHighVertices G).card = i).card

/-- Number of low vertices of a specified second-order defect degree. -/
def orderFortyNineLowDefectDegreeCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] (j : ℕ) : ℕ :=
  ((orderFortyNineLowVertices G).filter fun x =>
    (secondOrderDefectGraph G).degree x = j).card

/-- The four high-incidence bins on the low sector satisfy the exact size,
first-moment, and second-moment equations. -/
theorem orderFortyNine_highIncidence_census
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) :
    orderFortyNineHighIncidenceCount G 0 +
        orderFortyNineHighIncidenceCount G 1 +
        orderFortyNineHighIncidenceCount G 2 +
        orderFortyNineHighIncidenceCount G 3 =
      49 - (orderFortyNineHighVertices G).card ∧
    orderFortyNineHighIncidenceCount G 1 +
        2 * orderFortyNineHighIncidenceCount G 2 +
        3 * orderFortyNineHighIncidenceCount G 3 =
      8 * (orderFortyNineHighVertices G).card ∧
    orderFortyNineHighIncidenceCount G 1 +
        4 * orderFortyNineHighIncidenceCount G 2 +
        9 * orderFortyNineHighIncidenceCount G 3 =
      (orderFortyNineHighVertices G).card *
        ((orderFortyNineHighVertices G).card + 7) := by
  let H := orderFortyNineHighVertices G
  let L := orderFortyNineLowVertices G
  let k : V → ℕ := fun x => (G.neighborFinset x ∩ H).card
  have hk : ∀ x ∈ L, k x ≤ 3 := by
    intro x hx
    have hxnot : x ∉ H := (Finset.mem_sdiff.mp hx).2
    have hxdeg : G.degree x = 7 := by
      rcases orderFortyNine_degree_eq_seven_or_eight
          G hfree hmin hcard x with hx7 | hx8
      · exact hx7
      · exact (hxnot (by simp [H, orderFortyNineHighVertices, hx8])).elim
    exact orderFortyNine_highNeighborCount_le_three
      G hfree hmin hcard hxdeg
  let n0 := (L.filter fun x => k x = 0).card
  let n1 := (L.filter fun x => k x = 1).card
  let n2 := (L.filter fun x => k x = 2).card
  let n3 := (L.filter fun x => k x = 3).card
  change n0 + n1 + n2 + n3 = 49 - H.card ∧
      n1 + 2 * n2 + 3 * n3 = 8 * H.card ∧
      n1 + 4 * n2 + 9 * n3 = H.card * (H.card + 7)
  have hcensus := finset_census_le_three L k hk
  change L.card = n0 + n1 + n2 + n3 ∧
      (∑ x ∈ L, k x) = n1 + 2 * n2 + 3 * n3 ∧
      (∑ x ∈ L, (k x) ^ 2) = n1 + 4 * n2 + 9 * n3 at hcensus
  have hLcard : L.card = 49 - H.card := by
    dsimp [L, orderFortyNineLowVertices]
    rw [Finset.card_sdiff, Finset.card_univ, hcard]
    simp [H]
  have hfirst : (∑ x ∈ L, k x) = 8 * H.card := by
    simpa [H, L, k, orderFortyNineLowVertices] using
      orderFortyNine_sum_low_highNeighborCount_eq G hfree hmin hcard
  have hsecond : (∑ x ∈ L, (k x) ^ 2) = H.card * (H.card + 7) := by
    simpa [H, L, k, orderFortyNineLowVertices] using
      orderFortyNine_sum_low_highNeighborCount_sq_eq G hfree hmin hcard
  refine ⟨?_, ?_, ?_⟩
  · rw [← hLcard]
    exact hcensus.1.symm
  · rw [← hfirst]
    exact hcensus.2.1.symm
  · rw [← hsecond]
    exact hcensus.2.2.symm

/-- At `h = 9` the global PBD moments leave exactly five possible incidence
profiles.  In particular, almost every low vertex meets two or three highs. -/
theorem orderFortyNine_highIncidence_profile_of_nine_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9) :
    let n := orderFortyNineHighIncidenceCount G
    (n 0 = 4 ∧ n 1 = 0 ∧ n 2 = 36 ∧ n 3 = 0) ∨
    (n 0 = 3 ∧ n 1 = 3 ∧ n 2 = 33 ∧ n 3 = 1) ∨
    (n 0 = 2 ∧ n 1 = 6 ∧ n 2 = 30 ∧ n 3 = 2) ∨
    (n 0 = 1 ∧ n 1 = 9 ∧ n 2 = 27 ∧ n 3 = 3) ∨
    (n 0 = 0 ∧ n 1 = 12 ∧ n 2 = 24 ∧ n 3 = 4) := by
  dsimp only
  let n0 := orderFortyNineHighIncidenceCount G 0
  let n1 := orderFortyNineHighIncidenceCount G 1
  let n2 := orderFortyNineHighIncidenceCount G 2
  let n3 := orderFortyNineHighIncidenceCount G 3
  change (n0 = 4 ∧ n1 = 0 ∧ n2 = 36 ∧ n3 = 0) ∨
    (n0 = 3 ∧ n1 = 3 ∧ n2 = 33 ∧ n3 = 1) ∨
    (n0 = 2 ∧ n1 = 6 ∧ n2 = 30 ∧ n3 = 2) ∨
    (n0 = 1 ∧ n1 = 9 ∧ n2 = 27 ∧ n3 = 3) ∨
    (n0 = 0 ∧ n1 = 12 ∧ n2 = 24 ∧ n3 = 4)
  have hcensus := orderFortyNine_highIncidence_census
    G hfree hmin hcard
  change n0 + n1 + n2 + n3 =
      49 - (orderFortyNineHighVertices G).card ∧
    n1 + 2 * n2 + 3 * n3 =
      8 * (orderFortyNineHighVertices G).card ∧
    n1 + 4 * n2 + 9 * n3 =
      (orderFortyNineHighVertices G).card *
        ((orderFortyNineHighVertices G).card + 7) at hcensus
  rw [hHigh] at hcensus
  have hn3 : n3 ≤ 4 := by omega
  interval_cases n3 <;> omega

/-- Around a fixed high vertex, the high-incidence counts of its eight
neighbors sum to `h + 7`.  The diagonal high contributes eight, while each
other high contributes its unique common neighbor with the root. -/
theorem orderFortyNine_sum_highIncidence_over_highNeighborhood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8) :
    (∑ x ∈ G.neighborFinset v,
      (G.neighborFinset x ∩ orderFortyNineHighVertices G).card) =
      (orderFortyNineHighVertices G).card + 7 := by
  let H := orderFortyNineHighVertices G
  have hvH : v ∈ H := by simp [H, orderFortyNineHighVertices, hv]
  change (∑ x ∈ G.neighborFinset v,
      (G.neighborFinset x ∩ H).card) = H.card + 7
  have hcount (x : V) :
      (G.neighborFinset x ∩ H).card =
        ∑ w ∈ H, if G.Adj x w then 1 else 0 := by
    calc
      (G.neighborFinset x ∩ H).card =
          (H.filter fun w => G.Adj x w).card := by
        congr 1
        ext w
        simp [SimpleGraph.mem_neighborFinset, and_comm]
      _ = ∑ w ∈ H, if G.Adj x w then 1 else 0 := by
        rw [Finset.card_filter]
  simp_rw [hcount]
  rw [Finset.sum_comm]
  have hterm : ∀ w ∈ H,
      (∑ x ∈ G.neighborFinset v, if G.Adj x w then 1 else 0) =
        if w = v then 8 else 1 := by
    intro w hw
    have hw8 : G.degree w = 8 := (Finset.mem_filter.mp hw).2
    have hsumCommon :
        (∑ x ∈ G.neighborFinset v, if G.Adj x w then 1 else 0) =
          (G.neighborFinset v ∩ G.neighborFinset w).card := by
      rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
      apply Finset.sum_congr
      · ext x
        simp [SimpleGraph.mem_neighborFinset, G.adj_comm]
      · intro x hx
        have hxw : G.Adj x w := by
          have := (Finset.mem_inter.mp hx).2
          simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using this
        simp [hxw]
    rw [hsumCommon]
    by_cases hwv : w = v
    · subst w
      simp [hv]
    · rw [if_neg hwv]
      exact orderFortyNine_card_common_degreeEight_eq_one
        G hfree hmin hcard hv hw8 (fun h => hwv h.symm)
  calc
    (∑ w ∈ H, ∑ x ∈ G.neighborFinset v,
        if G.Adj x w then 1 else 0) =
        ∑ w ∈ H, if w = v then 8 else 1 := by
      apply Finset.sum_congr rfl
      intro w hw
      exact hterm w hw
    _ = H.card + 7 := by
      calc
        (∑ w ∈ H, if w = v then 8 else 1) =
            (∑ w ∈ H.erase v, if w = v then 8 else 1) + 8 := by
          rw [← Finset.sum_erase_add _ _ hvH]
          simp
        _ = (∑ _w ∈ H.erase v, 1) + 8 := by
          congr 1
          apply Finset.sum_congr rfl
          intro w hw
          simp [(Finset.mem_erase.mp hw).1]
        _ = H.card + 7 := by
          have hsumones : (∑ _w ∈ H.erase v, 1) = (H.erase v).card := by
            simp
          rw [hsumones, Finset.card_erase_of_mem hvH]
          have hpos : 0 < H.card := Finset.card_pos.mpr ⟨v, hvH⟩
          omega

/-- At `h = 9`, every high neighborhood contains equally many `k=1` and
`k=3` lows; the remaining neighbors have `k=2`.  Thus its local PBD profile
is one of five matching-compatible possibilities. -/
theorem orderFortyNine_highNeighborhood_profile_of_nine_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    {v : V} (hv : G.degree v = 8) :
    let a := fun i => ((G.neighborFinset v).filter fun x =>
      (G.neighborFinset x ∩ orderFortyNineHighVertices G).card = i).card
    (a 1 = 0 ∧ a 2 = 8 ∧ a 3 = 0) ∨
    (a 1 = 1 ∧ a 2 = 6 ∧ a 3 = 1) ∨
    (a 1 = 2 ∧ a 2 = 4 ∧ a 3 = 2) ∨
    (a 1 = 3 ∧ a 2 = 2 ∧ a 3 = 3) ∨
    (a 1 = 4 ∧ a 2 = 0 ∧ a 3 = 4) := by
  dsimp only
  let k : V → ℕ := fun x =>
    (G.neighborFinset x ∩ orderFortyNineHighVertices G).card
  let a1 := ((G.neighborFinset v).filter fun x => k x = 1).card
  let a2 := ((G.neighborFinset v).filter fun x => k x = 2).card
  let a3 := ((G.neighborFinset v).filter fun x => k x = 3).card
  change (a1 = 0 ∧ a2 = 8 ∧ a3 = 0) ∨
    (a1 = 1 ∧ a2 = 6 ∧ a3 = 1) ∨
    (a1 = 2 ∧ a2 = 4 ∧ a3 = 2) ∨
    (a1 = 3 ∧ a2 = 2 ∧ a3 = 3) ∨
    (a1 = 4 ∧ a2 = 0 ∧ a3 = 4)
  have hk : ∀ x ∈ G.neighborFinset v, k x ≤ 3 := by
    intro x hx
    have hxAdj : G.Adj v x := (G.mem_neighborFinset v x).mp hx
    have hxdeg := orderFortyNine_neighbor_degree_seven_of_degreeEight
      G hfree hmin hcard hv hxAdj
    exact orderFortyNine_highNeighborCount_le_three
      G hfree hmin hcard hxdeg
  have hcensus := finset_census_le_three (G.neighborFinset v) k hk
  let a0 := ((G.neighborFinset v).filter fun x => k x = 0).card
  change G.degree v = a0 + a1 + a2 + a3 ∧
      (∑ x ∈ G.neighborFinset v, k x) = a1 + 2 * a2 + 3 * a3 ∧
      (∑ x ∈ G.neighborFinset v, (k x) ^ 2) =
        a1 + 4 * a2 + 9 * a3 at hcensus
  have ha0 : a0 = 0 := by
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxmem := (Finset.mem_filter.mp hx).1
    have hxAdj : G.Adj v x := (G.mem_neighborFinset v x).mp hxmem
    have hvx : v ∈ G.neighborFinset x ∩ orderFortyNineHighVertices G := by
      simp [SimpleGraph.mem_neighborFinset, hxAdj.symm,
        orderFortyNineHighVertices, hv]
    have hkpos : 0 < k x := Finset.card_pos.mpr ⟨v, hvx⟩
    exact hkpos.ne' (Finset.mem_filter.mp hx).2
  have hsum := orderFortyNine_sum_highIncidence_over_highNeighborhood
    G hfree hmin hcard hv
  change (∑ x ∈ G.neighborFinset v, k x) =
    (orderFortyNineHighVertices G).card + 7 at hsum
  rw [hHigh] at hsum
  have ha3 : a3 ≤ 4 := by omega
  interval_cases a3 <;> omega

/-- The foreign-high blocks carried by the two endpoints of a local matching
edge at a high root are disjoint.  Otherwise the root and a repeated foreign
high would be two common neighbors of the matched low endpoints. -/
theorem orderFortyNine_disjoint_otherHighNeighbors_of_highLocalEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {v x y : V}
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hxy : G.Adj x y) :
    Disjoint
      ((G.neighborFinset x ∩ orderFortyNineHighVertices G).erase v)
      ((G.neighborFinset y ∩ orderFortyNineHighVertices G).erase v) := by
  rw [Finset.disjoint_left]
  intro w hwx hwy
  have hwx' := Finset.mem_erase.mp hwx
  have hwy' := Finset.mem_erase.mp hwy
  have hvw : v ≠ w := fun h => hwx'.1 h.symm
  have hwAdjX : G.Adj w x := by
    have := (Finset.mem_inter.mp hwx'.2).1
    simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using this
  have hwAdjY : G.Adj w y := by
    have := (Finset.mem_inter.mp hwy'.2).1
    simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using this
  exact hfree (containsC4_of_two_common (G.ne_of_adj hxy) hvw
    hvx hvy hwAdjX hwAdjY)

/-- A low vertex incident with three highs has exactly one edge which lies in
no triangle.  Its three high incidences exhaust the local triangle budget. -/
theorem orderFortyNine_triangleFreeEdgeGraph_degree_eq_one_of_three_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {x : V} (hx : G.degree x = 7)
    (hk : (G.neighborFinset x ∩
      orderFortyNineHighVertices G).card = 3) :
    (triangleFreeEdgeGraph G).degree x = 1 := by
  have hr := orderFortyNine_lowLowLocalEdgeCount_eq_zero_of_three_high
    G hfree hmin hcard hx hk
  have hlocal := orderFortyNine_high_add_lowLow_eq_localTriangleEdges
    G hfree hmin hcard hx
  rw [hk, hr] at hlocal
  have htriangleFree := card_triangleFreeNeighbors_add_two_mul_localEdges
    G hfree x
  rw [← hlocal, hx] at htriangleFree
  have hcardTF : (triangleFreeNeighbors G x).card = 1 := by omega
  rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
    triangleFreeEdgeGraph_neighborFinset]
  exact hcardTF

/-- At order 49, neighbor degree excess above seven is exactly the number of
high neighbors. -/
theorem orderFortyNine_neighborDegreeExcess_eq_highNeighborCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) (x : V) :
    neighborDegreeExcess G 7 x =
      (G.neighborFinset x ∩ orderFortyNineHighVertices G).card := by
  rw [neighborDegreeExcess_eq_sum_neighborFinset]
  have hterm : ∀ y ∈ G.neighborFinset x,
      G.degree y - 7 = if G.degree y = 8 then 1 else 0 := by
    intro y _hy
    rcases orderFortyNine_degree_eq_seven_or_eight
        G hfree hmin hcard y with hy7 | hy8
    · simp [hy7]
    · simp [hy8]
  calc
    (∑ y ∈ G.neighborFinset x, (G.degree y - 7)) =
        ∑ y ∈ G.neighborFinset x, if G.degree y = 8 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hterm y hy
    _ = ((G.neighborFinset x).filter fun y => G.degree y = 8).card := by
      rw [Finset.card_filter]
    _ = (G.neighborFinset x ∩ orderFortyNineHighVertices G).card := by
      congr 1
      ext y
      simp [orderFortyNineHighVertices, and_comm]

/-- **Defect/PBD conservation law.**  A low vertex of high-incidence `k`
has defect degree `6-k`. -/
theorem orderFortyNine_defectDegree_add_highNeighborCount_eq_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {x : V} (hx : G.degree x = 7) :
    (secondOrderDefectGraph G).degree x +
      (G.neighborFinset x ∩ orderFortyNineHighVertices G).card = 6 := by
  rw [← orderFortyNine_neighborDegreeExcess_eq_highNeighborCount
    G hfree hmin hcard x]
  exact orderFortyNine_degreeSeven_local_budget G hfree hmin hcard hx

/-- The `k=i` incidence fiber is exactly the low defect-degree `6-i` fiber. -/
theorem orderFortyNine_highIncidenceCount_eq_lowDefectDegreeCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {i : ℕ} (hi : i ≤ 3) :
    orderFortyNineHighIncidenceCount G i =
      orderFortyNineLowDefectDegreeCount G (6 - i) := by
  unfold orderFortyNineHighIncidenceCount
  unfold orderFortyNineLowDefectDegreeCount
  congr 1
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hxlow, hk⟩
    refine ⟨hxlow, ?_⟩
    have hxnot : x ∉ orderFortyNineHighVertices G := by
      exact (Finset.mem_sdiff.mp hxlow).2
    have hxdeg : G.degree x = 7 := by
      rcases orderFortyNine_degree_eq_seven_or_eight
          G hfree hmin hcard x with hx7 | hx8
      · exact hx7
      · exact (hxnot (by simp [orderFortyNineHighVertices, hx8])).elim
    have hbudget := orderFortyNine_defectDegree_add_highNeighborCount_eq_six
      G hfree hmin hcard hxdeg
    omega
  · rintro ⟨hxlow, hD⟩
    refine ⟨hxlow, ?_⟩
    have hxnot : x ∉ orderFortyNineHighVertices G := by
      exact (Finset.mem_sdiff.mp hxlow).2
    have hxdeg : G.degree x = 7 := by
      rcases orderFortyNine_degree_eq_seven_or_eight
          G hfree hmin hcard x with hx7 | hx8
      · exact hx7
      · exact (hxnot (by simp [orderFortyNineHighVertices, hx8])).elim
    have hbudget := orderFortyNine_defectDegree_add_highNeighborCount_eq_six
      G hfree hmin hcard hxdeg
    omega

/-- The five `h=9` incidence profiles are equivalently the following five
defect-degree distributions on the forty low vertices. -/
theorem orderFortyNine_lowDefectDegree_profile_of_nine_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9) :
    let d := orderFortyNineLowDefectDegreeCount G
    (d 6 = 4 ∧ d 5 = 0 ∧ d 4 = 36 ∧ d 3 = 0) ∨
    (d 6 = 3 ∧ d 5 = 3 ∧ d 4 = 33 ∧ d 3 = 1) ∨
    (d 6 = 2 ∧ d 5 = 6 ∧ d 4 = 30 ∧ d 3 = 2) ∨
    (d 6 = 1 ∧ d 5 = 9 ∧ d 4 = 27 ∧ d 3 = 3) ∨
    (d 6 = 0 ∧ d 5 = 12 ∧ d 4 = 24 ∧ d 3 = 4) := by
  dsimp only
  have heq0 := orderFortyNine_highIncidenceCount_eq_lowDefectDegreeCount
    G hfree hmin hcard (i := 0) (by omega)
  have heq1 := orderFortyNine_highIncidenceCount_eq_lowDefectDegreeCount
    G hfree hmin hcard (i := 1) (by omega)
  have heq2 := orderFortyNine_highIncidenceCount_eq_lowDefectDegreeCount
    G hfree hmin hcard (i := 2) (by omega)
  have heq3 := orderFortyNine_highIncidenceCount_eq_lowDefectDegreeCount
    G hfree hmin hcard (i := 3) (by omega)
  norm_num at heq0 heq1 heq2 heq3
  rcases orderFortyNine_highIncidence_profile_of_nine_high
      G hfree hmin hcard hHigh with hp | hp | hp | hp | hp <;>
    omega

/-- The second-order defect graph has exactly `7(21-h)` edges, where `h` is
the number of high vertices. -/
theorem orderFortyNine_secondOrderDefect_edge_count
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) :
    (secondOrderDefectGraph G).edgeFinset.card =
      7 * (21 - (orderFortyNineHighVertices G).card) := by
  let H := orderFortyNineHighVertices G
  let L := orderFortyNineLowVertices G
  let D := secondOrderDefectGraph G
  let k : V → ℕ := fun x => (G.neighborFinset x ∩ H).card
  have hlow : ∀ x ∈ L, D.degree x + k x = 6 := by
    intro x hx
    have hxnot : x ∉ H := (Finset.mem_sdiff.mp hx).2
    have hxdeg : G.degree x = 7 := by
      rcases orderFortyNine_degree_eq_seven_or_eight
          G hfree hmin hcard x with hx7 | hx8
      · exact hx7
      · exact (hxnot (by simp [H, orderFortyNineHighVertices, hx8])).elim
    exact orderFortyNine_defectDegree_add_highNeighborCount_eq_six
      G hfree hmin hcard hxdeg
  have hsumLocal :
      (∑ x ∈ L, D.degree x) + (∑ x ∈ L, k x) = 6 * L.card := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ x ∈ L, (D.degree x + k x)) = ∑ _x ∈ L, 6 := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hlow x hx
      _ = 6 * L.card := by simp [Nat.mul_comm]
  have hfirst : (∑ x ∈ L, k x) = 8 * H.card := by
    simpa [H, L, k, orderFortyNineLowVertices] using
      orderFortyNine_sum_low_highNeighborCount_eq G hfree hmin hcard
  have hLcard : L.card = 49 - H.card := by
    dsimp [L, orderFortyNineLowVertices]
    rw [Finset.card_sdiff, Finset.card_univ, hcard]
    simp [H]
  have hhighZero : (∑ x ∈ H, D.degree x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hx8 : G.degree x = 8 := (Finset.mem_filter.mp hx).2
    exact (orderFortyNine_degreeEight_defectDegree_and_neighborExcess_zero
      G hfree hmin hcard hx8).1
  have hsplit := Finset.sum_sdiff
    (show H ⊆ (Finset.univ : Finset V) by simp)
    (f := fun x => D.degree x)
  have hsumAll : (∑ x : V, D.degree x) = ∑ x ∈ L, D.degree x := by
    change (∑ x ∈ (Finset.univ : Finset V), D.degree x) = _
    change (∑ x ∈ (Finset.univ : Finset V) \ H, D.degree x) +
      (∑ x ∈ H, D.degree x) =
      (∑ x ∈ (Finset.univ : Finset V), D.degree x) at hsplit
    rw [hhighZero, add_zero] at hsplit
    exact hsplit.symm
  have hHle : H.card ≤ 9 := by
    simpa [H] using orderFortyNine_card_high_le_nine G hfree hmin hcard
  have hdegreeSum : (∑ x : V, D.degree x) = 14 * (21 - H.card) := by
    rw [hsumAll]
    rw [hfirst, hLcard] at hsumLocal
    omega
  have hhand := D.sum_degrees_eq_twice_card_edges
  rw [hdegreeSum] at hhand
  change D.edgeFinset.card = 7 * (21 - H.card)
  omega

end

end Erdos85
