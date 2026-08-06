import Proofs.Erdos85ExcessDefectRegular
import Proofs.Erdos85SecondOrderColorTrace
import Proofs.Erdos85NonneighborReduction

/-!
# The excess-one local dichotomy

For a regular `C₄`-free graph of order `d(d-1)+4`, the combined defect graph
is cubic.  When `d` is odd, the triangle-free part of the defect at each
vertex consequently has size one or three.  If moreover `d ≡ 3 (mod 6)`,
the value three must occur: otherwise the graph of triangular edges would be
locally linear with an edge count not divisible by three.

This is the uniform first half of the excess-one obstruction of Boza, phrased
in the defect-graph vocabulary used by the rest of the Erdős 85 development.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A graph of odd order and maximum degree at most one has an isolated
vertex.  This is the parity step used inside an odd second-layer branch. -/
theorem exists_degree_eq_zero_of_odd_card_of_degree_le_one
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hodd : Odd (Fintype.card W)) (hle : ∀ w, H.degree w ≤ 1) :
    ∃ w, H.degree w = 0 := by
  by_contra hnone
  push_neg at hnone
  have hone : ∀ w, H.degree w = 1 := by
    intro w
    have := hle w
    have := hnone w
    omega
  have hsum : ∑ w, H.degree w = Fintype.card W := by
    simp_rw [hone]
    simp
  have hhand := H.sum_degrees_eq_twice_card_edges
  obtain ⟨k, hk⟩ := hodd
  omega

/-- In an odd graph of maximum degree one, the number of isolated vertices
is itself odd.  The non-isolated vertices contribute one each to the even
degree sum. -/
theorem odd_card_isolatedVertices_of_odd_card_of_degree_le_one
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hodd : Odd (Fintype.card W)) (hle : ∀ w, H.degree w ≤ 1) :
    Odd ((Finset.univ.filter fun w => H.degree w = 0).card) := by
  let I := Finset.univ.filter fun w => H.degree w = 0
  let P := Finset.univ.filter fun w => H.degree w ≠ 0
  have hsum : ∑ w, H.degree w = P.card := by
    calc
      ∑ w, H.degree w = ∑ w, if H.degree w = 0 then 0 else 1 := by
        apply Finset.sum_congr rfl
        intro w _
        by_cases hw : H.degree w = 0
        · simp [hw]
        · simp [hw]
          have hwle := hle w
          omega
      _ = ∑ w, if H.degree w ≠ 0 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro w _
        by_cases hw : H.degree w = 0 <;> simp [hw]
      _ = P.card := by
        simpa [P] using
          (Finset.sum_boole (R := ℕ) (fun w : W => H.degree w ≠ 0)
            (Finset.univ : Finset W))
  have hPeven : Even P.card := by
    have hhand := H.sum_degrees_eq_twice_card_edges
    rw [hsum] at hhand
    exact ⟨H.edgeFinset.card, by omega⟩
  have hpartition : I.card + P.card = Fintype.card W := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset W)) (p := fun w => H.degree w = 0)
    simpa [I, P, Finset.card_univ] using h
  change Odd I.card
  obtain ⟨i, hi⟩ := hodd
  obtain ⟨p, hp⟩ := hPeven
  have hpi : p ≤ i := by omega
  refine ⟨i - p, ?_⟩
  omega

/-- Every graph induced on a second-layer branch has maximum degree at most
one: two neighbors in the same branch, together with its first-layer root,
would form a four-cycle. -/
theorem degree_induce_secondLayerBranch_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x : V)
    (y : {z : V // z ∈ G.neighborSet x})
    (w : secondLayerBranch G x y) :
    (G.induce (secondLayerBranch G x y)).degree w ≤ 1 := by
  classical
  rw [← (G.induce (secondLayerBranch G x y)).card_neighborFinset_eq_degree]
  rw [Finset.card_le_one]
  intro a ha b hb
  apply Subtype.ext
  by_contra hab
  have hwa : G.Adj w.1 a.1 := by
    simpa [SimpleGraph.mem_neighborFinset] using ha
  have hwb : G.Adj w.1 b.1 := by
    simpa [SimpleGraph.mem_neighborFinset] using hb
  have hya : G.Adj y.1 a.1 :=
    (G.mem_neighborFinset y.1 a.1).mp (Finset.mem_sdiff.mp a.2).1
  have hyb : G.Adj y.1 b.1 :=
    (G.mem_neighborFinset y.1 b.1).mp (Finset.mem_sdiff.mp b.2).1
  have hyw_ne : y.1 ≠ w.1 := by
    intro h
    exact (Finset.mem_sdiff.mp w.2).2
      (Finset.mem_insert.mpr (Or.inr
        ((G.mem_neighborFinset x w.1).mpr (h ▸ y.2))))
  exact hfree (containsC4_of_two_common
    (x := a.1) (y := b.1) (v := w.1) (v' := y.1)
    hab hyw_ne.symm hwa hwb hya hyb)

/-- A vertex has at most one neighbor in any second-layer branch whose root
is distinct from it. -/
theorem card_neighborFinset_inter_secondLayerBranch_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x a : V)
    (y : {z : V // z ∈ G.neighborSet x}) (hay : a ≠ y.1) :
    (G.neighborFinset a ∩ secondLayerBranch G x y).card ≤ 1 := by
  have hsub : G.neighborFinset a ∩ secondLayerBranch G x y ⊆
      G.neighborFinset a ∩ G.neighborFinset y.1 := by
    intro z hz
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hz).1,
      (Finset.mem_sdiff.mp (Finset.mem_inter.mp hz).2).1⟩
  exact (Finset.card_le_card hsub).trans
    (common_le_one_of_not_containsC4 hfree a y.1 hay)

/-- Branches rooted at adjacent first-layer vertices have no edges between
them.  Such an edge would close a four-cycle through the two roots. -/
theorem not_adj_between_secondLayerBranches_of_adj_roots
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x : V)
    (u v : {z : V // z ∈ G.neighborSet x}) (huv : G.Adj u.1 v.1)
    (a : secondLayerBranch G x u) (b : secondLayerBranch G x v) :
    ¬ G.Adj a.1 b.1 := by
  intro hab
  have hua : G.Adj u.1 a.1 :=
    (G.mem_neighborFinset u.1 a.1).mp (Finset.mem_sdiff.mp a.2).1
  have hvb : G.Adj v.1 b.1 :=
    (G.mem_neighborFinset v.1 b.1).mp (Finset.mem_sdiff.mp b.2).1
  have hub : u.1 ≠ b.1 := by
    intro h
    exact (Finset.mem_sdiff.mp b.2).2
      (Finset.mem_insert.mpr (Or.inr
        ((G.mem_neighborFinset x b.1).mpr (h ▸ u.2))))
  have hva : v.1 ≠ a.1 := by
    intro h
    exact (Finset.mem_sdiff.mp a.2).2
      (Finset.mem_insert.mpr (Or.inr
        ((G.mem_neighborFinset x a.1).mpr (h ▸ v.2))))
  exact hfree (containsC4_of_two_common
    (x := u.1) (y := b.1) (v := v.1) (v' := a.1)
    hub hva huv.symm hvb hua.symm hab)

/-- Exact size of a second-layer branch in a regular graph: its only
neighbors omitted from the branch are the center and the neighbors it shares
with the center. -/
theorem card_secondLayerBranch_eq_degree_sub_localDegree_sub_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : ∀ x, G.degree x = d) (x : V)
    (y : {z : V // z ∈ G.neighborSet x}) :
    (secondLayerBranch G x y).card =
      d - (G.induce (G.neighborSet x)).degree y - 1 := by
  have hcount := card_secondLayerBranch_add_common_add_one G x y
  rw [← degree_induce_neighborSet_eq_card_common, hreg y.1] at hcount
  omega

/-- At positive excess one and odd degree, exactly one or three incident
edges at every vertex lie in no triangle. -/
theorem excessOne_triangleFreeNeighbors_card_eq_one_or_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) (x : V) :
    (triangleFreeNeighbors G x).card = 1 ∨
      (triangleFreeNeighbors G x).card = 3 := by
  have hsum := card_triangleFreeNeighbors_add_localDegreeSum_of_regular
    G hfree hreg x
  let H := G.induce (G.neighborSet x)
  have hhand :
      (∑ y : {z : V // z ∈ G.neighborSet x}, H.degree y) =
        2 * H.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges H
  have hle : (triangleFreeNeighbors G x).card ≤ 3 := by
    have hsub : triangleFreeNeighbors G x ⊆
        (secondOrderDefectGraph G).neighborFinset x := by
      intro y hy
      rw [secondOrderDefectGraph_neighborFinset]
      exact Finset.mem_union_right _ hy
    calc
      (triangleFreeNeighbors G x).card ≤
          ((secondOrderDefectGraph G).neighborFinset x).card :=
        Finset.card_le_card hsub
      _ = (secondOrderDefectGraph G).degree x :=
        (secondOrderDefectGraph G).card_neighborFinset_eq_degree x
      _ = 3 := by
        simpa using secondOrderDefectGraph_degree_eq_excess_add_two
          G hfree hreg (e := 1) (by simpa using hcard) x
  have hdmod : d % 2 = 1 := Nat.odd_iff.mp hodd
  have htfmod : (triangleFreeNeighbors G x).card % 2 = 1 := by
    rw [hhand] at hsum
    omega
  omega

/-- In the `d ≡ 3 (mod 6)` excess-one regime, some vertex has three
triangle-free incident edges.  The alternative would make all triangular
edges a locally linear graph whose edge count is simultaneously and is not
divisible by three. -/
theorem exists_excessOne_triangleFreeNeighbors_card_eq_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hmod : d % 6 = 3) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    ∃ x : V, (triangleFreeNeighbors G x).card = 3 := by
  classical
  have hodd : Odd d := Nat.odd_iff.mpr (by omega)
  by_contra hnone
  push_neg at hnone
  have hone : ∀ x : V, (triangleFreeNeighbors G x).card = 1 := by
    intro x
    rcases excessOne_triangleFreeNeighbors_card_eq_one_or_three
        G hfree hodd hreg hcard x with hx | hx
    · exact hx
    · exact (hnone x hx).elim
  let T := triangleFreeEdgeGraph G
  let H := triangularEdgeGraph G
  have hsumG : ∑ x : V, G.degree x = Fintype.card V * d := by
    simp_rw [hreg]
    simp
  have hedgeG : 2 * G.edgeFinset.card = Fintype.card V * d := by
    rw [← SimpleGraph.sum_degrees_eq_twice_card_edges G]
    exact hsumG
  have hTdeg : ∀ x : V, T.degree x = 1 := by
    intro x
    rw [← T.card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset]
    exact hone x
  have hsumT : ∑ x : V, T.degree x = Fintype.card V := by
    simp_rw [hTdeg]
    simp
  have hedgeT : 2 * T.edgeFinset.card = Fintype.card V := by
    rw [← SimpleGraph.sum_degrees_eq_twice_card_edges T]
    exact hsumT
  have hTle : T ≤ G := by
    intro x y hxy
    exact ((mem_triangleFreeNeighbors G x y).mp
      ((triangleFreeEdgeGraph_adj G x y).mp hxy)).1
  have hpartition : G.edgeFinset.card = H.edgeFinset.card + T.edgeFinset.card := by
    have heq : H.edgeFinset = G.edgeFinset \ T.edgeFinset := by
      ext e
      simp [H, T, triangularEdgeGraph]
    have hlecard : T.edgeFinset.card ≤ G.edgeFinset.card :=
      Finset.card_le_card (edgeFinset_mono hTle)
    rw [heq, Finset.card_sdiff_of_subset (edgeFinset_mono hTle)]
    omega
  have hlocal : H.LocallyLinear :=
    triangularEdgeGraph_locallyLinear_of_not_containsC4 G hfree
  have htri : H.edgeFinset.card = 3 * (H.cliqueFinset 3).card :=
    hlocal.card_edgeFinset
  have hdform : d = 6 * (d / 6) + 3 := by omega
  have hdmod3 : d % 3 = 0 := by omega
  have hdminus : (d - 1) % 3 = 2 := by omega
  have hnmod : Fintype.card V % 3 = 1 := by
    rw [hcard, Nat.add_mod, Nat.mul_mod, hdmod3, hdminus]
  have hd1 : 1 ≤ d := by omega
  have hprod : Fintype.card V * d =
      Fintype.card V * (d - 1) + Fintype.card V := by
    calc
      Fintype.card V * d = Fintype.card V * ((d - 1) + 1) := by
        rw [Nat.sub_add_cancel hd1]
      _ = Fintype.card V * (d - 1) + Fintype.card V := by ring
  have harith : 2 * H.edgeFinset.card = Fintype.card V * (d - 1) := by
    omega
  have hlmod : (2 * H.edgeFinset.card) % 3 = 0 := by
    rw [htri]
    omega
  have hrmod : (Fintype.card V * (d - 1)) % 3 = 2 := by
    rw [Nat.mul_mod, hnmod, hdminus]
  have := congrArg (· % 3) harith
  omega

/-- At an excess-one vertex with three triangle-free incident edges there is
no third distance layer: the pairwise-disjoint branches through its neighbors
partition the whole complement of its closed neighborhood. -/
theorem excessOne_secondLayer_eq_outsideClosedNeighborhood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    (x : V) (hx : (triangleFreeNeighbors G x).card = 3) :
    secondLayer G x = outsideClosedNeighborhood G x := by
  classical
  have hlocalsum :
      (∑ y : {z : V // z ∈ G.neighborSet x},
        (G.induce (G.neighborSet x)).degree y) = d - 3 := by
    have hsum := card_triangleFreeNeighbors_add_localDegreeSum_of_regular
      G hfree hreg x
    rw [hx] at hsum
    omega
  have hextid := card_external_add_degree_sq_add_one_eq_card_add_localDegreeSum
    G hfree hreg x
  rw [hcard, hlocalsum] at hextid
  have hextcard : (externalRepairCandidates G x).card = 0 := by
    have hd3 : 3 ≤ d := by
      have hle := (Finset.card_le_card
        (show triangleFreeNeighbors G x ⊆ G.neighborFinset x by
          intro y hy
          exact (G.mem_neighborFinset x y).mpr
            ((mem_triangleFreeNeighbors G x y).mp hy).1))
      rw [hx, G.card_neighborFinset_eq_degree, hreg x] at hle
      exact hle
    have hmul : d * d = d * (d - 1) + d := by
      calc
        d * d = d * ((d - 1) + 1) := by rw [Nat.sub_add_cancel (by omega)]
        _ = d * (d - 1) + d := by ring
    rw [hmul] at hextid
    omega
  have hext : externalRepairCandidates G x = ∅ := Finset.card_eq_zero.mp hextcard
  apply Finset.Subset.antisymm
  · intro y hy
    simp only [outsideClosedNeighborhood, Finset.mem_filter]
    change y ∈ secondLayer G x at hy
    rw [secondLayer, Finset.mem_biUnion] at hy
    obtain ⟨z, _, hz⟩ := hy
    have hout := (Finset.mem_sdiff.mp hz).2
    refine ⟨Finset.mem_univ y, ?_, ?_⟩
    · intro hyx
      exact hout (Finset.mem_insert.mpr (Or.inl hyx))
    · intro hyadj
      exact hout (Finset.mem_insert.mpr (Or.inr
        ((G.mem_neighborFinset x y).mpr hyadj.symm)))
  · intro y hy
    have hcover := closedNeighborhood_union_secondLayer_union_external_eq_univ G x
    have hycover : y ∈ insert x (G.neighborFinset x) ∪ secondLayer G x ∪
        (externalRepairCandidates G x).map
          ⟨Subtype.val, Subtype.val_injective⟩ := by
      rw [hcover]
      exact Finset.mem_univ y
    rw [hext] at hycover
    simp only [Finset.map_empty, Finset.union_empty] at hycover
    rcases Finset.mem_union.mp hycover with hclosed | hsecond
    · have hyout := (Finset.mem_filter.mp hy).2
      rcases Finset.mem_insert.mp hclosed with rfl | hneighbor
      · exact (hyout.1 rfl).elim
      · exact (hyout.2 ((G.mem_neighborFinset x y).mp hneighbor).symm).elim
    · exact hsecond

/-- At an excess-one vertex with exactly one triangle-free incident edge,
the failure of the second layer to cover the complement is exact: there are
precisely two vertices at distance at least three.  These are the two slots
that remain in the odd matching-branch pigeonhole argument. -/
theorem excessOne_externalRepairCandidates_card_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    (x : V) (hx : (triangleFreeNeighbors G x).card = 1) :
    (externalRepairCandidates G x).card = 2 := by
  have hlocalsum :
      (∑ y : {z : V // z ∈ G.neighborSet x},
        (G.induce (G.neighborSet x)).degree y) = d - 1 := by
    have hsum := card_triangleFreeNeighbors_add_localDegreeSum_of_regular
      G hfree hreg x
    rw [hx] at hsum
    omega
  have hextid := card_external_add_degree_sq_add_one_eq_card_add_localDegreeSum
    G hfree hreg x
  rw [hcard, hlocalsum] at hextid
  have hd1 : 1 ≤ d := by
    have hle := Finset.card_le_card
      (show triangleFreeNeighbors G x ⊆ G.neighborFinset x by
        intro y hy
        exact (G.mem_neighborFinset x y).mpr
          ((mem_triangleFreeNeighbors G x y).mp hy).1)
    rw [hx, G.card_neighborFinset_eq_degree, hreg x] at hle
    exact hle
  have hmul : d * d = d * (d - 1) + d := by
    calc
      d * d = d * ((d - 1) + 1) := by rw [Nat.sub_add_cancel hd1]
      _ = d * (d - 1) + d := by ring
  rw [hmul] at hextid
  omega

/-- An isolated vertex in a second-layer branch whose root is paired inside
the first neighborhood must see the external reservoir.  Otherwise its
`d-1` non-root neighbors inject into only the `d-2` branches other than the
root and its partner.  This is the corrected pigeonhole statement for the
triangle-free-degree-one case. -/
theorem exists_adj_external_of_isolated_matched_secondLayerBranch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ z, G.degree z = d) (x : V)
    (u v : {z : V // z ∈ G.neighborSet x}) (huv : G.Adj u.1 v.1)
    (a : secondLayerBranch G x u)
    (haIso : (G.induce (secondLayerBranch G x u)).degree a = 0) :
    ∃ z : {y : V // y ≠ x},
      z ∈ externalRepairCandidates G x ∧ G.Adj a.1 z.1 := by
  classical
  by_contra hnone
  push_neg at hnone
  let B := (G.neighborFinset a.1).erase u.1
  have hua : G.Adj u.1 a.1 :=
    (G.mem_neighborFinset u.1 a.1).mp (Finset.mem_sdiff.mp a.2).1
  have huMem : u.1 ∈ G.neighborFinset a.1 :=
    (G.mem_neighborFinset a.1 u.1).mpr hua.symm
  have hBcard : B.card = d - 1 := by
    simp only [B]
    rw [Finset.card_erase_of_mem huMem,
      G.card_neighborFinset_eq_degree, hreg a.1]
  have hroot : ∀ b, b ∈ B →
      ∃ r : {z : V // z ∈ G.neighborSet x},
        b ∈ secondLayerBranch G x r := by
    intro b hb
    have hab : G.Adj a.1 b :=
      (G.mem_neighborFinset a.1 b).mp (Finset.mem_erase.mp hb).2
    have hbu : b ≠ u.1 := (Finset.mem_erase.mp hb).1
    have hbClosed : b ∉ insert x (G.neighborFinset x) := by
      intro hbcl
      rcases Finset.mem_insert.mp hbcl with hbx | hbx
      · subst b
        exact (Finset.mem_sdiff.mp a.2).2
          (Finset.mem_insert.mpr (Or.inr
            ((G.mem_neighborFinset x a.1).mpr hab.symm)))
      · have hxb : G.Adj x b := (G.mem_neighborFinset x b).mp hbx
        have hxa : x ≠ a.1 := by
          intro h
          exact (Finset.mem_sdiff.mp a.2).2
            (Finset.mem_insert.mpr (Or.inl h.symm))
        exact hfree (containsC4_of_two_common
          (x := x) (y := a.1) (v := u.1) (v' := b)
          hxa hbu.symm u.2.symm hua hxb.symm hab.symm)
    have hcover := closedNeighborhood_union_secondLayer_union_external_eq_univ G x
    have hbcover : b ∈ insert x (G.neighborFinset x) ∪ secondLayer G x ∪
        (externalRepairCandidates G x).map
          ⟨Subtype.val, Subtype.val_injective⟩ := by
      rw [hcover]
      exact Finset.mem_univ b
    rcases Finset.mem_union.mp hbcover with hleft | hext
    · rcases Finset.mem_union.mp hleft with hclosed | hsecond
      · exact (hbClosed hclosed).elim
      · rw [secondLayer, Finset.mem_biUnion] at hsecond
        obtain ⟨r, _, hr⟩ := hsecond
        exact ⟨r, hr⟩
    · rw [Finset.mem_map] at hext
      obtain ⟨z, hz, hzb⟩ := hext
      have := hnone z hz
      exact (this (by simpa [← hzb] using hab)).elim
  let root : B → {z : V // z ∈ G.neighborSet x} := fun b =>
    Classical.choose (hroot b.1 b.2)
  have hrootMem : ∀ b : B, b.1 ∈ secondLayerBranch G x (root b) := by
    intro b
    exact Classical.choose_spec (hroot b.1 b.2)
  have hroot_ne_u : ∀ b : B, root b ≠ u := by
    intro b hru
    have hbA : b.1 ∈ secondLayerBranch G x u := by
      simpa [hru] using hrootMem b
    have habK : (G.induce (secondLayerBranch G x u)).Adj
        a ⟨b.1, hbA⟩ := by
      change G.Adj a.1 b.1
      exact (G.mem_neighborFinset a.1 b.1).mp
        (Finset.mem_erase.mp b.2).2
    have hbK : (⟨b.1, hbA⟩ : secondLayerBranch G x u) ∈
        (G.induce (secondLayerBranch G x u)).neighborFinset a :=
      ((G.induce (secondLayerBranch G x u)).mem_neighborFinset a _).mpr habK
    have hempty :
        (G.induce (secondLayerBranch G x u)).neighborFinset a = ∅ := by
      apply Finset.card_eq_zero.mp
      rw [(G.induce (secondLayerBranch G x u)).card_neighborFinset_eq_degree,
        haIso]
    rw [hempty] at hbK
    exact Finset.notMem_empty _ hbK
  have hroot_ne_v : ∀ b : B, root b ≠ v := by
    intro b hrv
    have hbV : b.1 ∈ secondLayerBranch G x v := by
      simpa [hrv] using hrootMem b
    have hab : G.Adj a.1 b.1 :=
      (G.mem_neighborFinset a.1 b.1).mp (Finset.mem_erase.mp b.2).2
    exact (not_adj_between_secondLayerBranches_of_adj_roots
      G hfree x u v huv a ⟨b.1, hbV⟩) hab
  have hrootInj : Function.Injective root := by
    intro b c hbc
    apply Subtype.ext
    by_contra hbval
    have htwo : 2 ≤
        (G.neighborFinset a.1 ∩ secondLayerBranch G x (root b)).card := by
      have hcMem : c.1 ∈ secondLayerBranch G x (root b) := by
        rw [hbc]
        exact hrootMem c
      have hsub : ({b.1, c.1} : Finset V) ⊆
          G.neighborFinset a.1 ∩ secondLayerBranch G x (root b) := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_inter.mpr
            ⟨(Finset.mem_erase.mp b.2).2, hrootMem b⟩
        · exact Finset.mem_inter.mpr
            ⟨(Finset.mem_erase.mp c.2).2, hcMem⟩
      have hpair : ({b.1, c.1} : Finset V).card = 2 := by simp [hbval]
      rw [← hpair]
      exact Finset.card_le_card hsub
    have hroot_ne_a : a.1 ≠ (root b).1 := by
      intro h
      exact (Finset.mem_sdiff.mp a.2).2
        (Finset.mem_insert.mpr (Or.inr
          ((G.mem_neighborFinset x a.1).mpr (h ▸ (root b).2))))
    have hone := card_neighborFinset_inter_secondLayerBranch_le_one
      G hfree x a.1 (root b) hroot_ne_a
    omega
  have huv_ne : u ≠ v := by
    intro h
    exact (G.ne_of_adj huv) (congrArg Subtype.val h)
  let target := (Finset.univ.erase u).erase v
  let root' : B → target := fun b => ⟨root b, by
    simp only [target, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨hroot_ne_v b, hroot_ne_u b⟩⟩
  have hroot'Inj : Function.Injective root' := by
    intro b c h
    apply hrootInj
    exact congrArg Subtype.val h
  have hlecard : Fintype.card B ≤ Fintype.card target :=
    Fintype.card_le_of_injective root' hroot'Inj
  have hNcard : Fintype.card {z : V // z ∈ G.neighborSet x} = d := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet x) =
        G.neighborFinset x := by ext z; simp
    rw [heq, G.card_neighborFinset_eq_degree, hreg x]
  have hd2 : 2 ≤ d := by
    have hpair : ({u, v} : Finset {z : V // z ∈ G.neighborSet x}).card = 2 := by
      simp [huv_ne]
    have hpairle : ({u, v} : Finset {z : V // z ∈ G.neighborSet x}).card ≤
        Fintype.card {z : V // z ∈ G.neighborSet x} := by
      simpa [Fintype.card_subtype] using
        (Finset.card_le_card (Finset.subset_univ ({u, v} :
          Finset {z : V // z ∈ G.neighborSet x})))
    rw [hpair, hNcard] at hpairle
    exact hpairle
  have htargetcard : Fintype.card target = d - 2 := by
    simp only [target, Fintype.card_coe]
    rw [Finset.card_erase_of_mem]
    · rw [Finset.card_erase_of_mem (Finset.mem_univ u),
        Finset.card_univ, hNcard]
      omega
    · exact Finset.mem_erase.mpr ⟨huv_ne.symm, Finset.mem_univ v⟩
  rw [Fintype.card_coe, hBcard, htargetcard] at hlecard
  omega

/-- In the odd excess-one, triangle-free-degree-one regime, every branch
whose root is paired inside the first neighborhood has exactly one isolated
vertex.  Oddness gives an odd number of isolated vertices; each must choose
one of the two external vertices, and `C₄`-freeness makes that choice
injective. -/
theorem isolatedVertices_card_eq_one_of_matched_secondLayerBranch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    (x : V) (hx : (triangleFreeNeighbors G x).card = 1)
    (u v : {z : V // z ∈ G.neighborSet x}) (huv : G.Adj u.1 v.1) :
    ((Finset.univ : Finset (secondLayerBranch G x u)).filter fun a =>
      (G.induce (secondLayerBranch G x u)).degree a = 0).card = 1 := by
  classical
  let A := secondLayerBranch G x u
  let K := G.induce A
  let I := (Finset.univ : Finset A).filter fun a => K.degree a = 0
  have huLocal : (G.induce (G.neighborSet x)).degree u = 1 := by
    have hle : (G.induce (G.neighborSet x)).degree u ≤ 1 := by
      rw [degree_induce_neighborSet_eq_card_common]
      exact common_le_one_of_not_containsC4 hfree x u.1 (G.ne_of_adj u.2)
    have hvMem : v ∈ (G.induce (G.neighborSet x)).neighborFinset u := by
      rw [(G.induce (G.neighborSet x)).mem_neighborFinset]
      exact huv
    have hpos : 0 < (G.induce (G.neighborSet x)).degree u := by
      rw [← (G.induce (G.neighborSet x)).card_neighborFinset_eq_degree,
        Finset.card_pos]
      exact ⟨v, hvMem⟩
    omega
  have hAcard : Fintype.card A = d - 2 := by
    rw [Fintype.card_coe]
    have h := card_secondLayerBranch_eq_degree_sub_localDegree_sub_one
      G hreg x u
    rw [huLocal] at h
    change A.card = d - 1 - 1 at h
    omega
  have hd2 : 2 ≤ d := by
    have huDeg := hreg x
    have huv_ne : u ≠ v := by
      intro h
      exact (G.ne_of_adj huv) (congrArg Subtype.val h)
    have huv_val_ne : u.1 ≠ v.1 := fun h => huv_ne (Subtype.ext h)
    have hpair : ({u.1, v.1} : Finset V).card = 2 := by
      simp [huv_val_ne]
    have hsub : ({u.1, v.1} : Finset V) ⊆ G.neighborFinset x := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact (G.mem_neighborFinset x u.1).mpr u.2
      · exact (G.mem_neighborFinset x v.1).mpr v.2
    have := Finset.card_le_card hsub
    rw [hpair, G.card_neighborFinset_eq_degree, huDeg] at this
    exact this
  have hAodd : Odd (Fintype.card A) := by
    rw [hAcard]
    obtain ⟨k, hk⟩ := hodd
    refine ⟨k - 1, ?_⟩
    omega
  have hKle : ∀ a : A, K.degree a ≤ 1 := by
    intro a
    exact degree_induce_secondLayerBranch_le_one G hfree x u a
  have hIodd : Odd I.card := by
    exact odd_card_isolatedVertices_of_odd_card_of_degree_le_one
      K hAodd hKle
  let E := externalRepairCandidates G x
  have hEcard : E.card = 2 :=
    excessOne_externalRepairCandidates_card_eq_two
      G hfree hreg hcard x hx
  have hchoose : ∀ a : I,
      ∃ z : {y : V // y ≠ x}, z ∈ E ∧ G.Adj a.1.1 z.1 := by
    intro a
    exact exists_adj_external_of_isolated_matched_secondLayerBranch
      G hfree hreg x u v huv ⟨a.1.1, a.1.2⟩ (by
        change K.degree a.1 = 0
        exact (Finset.mem_filter.mp a.2).2)
  let pick : I → {z : {y : V // y ≠ x} // z ∈ E} := fun a =>
    ⟨Classical.choose (hchoose a), (Classical.choose_spec (hchoose a)).1⟩
  have hpickAdj : ∀ a : I, G.Adj a.1.1 (pick a).1.1 := by
    intro a
    exact (Classical.choose_spec (hchoose a)).2
  have hpickInj : Function.Injective pick := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    by_contra habv
    have hzu : (pick a).1.1 ≠ u.1 := by
      intro h
      have hzext := (mem_externalRepairCandidates G x (pick a).1).mp (pick a).2
      exact hzext.1 (h ▸ u.2.symm)
    have hua : G.Adj u.1 a.1.1 :=
      (G.mem_neighborFinset u.1 a.1.1).mp (Finset.mem_sdiff.mp a.1.2).1
    have hub : G.Adj u.1 b.1.1 :=
      (G.mem_neighborFinset u.1 b.1.1).mp (Finset.mem_sdiff.mp b.1.2).1
    have hzb : G.Adj b.1.1 (pick a).1.1 := by
      have := hpickAdj b
      simpa [hab] using this
    exact hfree (containsC4_of_two_common
      (x := u.1) (y := (pick a).1.1) (v := a.1.1) (v' := b.1.1)
      hzu.symm habv hua.symm (hpickAdj a) hub.symm hzb)
  have hIle : Fintype.card I ≤ Fintype.card {z : {y : V // y ≠ x} // z ∈ E} :=
    Fintype.card_le_of_injective pick hpickInj
  have hIle2 : I.card ≤ 2 := by
    rw [Fintype.card_coe, Fintype.card_subtype] at hIle
    have heq : Finset.univ.filter (fun z => z ∈ E) = E := by ext z; simp
    rw [heq, hEcard] at hIle
    exact hIle
  have hIeq : I.card = 1 := by
    obtain ⟨k, hk⟩ := hIodd
    omega
  simpa [I, K, A] using hIeq

/-- The canonical isolated vertex of a matched branch sees either one or
both of the center's two antipodes. -/
theorem card_neighbor_inter_antipodal_of_isolated_matched_branch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    (x : V) (hx : (triangleFreeNeighbors G x).card = 1)
    (u v : {z : V // z ∈ G.neighborSet x}) (huv : G.Adj u.1 v.1)
    (a : secondLayerBranch G x u)
    (haIso : (G.induce (secondLayerBranch G x u)).degree a = 0) :
    (G.neighborFinset a.1 ∩ antipodalNeighbors G x).card = 1 ∨
      (G.neighborFinset a.1 ∩ antipodalNeighbors G x).card = 2 := by
  classical
  have hext := exists_adj_external_of_isolated_matched_secondLayerBranch
    G hfree hreg x u v huv a haIso
  obtain ⟨z, hzE, haz⟩ := hext
  have hzAnti : z.1 ∈ antipodalNeighbors G x := by
    rw [antipodalNeighbors, Finset.mem_map]
    exact ⟨z, hzE, rfl⟩
  have hzInter : z.1 ∈ G.neighborFinset a.1 ∩ antipodalNeighbors G x :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a.1 z.1).mpr haz, hzAnti⟩
  have hpos : 0 < (G.neighborFinset a.1 ∩ antipodalNeighbors G x).card :=
    Finset.card_pos.mpr ⟨z.1, hzInter⟩
  have hAntiCard : (antipodalNeighbors G x).card = 2 := by
    rw [antipodalNeighbors, Finset.card_map]
    exact excessOne_externalRepairCandidates_card_eq_two
      G hfree hreg hcard x hx
  have hle : (G.neighborFinset a.1 ∩ antipodalNeighbors G x).card ≤ 2 := by
    calc
      (G.neighborFinset a.1 ∩ antipodalNeighbors G x).card ≤
          (antipodalNeighbors G x).card :=
        Finset.card_le_card Finset.inter_subset_right
      _ = 2 := hAntiCard
  omega

/-- **Uniform excess-one terminal.**  A regular `C₄`-free graph of order
`d(d-1)+4`, with `d ≥ 4`, cannot have a vertex with exactly three incident
triangle-free edges. -/
theorem false_of_excessOne_triangleFreeNeighbors_card_eq_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    (x : V) (hx : (triangleFreeNeighbors G x).card = 3) : False := by
  classical
  let N := G.neighborFinset x
  let H := G.induce (G.neighborSet x)
  have hlocalsum :
      (∑ y : {z : V // z ∈ G.neighborSet x}, H.degree y) = d - 3 := by
    have hsum := card_triangleFreeNeighbors_add_localDegreeSum_of_regular
      G hfree hreg x
    rw [hx] at hsum
    change (∑ y : {z : V // z ∈ G.neighborSet x}, H.degree y) = d - 3
    change 3 + (∑ y : {z : V // z ∈ G.neighborSet x}, H.degree y) = d at hsum
    omega
  have hhand := H.sum_degrees_eq_twice_card_edges
  have hodd : Odd d := by
    rw [hlocalsum] at hhand
    obtain ⟨k, hk⟩ : Even (d - 3) := by
      refine ⟨H.edgeFinset.card, ?_⟩
      omega
    exact ⟨k + 1, by omega⟩
  have hNcard : N.card = d := by
    simp only [N]
    rw [G.card_neighborFinset_eq_degree, hreg x]
  have hlt : (triangleFreeNeighbors G x).card < N.card := by
    rw [hx, hNcard]
    omega
  obtain ⟨u0, huN, huTF⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hlt
  let u : {z : V // z ∈ G.neighborSet x} := ⟨u0, by simpa [N] using huN⟩
  have huLocal : H.degree u = 1 := by
    have hle : H.degree u ≤ 1 := by
      change (G.induce (G.neighborSet x)).degree u ≤ 1
      rw [degree_induce_neighborSet_eq_card_common]
      exact common_le_one_of_not_containsC4 hfree x u.1 (G.ne_of_adj u.2)
    have hne : H.degree u ≠ 0 := by
      intro hz
      apply huTF
      rw [mem_triangleFreeNeighbors]
      refine ⟨u.2, ?_⟩
      change (G.induce (G.neighborSet x)).degree u = 0 at hz
      rw [degree_induce_neighborSet_eq_card_common] at hz
      exact hz
    omega
  have huNonempty : H.neighborFinset u |>.Nonempty := by
    rw [← Finset.card_pos, H.card_neighborFinset_eq_degree, huLocal]
    decide
  obtain ⟨v0, hv0⟩ := huNonempty
  let v : {z : V // z ∈ G.neighborSet x} := v0
  have huv : G.Adj u.1 v.1 := by
    simpa [H, SimpleGraph.mem_neighborFinset] using hv0
  have huv_ne : u ≠ v := by
    intro h
    exact (G.ne_of_adj huv) (congrArg Subtype.val h)
  let A := secondLayerBranch G x u
  have hAcard : A.card = d - 2 := by
    have hcardA := card_secondLayerBranch_eq_degree_sub_localDegree_sub_one
      G hreg x u
    rw [huLocal] at hcardA
    change A.card = d - 1 - 1 at hcardA
    omega
  have hAodd : Odd (Fintype.card A) := by
    rw [Fintype.card_coe, hAcard]
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k - 1, by omega⟩
  let K := G.induce A
  have hKle : ∀ a : A, K.degree a ≤ 1 := by
    intro a
    exact degree_induce_secondLayerBranch_le_one G hfree x u a
  obtain ⟨a, haIso⟩ :=
    exists_degree_eq_zero_of_odd_card_of_degree_le_one K hAodd hKle
  let B := (G.neighborFinset a.1).erase u.1
  have hua : G.Adj u.1 a.1 :=
    (G.mem_neighborFinset u.1 a.1).mp (Finset.mem_sdiff.mp a.2).1
  have huMem : u.1 ∈ G.neighborFinset a.1 :=
    (G.mem_neighborFinset a.1 u.1).mpr hua.symm
  have hBcard : B.card = d - 1 := by
    simp only [B]
    rw [Finset.card_erase_of_mem huMem,
      G.card_neighborFinset_eq_degree, hreg a.1]
  have hlayer := excessOne_secondLayer_eq_outsideClosedNeighborhood
    G hfree hreg hcard x hx
  have hroot : ∀ b, b ∈ B →
      ∃ r : {z : V // z ∈ G.neighborSet x},
        b ∈ secondLayerBranch G x r := by
    intro b hb
    have hab : G.Adj a.1 b :=
      (G.mem_neighborFinset a.1 b).mp (Finset.mem_erase.mp hb).2
    have hbu : b ≠ u.1 := (Finset.mem_erase.mp hb).1
    have hbOut : b ∈ outsideClosedNeighborhood G x := by
      simp only [outsideClosedNeighborhood, Finset.mem_filter]
      refine ⟨Finset.mem_univ b, ?_, ?_⟩
      · intro hbx
        subst b
        have hnax : ¬ G.Adj x a.1 := by
          intro hxa
          exact (Finset.mem_sdiff.mp a.2).2
            (Finset.mem_insert.mpr (Or.inr
              ((G.mem_neighborFinset x a.1).mpr hxa)))
        exact hnax hab.symm
      · intro hbx
        have hxu : G.Adj x u.1 := u.2
        have hxa : x ≠ a.1 := by
          intro h
          have hax : a.1 = x := h.symm
          exact (Finset.mem_sdiff.mp a.2).2
            (Finset.mem_insert.mpr (Or.inl hax))
        exact hfree (containsC4_of_two_common
          (x := x) (y := a.1) (v := u.1) (v' := b)
          hxa hbu.symm hxu.symm hua hbx hab.symm)
    rw [← hlayer, secondLayer, Finset.mem_biUnion] at hbOut
    obtain ⟨r, _, hr⟩ := hbOut
    exact ⟨r, hr⟩
  let root : B → {z : V // z ∈ G.neighborSet x} := fun b =>
    Classical.choose (hroot b.1 b.2)
  have hrootMem : ∀ b : B, b.1 ∈ secondLayerBranch G x (root b) := by
    intro b
    exact Classical.choose_spec (hroot b.1 b.2)
  have hroot_ne_u : ∀ b : B, root b ≠ u := by
    intro b hru
    have hbA : b.1 ∈ A := by simpa [A, hru] using hrootMem b
    have habK : K.Adj a ⟨b.1, hbA⟩ := by
      change G.Adj a.1 b.1
      exact (G.mem_neighborFinset a.1 b.1).mp
        (Finset.mem_erase.mp b.2).2
    have hbK : (⟨b.1, hbA⟩ : A) ∈ K.neighborFinset a :=
      (K.mem_neighborFinset a _).mpr habK
    have : K.neighborFinset a = ∅ := by
      apply Finset.card_eq_zero.mp
      rwa [K.card_neighborFinset_eq_degree]
    rw [this] at hbK
    exact Finset.notMem_empty _ hbK
  have hroot_ne_v : ∀ b : B, root b ≠ v := by
    intro b hrv
    have hbV : b.1 ∈ secondLayerBranch G x v := by
      simpa [hrv] using hrootMem b
    have hab : G.Adj a.1 b.1 :=
      (G.mem_neighborFinset a.1 b.1).mp (Finset.mem_erase.mp b.2).2
    exact (not_adj_between_secondLayerBranches_of_adj_roots
      G hfree x u v huv a ⟨b.1, hbV⟩) hab
  have hrootInj : Function.Injective root := by
    intro b c hbc
    apply Subtype.ext
    by_contra hbval
    have htwo : 2 ≤
        (G.neighborFinset a.1 ∩ secondLayerBranch G x (root b)).card := by
      have hcMem : c.1 ∈ secondLayerBranch G x (root b) := by
        rw [hbc]
        exact hrootMem c
      have hsub : ({b.1, c.1} : Finset V) ⊆
          G.neighborFinset a.1 ∩ secondLayerBranch G x (root b) := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_inter.mpr
            ⟨(Finset.mem_erase.mp b.2).2, hrootMem b⟩
        · exact Finset.mem_inter.mpr
            ⟨(Finset.mem_erase.mp c.2).2, hcMem⟩
      have hpair : ({b.1, c.1} : Finset V).card = 2 := by
        simp [hbval]
      rw [← hpair]
      exact Finset.card_le_card hsub
    have hroot_ne_a : a.1 ≠ (root b).1 := by
      intro h
      have haN : a.1 ∈ G.neighborFinset x := by
        rw [h]
        exact (G.mem_neighborFinset x (root b).1).mpr (root b).2
      exact (Finset.mem_sdiff.mp a.2).2
        (Finset.mem_insert.mpr (Or.inr haN))
    have hone := card_neighborFinset_inter_secondLayerBranch_le_one
      G hfree x a.1 (root b) hroot_ne_a
    omega
  let target := (Finset.univ.erase u).erase v
  let root' : B → target := fun b => ⟨root b, by
    simp only [target, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨hroot_ne_v b, hroot_ne_u b⟩⟩
  have hroot'Inj : Function.Injective root' := by
    intro b c h
    apply hrootInj
    exact congrArg Subtype.val h
  have hlecard : Fintype.card B ≤ Fintype.card target :=
    Fintype.card_le_of_injective root' hroot'Inj
  have htargetcard : Fintype.card target = d - 2 := by
    simp only [target, Fintype.card_coe]
    rw [Finset.card_erase_of_mem]
    · rw [Finset.card_erase_of_mem (Finset.mem_univ u),
        Finset.card_univ, Fintype.card_subtype]
      have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet x) = N := by
        ext z
        simp [N]
      rw [heq, hNcard]
      omega
    · exact Finset.mem_erase.mpr ⟨huv_ne.symm, Finset.mem_univ v⟩
  rw [Fintype.card_coe, hBcard, htargetcard] at hlecard
  omega

/-- There is no regular `C₄`-free excess-one graph in the congruence class
`d ≡ 3 (mod 6)` once `d ≥ 4`. -/
theorem no_c4Free_regular_excessOne_of_degree_mod_six_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hmod : d % 6 = 3) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) : False := by
  obtain ⟨x, hx⟩ := exists_excessOne_triangleFreeNeighbors_card_eq_three
    G hfree hmod hreg hcard
  exact false_of_excessOne_triangleFreeNeighbors_card_eq_three
    G hfree hd hreg hcard x hx

/-- Minimum-degree form of the uniform excess-one obstruction.  The Moore
layer bound first forces regularity, after which the preceding theorem
applies. -/
theorem no_c4Free_minDegree_excessOne_of_degree_mod_six_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hmod : d % 6 = 3) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 4) : False := by
  have hd9 : 9 ≤ d := by omega
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    have hid : (d + 1) * (d - 1) + 1 = d * (d - 1) + d := by
      calc
        (d + 1) * (d - 1) + 1 = d * (d - 1) + ((d - 1) + 1) := by ring
        _ = d * (d - 1) + d := by rw [Nat.sub_add_cancel (by omega)]
    rw [hid]
    omega
  have hreg : ∀ x, G.degree x = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by omega) hmin hbelow
  exact no_c4Free_regular_excessOne_of_degree_mod_six_three
    G hfree hd hmod hreg hcard

/-- Without any congruence condition, odd-degree excess-one graphs have
exactly one triangle-free incident edge at every vertex.  The alternative
value three is excluded by the exceptional-vertex terminal. -/
theorem excessOne_triangleFreeNeighbors_card_eq_one_of_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) (x : V) :
    (triangleFreeNeighbors G x).card = 1 := by
  rcases excessOne_triangleFreeNeighbors_card_eq_one_or_three
      G hfree hodd hreg hcard x with hx | hx
  · exact hx
  · exact (false_of_excessOne_triangleFreeNeighbors_card_eq_three
      G hfree hd hreg hcard x hx).elim

/-- Operator-facing form: the triangle-free-edge color is one-regular, hence
a perfect matching, in every odd-degree excess-one graph. -/
theorem triangleFreeEdgeGraph_degree_eq_one_of_odd_excessOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) (x : V) :
    (triangleFreeEdgeGraph G).degree x = 1 := by
  rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
    triangleFreeEdgeGraph_neighborFinset]
  exact excessOne_triangleFreeNeighbors_card_eq_one_of_odd
    G hfree hd hodd hreg hcard x

/-- The complementary antipodal color is two-regular.  Thus every odd-degree
excess-one defect graph canonically splits as a 2-factor plus a perfect
matching. -/
theorem antipodalGraph_degree_eq_two_of_odd_excessOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) (x : V) :
    (antipodalGraph G).degree x = 2 := by
  have hD := secondOrderDefectGraph_degree_eq_excess_add_two
    G hfree hreg (e := 1) (by simpa using hcard) x
  have hT := excessOne_triangleFreeNeighbors_card_eq_one_of_odd
    G hfree hd hodd hreg hcard x
  rw [← (antipodalGraph G).card_neighborFinset_eq_degree,
    antipodalGraph_neighborFinset]
  rw [← (secondOrderDefectGraph G).card_neighborFinset_eq_degree,
    secondOrderDefectGraph_neighborFinset,
    Finset.card_union_of_disjoint
      (disjoint_antipodal_triangleFreeNeighbors G x)] at hD
  omega

end

end Erdos85
