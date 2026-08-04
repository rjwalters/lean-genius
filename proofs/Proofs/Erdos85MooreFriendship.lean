import Proofs.Erdos85DistanceLayers
import Proofs.FriendshipTheoremOQ01

/-!
# Equality in the C4 Moore bound forces a friendship graph

At order `d(d-1)+1`, the asymmetric Moore bound first forces regularity.
Exact distance-layer accounting then forces every adjacent pair to have one
common neighbor and leaves no vertex beyond distance two.  C4-freeness makes
the common neighbor unique for nonadjacent pairs as well.  The axiom-free
Friendship Theorem already formalized in this repository then forces `d=2`.
-/

open SimpleGraph

namespace Erdos85

/-- At exact Moore order there is no vertex beyond distance two from any
chosen center. -/
theorem externalRepairCandidates_eq_empty_of_moore
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 2 ≤ d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 1)
    (x : V) :
    externalRepairCandidates G x = ∅ := by
  have hreg : ∀ v : V, G.degree v = d :=
    regular_of_minDegree_mooreOrder G hfree hd hmin hcard
  have hid := card_external_add_degree_sq_add_one_eq_card_add_localDegreeSum
    G hfree hreg x
  have hlocal := sum_localNeighborhood_degrees_le_degree G hfree x
  rw [hreg x] at hlocal
  rw [hcard] at hid
  have hsq : d * d = d * (d - 1) + d := by
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 2 := ⟨d - 2, by omega⟩
    norm_num
    ring
  have hzero : (externalRepairCandidates G x).card = 0 := by
    rw [hsq] at hid
    omega
  exact Finset.card_eq_zero.mp hzero

/-- Equality also forces the graph induced by every neighborhood to be
one-regular: each adjacent pair has exactly one common neighbor. -/
theorem localNeighborhood_degree_eq_one_of_moore
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 2 ≤ d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 1)
    (x : V) (y : {z : V // z ∈ G.neighborSet x}) :
    (G.induce (G.neighborSet x)).degree y = 1 := by
  classical
  have hreg : ∀ v : V, G.degree v = d :=
    regular_of_minDegree_mooreOrder G hfree hd hmin hcard
  let S := ∑ z : {w : V // w ∈ G.neighborSet x},
    (G.induce (G.neighborSet x)).degree z
  have hid := card_external_add_degree_sq_add_one_eq_card_add_localDegreeSum
    G hfree hreg x
  have hlocal := sum_localNeighborhood_degrees_le_degree G hfree x
  rw [hreg x] at hlocal
  rw [hcard] at hid
  have hsq : d * d = d * (d - 1) + d := by
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 2 := ⟨d - 2, by omega⟩
    norm_num
    ring
  have hext := externalRepairCandidates_eq_empty_of_moore
    G hfree hd hmin hcard x
  have hSeq : S = d := by
    rw [hext] at hid
    simp only [Finset.card_empty, zero_add] at hid
    change S ≤ d at hlocal
    change d * d + 1 = d * (d - 1) + 1 + S at hid
    rw [hsq] at hid
    omega
  have hle : ∀ z : {w : V // w ∈ G.neighborSet x},
      (G.induce (G.neighborSet x)).degree z ≤ 1 := by
    intro z
    rw [degree_induce_neighborSet_eq_card_common]
    exact common_le_one_of_not_containsC4 hfree x z.1 (G.ne_of_adj z.2)
  by_contra hy
  have hley := hle y
  have hylt : (G.induce (G.neighborSet x)).degree y < 1 := by omega
  have hsumlt : S < ∑ _z : {w : V // w ∈ G.neighborSet x}, 1 := by
    change (∑ z : {w : V // w ∈ G.neighborSet x},
      (G.induce (G.neighborSet x)).degree z) < _
    apply Finset.sum_lt_sum
    · intro z _
      exact hle z
    · exact ⟨y, Finset.mem_univ _, hylt⟩
  have hNcard : Fintype.card {w : V // w ∈ G.neighborSet x} = d := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet x) =
        G.neighborFinset x := by ext z; simp
    rw [heq, G.card_neighborFinset_eq_degree, hreg x]
  have hsumones : (∑ _z : {w : V // w ∈ G.neighborSet x}, 1) = d := by
    rw [Finset.sum_const, Finset.card_univ, hNcard]
    simp
  rw [hsumones, hSeq] at hsumlt
  omega

/-- Equality in the Moore bound makes the graph a friendship graph: every
distinct pair has exactly one common neighbor. -/
theorem isFriendshipGraph_of_c4Free_minDegree_mooreOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 2 ≤ d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 1) :
    FriendshipTheoremOQ01.IsFriendshipGraph G := by
  intro u v huv
  have hupper := common_le_one_of_not_containsC4 hfree u v huv
  have hlower : 1 ≤ (G.neighborFinset u ∩ G.neighborFinset v).card := by
    by_cases huvAdj : G.Adj u v
    · let y : {z : V // z ∈ G.neighborSet u} := ⟨v, huvAdj⟩
      have hy := localNeighborhood_degree_eq_one_of_moore
        G hfree hd hmin hcard u y
      rw [degree_induce_neighborSet_eq_card_common] at hy
      exact hy.ge
    · have hext := externalRepairCandidates_eq_empty_of_moore
        G hfree hd hmin hcard u
      have hvu : v ≠ u := Ne.symm huv
      let a : {z : V // z ≠ u} := ⟨v, hvu⟩
      by_contra hzero
      have hinter : G.neighborFinset u ∩ G.neighborFinset v = ∅ :=
        Finset.card_eq_zero.mp (by omega)
      have ha : a ∈ externalRepairCandidates G u := by
        rw [mem_externalRepairCandidates]
        refine ⟨(fun hva => huvAdj hva.symm), ?_⟩
        intro b hbu hbva
        have hbmem : b.1 ∈ G.neighborFinset u ∩ G.neighborFinset v :=
          Finset.mem_inter.mpr ⟨
            (G.mem_neighborFinset u b.1).mpr hbu.symm,
            (G.mem_neighborFinset v b.1).mpr hbva⟩
        rw [hinter] at hbmem
        exact Finset.notMem_empty _ hbmem
      rw [hext] at ha
      exact Finset.notMem_empty _ ha
  have hcardOne : (G.neighborFinset u ∩ G.neighborFinset v).card = 1 :=
    le_antisymm hupper hlower
  have hset : G.commonNeighbors u v =
      ↑(G.neighborFinset u ∩ G.neighborFinset v) := by
    ext z
    simp [SimpleGraph.mem_commonNeighbors, SimpleGraph.mem_neighborFinset]
  rw [hset, Set.ncard_coe_finset, hcardOne]

/-- **Strict C4 Moore bound for every degree above two.**  Exact order
`d(d-1)+1` would be a regular friendship graph, while the axiom-free
Friendship Theorem forces every such graph of degree at least two to have
degree exactly two. -/
theorem containsC4_of_minDegree_mooreOrder_of_three_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : 3 ≤ d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 1) :
    containsC4 V G := by
  by_contra hfree
  letI : Nonempty V := Fintype.card_pos_iff.mp (by rw [hcard]; positivity)
  have hreg : ∀ v : V, G.degree v = d :=
    regular_of_minDegree_mooreOrder G hfree (by omega) hmin hcard
  have hfriend := isFriendshipGraph_of_c4Free_minDegree_mooreOrder
    G hfree (by omega) hmin hcard
  let u : V := Classical.choice (inferInstance : Nonempty V)
  have hd2 := FriendshipTheoremOQ01.k_eq_two_no_axiom
    G hfriend u d (by omega) hreg
  omega

/-- Numerical strict Moore bound: every nonempty C4-free graph of minimum
degree at least `d≥3` has at least `d(d-1)+2` vertices. -/
theorem mul_pred_add_two_le_card_of_c4Free_minDegree
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : 3 ≤ d)
    (hmin : d ≤ G.minDegree)
    (hfree : ¬ containsC4 V G) :
    d * (d - 1) + 2 ≤ Fintype.card V := by
  let x : V := Classical.choice (inferInstance : Nonempty V)
  have hdx : d ≤ G.degree x := hmin.trans (G.minDegree_le_degree x)
  have hbound := one_add_degree_add_mul_sub_two_le_card_of_minDegree
    G hfree hmin x
  have hrewrite :
      1 + G.degree x + G.degree x * (d - 2) =
        1 + G.degree x * (d - 1) := by
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 3 := ⟨d - 3, by omega⟩
    have hsub2 : e + 3 - 2 = e + 1 := by omega
    have hsub1 : e + 3 - 1 = e + 2 := by omega
    rw [hsub2, hsub1]
    ring
  have hmul := Nat.mul_le_mul_right (d - 1) hdx
  have hbase : d * (d - 1) + 1 ≤ Fintype.card V := by
    rw [hrewrite] at hbound
    omega
  have hne : Fintype.card V ≠ d * (d - 1) + 1 := by
    intro heq
    exact hfree (containsC4_of_minDegree_mooreOrder_of_three_le
      G hd hmin heq)
  omega

/-- Threshold form of the strict Moore bound.  This improves the elementary
cherry-counting upper bound by one order at every `d≥3`, including even `d`. -/
theorem minDegreeForC4_mooreOrder_le {d : ℕ} (hd : 3 ≤ d) :
    minDegreeForC4 (d * (d - 1) + 1) ≤ d := by
  apply Nat.sInf_le
  intro G _ hmin
  exact containsC4_of_minDegree_mooreOrder_of_three_le
    G hd hmin (by simp)

/-! ## Stability at the first possible order

The strict bound leaves `d(d-1)+2` as the first order at which a C4-free
minimum-degree-`d` graph could exist.  This order is still below the next
asymmetric layer threshold, so near-Moore regularity applies.  Exact branch
accounting then leaves only one unit of slack: every center has at most one
vertex beyond distance two, and all but at most one of its neighbors are
paired inside its neighborhood.
-/

/-- Exact one-slack identity at the first order not excluded by the strict
Moore bound. -/
theorem card_external_add_degree_eq_one_add_localDegreeSum_of_firstOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2)
    (x : V) :
    (externalRepairCandidates G x).card + d =
      1 + ∑ y : {z : V // z ∈ G.neighborSet x},
        (G.induce (G.neighborSet x)).degree y := by
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 3 := ⟨d - 3, by omega⟩
    norm_num
    nlinarith
  have hreg : ∀ v : V, G.degree v = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by omega) hmin hbelow
  have hid := card_external_add_degree_sq_add_one_eq_card_add_localDegreeSum
    G hfree hreg x
  rw [hcard] at hid
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 3 := ⟨d - 3, by omega⟩
  norm_num at hid ⊢
  nlinarith

/-- At the first possible order, each center has at most one external vertex,
and at most one isolated vertex in its induced neighborhood. -/
theorem firstOrder_external_le_one_and_localDegreeSum_large
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2)
    (x : V) :
    (externalRepairCandidates G x).card ≤ 1 ∧
      d - 1 ≤ ∑ y : {z : V // z ∈ G.neighborSet x},
        (G.induce (G.neighborSet x)).degree y := by
  have hid := card_external_add_degree_eq_one_add_localDegreeSum_of_firstOrder
    G hfree hd hmin hcard x
  have hlocal := sum_localNeighborhood_degrees_le_degree G hfree x
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 3 := ⟨d - 3, by omega⟩
    norm_num
    nlinarith
  have hdeg := degree_eq_of_minDegree_card_lt_nextMooreLayer
    G hfree (by omega) hmin hbelow x
  rw [hdeg] at hlocal
  omega

/-- For even `d`, the unique unit of first-order slack is an external vertex:
every induced neighborhood is a perfect matching and there is exactly one
vertex beyond distance two from the center. -/
theorem firstOrder_structure_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d) (hdeven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2)
    (x : V) :
    (externalRepairCandidates G x).card = 1 ∧
      (∑ y : {z : V // z ∈ G.neighborSet x},
        (G.induce (G.neighborSet x)).degree y) = d := by
  let S := ∑ y : {z : V // z ∈ G.neighborSet x},
    (G.induce (G.neighborSet x)).degree y
  have hid := card_external_add_degree_eq_one_add_localDegreeSum_of_firstOrder
    G hfree hd hmin hcard x
  have hbounds := firstOrder_external_le_one_and_localDegreeSum_large
    G hfree hd hmin hcard x
  have hSeven : Even S := by
    change Even (∑ y : {z : V // z ∈ G.neighborSet x},
      (G.induce (G.neighborSet x)).degree y)
    rw [(G.induce (G.neighborSet x)).sum_degrees_eq_twice_card_edges]
    exact even_two_mul _
  change (externalRepairCandidates G x).card + d = 1 + S at hid
  change (externalRepairCandidates G x).card ≤ 1 ∧ d - 1 ≤ S at hbounds
  change (externalRepairCandidates G x).card = 1 ∧ S = d
  rw [Nat.even_iff] at hdeven hSeven
  omega

/-- For odd `d`, the unique unit of first-order slack is the isolated vertex
in each induced neighborhood; there is no vertex beyond distance two. -/
theorem firstOrder_structure_of_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d) (hdodd : Odd d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2)
    (x : V) :
    (externalRepairCandidates G x).card = 0 ∧
      (∑ y : {z : V // z ∈ G.neighborSet x},
        (G.induce (G.neighborSet x)).degree y) = d - 1 := by
  let S := ∑ y : {z : V // z ∈ G.neighborSet x},
    (G.induce (G.neighborSet x)).degree y
  have hid := card_external_add_degree_eq_one_add_localDegreeSum_of_firstOrder
    G hfree hd hmin hcard x
  have hbounds := firstOrder_external_le_one_and_localDegreeSum_large
    G hfree hd hmin hcard x
  have hSeven : Even S := by
    change Even (∑ y : {z : V // z ∈ G.neighborSet x},
      (G.induce (G.neighborSet x)).degree y)
    rw [(G.induce (G.neighborSet x)).sum_degrees_eq_twice_card_edges]
    exact even_two_mul _
  change (externalRepairCandidates G x).card + d = 1 + S at hid
  change (externalRepairCandidates G x).card ≤ 1 ∧ d - 1 ≤ S at hbounds
  change (externalRepairCandidates G x).card = 0 ∧ S = d - 1
  rw [Nat.odd_iff] at hdodd
  rw [Nat.even_iff] at hSeven
  omega

/-- Neighbors of `x` whose edge to `x` lies in no triangle.  In a C4-free
graph these are exactly the isolated vertices of the graph induced by
`N(x)`. -/
def triangleFreeNeighborIndices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    Finset {z : V // z ∈ G.neighborSet x} :=
  Finset.univ.filter fun y =>
    (G.induce (G.neighborSet x)).degree y = 0

/-- Vertex-level version of `triangleFreeNeighborIndices`. -/
def triangleFreeNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : Finset V :=
  (triangleFreeNeighborIndices G x).map
    ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem mem_triangleFreeNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    y ∈ triangleFreeNeighbors G x ↔
      G.Adj x y ∧
        (G.neighborFinset x ∩ G.neighborFinset y).card = 0 := by
  constructor
  · intro hy
    rw [triangleFreeNeighbors, Finset.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hz0 : (G.induce (G.neighborSet x)).degree z = 0 := by
      simpa [triangleFreeNeighborIndices] using hz
    rw [degree_induce_neighborSet_eq_card_common] at hz0
    exact ⟨z.2, hz0⟩
  · rintro ⟨hxy, hcommon⟩
    let z : {w : V // w ∈ G.neighborSet x} := ⟨y, hxy⟩
    rw [triangleFreeNeighbors, Finset.mem_map]
    refine ⟨z, ?_, rfl⟩
    simp only [triangleFreeNeighborIndices, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [degree_induce_neighborSet_eq_card_common]
    exact hcommon

/-- Being joined by a triangle-free edge is symmetric. -/
theorem mem_triangleFreeNeighbors_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    y ∈ triangleFreeNeighbors G x ↔ x ∈ triangleFreeNeighbors G y := by
  rw [mem_triangleFreeNeighbors, mem_triangleFreeNeighbors]
  constructor
  · rintro ⟨hxy, hzero⟩
    exact ⟨hxy.symm, by simpa [Finset.inter_comm] using hzero⟩
  · rintro ⟨hyx, hzero⟩
    exact ⟨hyx.symm, by simpa [Finset.inter_comm] using hzero⟩

/-- In the odd first-order template every vertex is incident with exactly one
triangle-free edge. -/
theorem card_triangleFreeNeighborIndices_eq_one_of_firstOrder_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d) (hdodd : Odd d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2)
    (x : V) :
    (triangleFreeNeighborIndices G x).card = 1 := by
  classical
  let H := G.induce (G.neighborSet x)
  let S := ∑ y : {z : V // z ∈ G.neighborSet x}, H.degree y
  have hstructure := firstOrder_structure_of_odd
    G hfree hd hdodd hmin hcard x
  have hS : S = d - 1 := hstructure.2
  have hle : ∀ y : {z : V // z ∈ G.neighborSet x}, H.degree y ≤ 1 := by
    intro y
    change (G.induce (G.neighborSet x)).degree y ≤ 1
    rw [degree_induce_neighborSet_eq_card_common]
    exact common_le_one_of_not_containsC4 hfree x y.1 (G.ne_of_adj y.2)
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 3 := ⟨d - 3, by omega⟩
    norm_num
    nlinarith
  have hdeg := degree_eq_of_minDegree_card_lt_nextMooreLayer
    G hfree (by omega) hmin hbelow x
  have hNcard : Fintype.card {z : V // z ∈ G.neighborSet x} = d := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet x) =
        G.neighborFinset x := by ext z; simp
    rw [heq, G.card_neighborFinset_eq_degree, hdeg]
  have hnonzero : S =
      (Finset.univ.filter fun y : {z : V // z ∈ G.neighborSet x} =>
        H.degree y ≠ 0).card := by
    change (∑ y : {z : V // z ∈ G.neighborSet x}, H.degree y) = _
    calc
      (∑ y : {z : V // z ∈ G.neighborSet x}, H.degree y) =
          (∑ y : {z : V // z ∈ G.neighborSet x},
            if H.degree y ≠ 0 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro y _
        have hyLe := hle y
        split_ifs with hy
        · omega
        · omega
      _ = _ := by simpa using
        (Finset.sum_boole (R := ℕ)
          (fun y : {z : V // z ∈ G.neighborSet x} => H.degree y ≠ 0)
          Finset.univ)
  have hpartition := Finset.card_filter_add_card_filter_not
    (fun y : {z : V // z ∈ G.neighborSet x} => H.degree y = 0)
    (s := Finset.univ)
  have hnonzeroCard :
      (Finset.univ.filter fun y : {z : V // z ∈ G.neighborSet x} =>
        H.degree y ≠ 0).card = d - 1 := hnonzero.symm.trans hS
  have hisolated :
      (Finset.univ.filter fun y : {z : V // z ∈ G.neighborSet x} =>
        H.degree y = 0).card = 1 := by
    simp only [Finset.card_univ, hNcard] at hpartition
    have hnot : (Finset.univ.filter fun y : {z : V // z ∈ G.neighborSet x} =>
        ¬H.degree y = 0) =
        Finset.univ.filter fun y => H.degree y ≠ 0 := by
      ext y
      simp
    rw [hnot] at hpartition
    rw [hnonzeroCard] at hpartition
    omega
  simpa [triangleFreeNeighborIndices, H] using hisolated

/-- Vertex-level form: the triangle-free edges constitute a one-regular
spanning subgraph in the odd first-order template. -/
theorem card_triangleFreeNeighbors_eq_one_of_firstOrder_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d) (hdodd : Odd d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2)
    (x : V) :
    (triangleFreeNeighbors G x).card = 1 := by
  rw [triangleFreeNeighbors, Finset.card_map]
  exact card_triangleFreeNeighborIndices_eq_one_of_firstOrder_odd
    G hfree hd hdodd hmin hcard x

end Erdos85
