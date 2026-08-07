import Proofs.Erdos85OrderFortyNineOddIncidence

/-!
# Pairwise-balanced-design classification of the high sector

At order 49, the high-neighbor supports of low vertices form a linear
pairwise-balanced design on the high vertices.  Every pair of highs has a
unique common low witness, whose support has size two or three; distinct
three-supports meet in at most one high; and, at nine highs, singleton
multiplicity equals triple multiplicity pointwise.

These are the graph-facing reduction lemmas used to turn the final `h=9`
profiles into finite linear triple systems.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The block of high vertices incident with a vertex. -/
def orderFortyNineHighSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : Finset V :=
  G.neighborFinset x ∩ orderFortyNineHighVertices G

/-- Every pair of distinct high vertices has a unique common witness, and
that witness is low with high-support size two or three. -/
theorem orderFortyNine_existsUnique_pairBlock_of_highs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {a b : V}
    (ha : a ∈ orderFortyNineHighVertices G)
    (hb : b ∈ orderFortyNineHighVertices G) (hab : a ≠ b) :
    ∃! x, G.Adj a x ∧ G.Adj b x ∧ G.degree x = 7 ∧
      ((orderFortyNineHighSupport G x).card = 2 ∨
       (orderFortyNineHighSupport G x).card = 3) := by
  have ha8 : G.degree a = 8 := (Finset.mem_filter.mp ha).2
  have hb8 : G.degree b = 8 := (Finset.mem_filter.mp hb).2
  have hcommon := orderFortyNine_card_common_degreeEight_eq_one
    G hfree hmin hcard ha8 hb8 hab
  rcases Finset.card_eq_one.mp hcommon with ⟨x, hx⟩
  have hxmem : x ∈ G.neighborFinset a ∩ G.neighborFinset b := by
    simp [hx]
  have hax : G.Adj a x := by
    simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hxmem).1
  have hbx : G.Adj b x := by
    simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hxmem).2
  have hx7 := orderFortyNine_neighbor_degree_seven_of_degreeEight
    G hfree hmin hcard ha8 hax
  have htwo : 2 ≤ (orderFortyNineHighSupport G x).card := by
    have haMem : a ∈ orderFortyNineHighSupport G x := by
      simp [orderFortyNineHighSupport, SimpleGraph.mem_neighborFinset,
        G.adj_comm, hax, ha]
    have hbMem : b ∈ orderFortyNineHighSupport G x := by
      simp [orderFortyNineHighSupport, SimpleGraph.mem_neighborFinset,
        G.adj_comm, hbx, hb]
    have hpair : ({a, b} : Finset V) ⊆ orderFortyNineHighSupport G x := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact haMem
      · exact hbMem
    calc
      2 = ({a, b} : Finset V).card := by simp [hab]
      _ ≤ (orderFortyNineHighSupport G x).card := Finset.card_le_card hpair
  have hthree : (orderFortyNineHighSupport G x).card ≤ 3 := by
    simpa [orderFortyNineHighSupport] using
      orderFortyNine_highNeighborCount_le_three G hfree hmin hcard hx7
  refine ⟨x, ⟨hax, hbx, hx7, by omega⟩, ?_⟩
  intro y hy
  have hymem : y ∈ G.neighborFinset a ∩ G.neighborFinset b := by
    simp [SimpleGraph.mem_neighborFinset, hy.1, hy.2.1]
  simpa [hx] using hymem

/-- The high supports of two distinct low vertices meet in at most one
point.  In particular, the size-three blocks form a linear triple system. -/
theorem orderFortyNine_card_inter_highSupport_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {x y : V} (hxy : x ≠ y) :
    ((orderFortyNineHighSupport G x) ∩
      orderFortyNineHighSupport G y).card ≤ 1 := by
  have hsub : (orderFortyNineHighSupport G x ∩
      orderFortyNineHighSupport G y) ⊆
      (G.neighborFinset x ∩ G.neighborFinset y) := by
    intro w hw
    have hwx := Finset.mem_inter.mp hw
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hwx.1).1, (Finset.mem_inter.mp hwx.2).1⟩
  exact le_trans (Finset.card_le_card hsub)
    (common_le_one_of_not_containsC4 hfree x y hxy)

/-- Two distinct size-three blocks cannot contain the same high pair. -/
theorem orderFortyNine_tripleBlocks_pairwise_linear
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {x y : V} (hxy : x ≠ y)
    (_hx3 : (orderFortyNineHighSupport G x).card = 3)
    (_hy3 : (orderFortyNineHighSupport G y).card = 3) :
    ((orderFortyNineHighSupport G x) ∩
      orderFortyNineHighSupport G y).card ≤ 1 :=
  orderFortyNine_card_inter_highSupport_le_one G hfree hxy

/-- At nine highs, the number of singleton blocks through a high point is
exactly the number of triple blocks through it. -/
theorem orderFortyNine_singletonMultiplicity_eq_tripleMultiplicity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    {v : V} (hv : v ∈ orderFortyNineHighVertices G) :
    ((G.neighborFinset v).filter fun x =>
      (orderFortyNineHighSupport G x).card = 1).card =
    ((G.neighborFinset v).filter fun x =>
      (orderFortyNineHighSupport G x).card = 3).card := by
  have hv8 : G.degree v = 8 := (Finset.mem_filter.mp hv).2
  simpa [orderFortyNineHighSupport] using
    orderFortyNine_highNeighborhood_count_one_eq_count_three
      G hfree hmin hcard hHigh hv8

/-- Three pairwise-linear triples cannot be supported on only five points.
This is the structural obstruction that removes the apparent three-triple
profile in the `h=5` stratum, without enumerating triple systems. -/
theorem not_three_pairwise_linear_triples_of_card_five
    {α : Type*} [DecidableEq α] (H A B C : Finset α)
    (hH : H.card = 5)
    (hAH : A ⊆ H) (hBH : B ⊆ H) (hCH : C ⊆ H)
    (hA : A.card = 3) (hB : B.card = 3) (hC : C.card = 3)
    (hAB : (A ∩ B).card ≤ 1)
    (hAC : (A ∩ C).card ≤ 1)
    (hBC : (B ∩ C).card ≤ 1) : False := by
  have hUnionSub : A ∪ B ⊆ H := Finset.union_subset hAH hBH
  have hUnionGe : 5 ≤ (A ∪ B).card := by
    have hcount := Finset.card_union_add_card_inter A B
    omega
  have hUnionLe : (A ∪ B).card ≤ 5 := by
    rw [← hH]
    exact Finset.card_le_card hUnionSub
  have hUnionEq : A ∪ B = H := by
    apply Finset.eq_of_subset_of_card_le hUnionSub
    rw [hH]
    exact hUnionGe
  have hCeq : C = C ∩ (A ∪ B) := by
    rw [hUnionEq]
    ext x
    simp only [Finset.mem_inter]
    exact ⟨fun hx => ⟨hx, hCH hx⟩, fun hx => hx.1⟩
  have hsplit : C ∩ (A ∪ B) = (C ∩ A) ∪ (C ∩ B) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have hcardLe : C.card ≤ (C ∩ A).card + (C ∩ B).card := by
    calc
      C.card = ((C ∩ A) ∪ (C ∩ B)).card :=
        congrArg Finset.card (hCeq.trans hsplit)
      _ ≤ (C ∩ A).card + (C ∩ B).card :=
        Finset.card_union_le (C ∩ A) (C ∩ B)
  have hAC' : (C ∩ A).card ≤ 1 := by
    rw [Finset.inter_comm]
    exact hAC
  have hBC' : (C ∩ B).card ≤ 1 := by
    rw [Finset.inter_comm]
    exact hBC
  rw [hC] at hcardLe
  omega

end

end Erdos85
