import Proofs.Erdos85AntipodalCommutatorRows

/-!
# Claw structure of the triangle-free color at odd excess three

At odd excess three the triangle-free-edge graph `T` has local degree `1`
or `3` everywhere.  This file pins down the component geometry forced by
`C₄`-freeness of the ambient graph:

* `T` is itself triangle-free: a `T`-triangle would place a triangle-free
  original edge inside an original triangle;
* two triangle-free edges sharing an endpoint have far endpoints that are
  **nonadjacent in the original graph** and have that shared endpoint as
  their **unique** common original neighbor — a degree-three vertex is
  therefore the center of an induced claw `K_{1,3}`;
* together with `T`-`C₄`-freeness (inherited from `G`), `T` has girth at
  least five, and since no `T`-degree equals two, every vertex either
  spans an isolated `K₂` component with its unique partner or lies at
  `T`-distance at most one from a degree-three claw center.
-/

open SimpleGraph

namespace Erdos85

/-- A triangle-free original edge lies in no original triangle. -/
theorem not_adj_adj_of_triangleFreeEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y z : V} (hxy : (triangleFreeEdgeGraph G).Adj x y)
    (hxz : G.Adj x z) (hyz : G.Adj y z) : False := by
  have hzero : (G.neighborFinset x ∩ G.neighborFinset y).card = 0 :=
    ((mem_triangleFreeNeighbors G x y).mp
      ((triangleFreeEdgeGraph_adj G x y).mp hxy)).2
  have hzmem : z ∈ G.neighborFinset x ∩ G.neighborFinset y :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset x z).mpr hxz,
        (G.mem_neighborFinset y z).mpr hyz⟩
  rw [Finset.card_eq_zero.mp hzero] at hzmem
  exact Finset.notMem_empty z hzmem

/-- **The triangle-free color is triangle-free as a graph.**  Three
triangle-free edges cannot close a triangle. -/
theorem triangleFreeEdgeGraph_no_triangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y z : V} (hxy : (triangleFreeEdgeGraph G).Adj x y)
    (hyz : (triangleFreeEdgeGraph G).Adj y z)
    (hzx : (triangleFreeEdgeGraph G).Adj z x) : False := by
  have hGyz : G.Adj y z :=
    ((mem_triangleFreeNeighbors G y z).mp
      ((triangleFreeEdgeGraph_adj G y z).mp hyz)).1
  have hGxz : G.Adj x z :=
    ((mem_triangleFreeNeighbors G z x).mp
      ((triangleFreeEdgeGraph_adj G z x).mp hzx)).1.symm
  exact not_adj_adj_of_triangleFreeEdge G hxy hGxz hGyz

/-- **Claw legs are nonadjacent.**  The far endpoints of two triangle-free
edges through a common vertex are nonadjacent in the original graph. -/
theorem not_adj_legs_of_triangleFree_center
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y z : V} (hxy : (triangleFreeEdgeGraph G).Adj x y)
    (hxz : (triangleFreeEdgeGraph G).Adj x z) :
    ¬ G.Adj y z := by
  intro hyz
  have hGxz : G.Adj x z :=
    ((mem_triangleFreeNeighbors G x z).mp
      ((triangleFreeEdgeGraph_adj G x z).mp hxz)).1
  exact not_adj_adj_of_triangleFreeEdge G hxy hGxz hyz

/-- **Claw legs have a unique common neighbor.**  In a `C₄`-free graph the
far endpoints of two triangle-free edges through `x` have exactly `x` as
common original neighborhood. -/
theorem common_eq_singleton_of_triangleFree_center
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {x y z : V} (hxy : (triangleFreeEdgeGraph G).Adj x y)
    (hxz : (triangleFreeEdgeGraph G).Adj x z) (hyz : y ≠ z) :
    G.neighborFinset y ∩ G.neighborFinset z = {x} := by
  have hGxy : G.Adj x y :=
    ((mem_triangleFreeNeighbors G x y).mp
      ((triangleFreeEdgeGraph_adj G x y).mp hxy)).1
  have hGxz : G.Adj x z :=
    ((mem_triangleFreeNeighbors G x z).mp
      ((triangleFreeEdgeGraph_adj G x z).mp hxz)).1
  have hxmem : x ∈ G.neighborFinset y ∩ G.neighborFinset z :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset y x).mpr hGxy.symm,
        (G.mem_neighborFinset z x).mpr hGxz.symm⟩
  have hsub : ({x} : Finset V) ⊆
      G.neighborFinset y ∩ G.neighborFinset z := by
    intro w hw
    rw [Finset.mem_singleton] at hw
    subst w
    exact hxmem
  have hle : (G.neighborFinset y ∩ G.neighborFinset z).card ≤ 1 :=
    common_le_one_of_not_containsC4 hfree y z hyz
  have hcard : (G.neighborFinset y ∩ G.neighborFinset z).card ≤
      ({x} : Finset V).card := by
    rw [Finset.card_singleton]
    exact hle
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

/-- A vertex of triangle-free degree one has a unique partner. -/
theorem exists_unique_partner_of_triangleFreeDegree_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    {x : V} (hx : (triangleFreeEdgeGraph G).degree x = 1) :
    ∃ y : V, (triangleFreeEdgeGraph G).neighborFinset x = {y} := by
  have hcard : ((triangleFreeEdgeGraph G).neighborFinset x).card = 1 := by
    rw [(triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
    exact hx
  exact Finset.card_eq_one.mp hcard

/-- **Local component dichotomy at odd excess three.**  Every vertex either
spans an isolated `K₂` component of the triangle-free color together with
its unique partner, or lies at `T`-distance at most one from a claw center
of `T`-degree three. -/
theorem excessThree_K2_or_claw
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) (x : V) :
    (∃ y : V, (triangleFreeEdgeGraph G).neighborFinset x = {y} ∧
        (triangleFreeEdgeGraph G).neighborFinset y = {x}) ∨
      (∃ z : V, (z = x ∨ (triangleFreeEdgeGraph G).Adj x z) ∧
        (triangleFreeEdgeGraph G).degree z = 3) := by
  classical
  let T := triangleFreeEdgeGraph G
  have hdeg : ∀ w : V, T.degree w = 1 ∨ T.degree w = 3 := by
    intro w
    rw [← T.card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset]
    exact excessThree_triangleFreeNeighbors_card_eq_one_or_three_of_odd
      G hfree hd hodd hreg hcard w
  rcases hdeg x with hx | hx
  · obtain ⟨y, hy⟩ := exists_unique_partner_of_triangleFreeDegree_one G hx
    rcases hdeg y with hy1 | hy3
    · left
      refine ⟨y, hy, ?_⟩
      obtain ⟨w, hw⟩ := exists_unique_partner_of_triangleFreeDegree_one G hy1
      have hxy : T.Adj x y := by
        rw [← T.mem_neighborFinset, hy]
        exact Finset.mem_singleton_self y
      have hxmem : x ∈ T.neighborFinset y :=
        (T.mem_neighborFinset y x).mpr hxy.symm
      rw [hw] at hxmem
      rw [Finset.mem_singleton] at hxmem
      rw [hw, hxmem]
    · right
      refine ⟨y, Or.inr ?_, hy3⟩
      rw [← T.mem_neighborFinset, hy]
      exact Finset.mem_singleton_self y
  · right
    exact ⟨x, Or.inl rfl, hx⟩

/-- **Claw geometry at a degree-three vertex.**  At odd excess three every
degree-three vertex of the triangle-free color is the center of an induced
claw: its three legs are pairwise nonadjacent in the original graph and
pairwise have the center as unique common neighbor. -/
theorem excessThree_claw_of_triangleFreeDegree_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {x : V} (hx : (triangleFreeEdgeGraph G).degree x = 3) :
    ∃ p q r : V, p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      (triangleFreeEdgeGraph G).neighborFinset x = {p, q, r} ∧
      (¬ G.Adj p q ∧ ¬ G.Adj p r ∧ ¬ G.Adj q r) ∧
      G.neighborFinset p ∩ G.neighborFinset q = {x} ∧
      G.neighborFinset p ∩ G.neighborFinset r = {x} ∧
      G.neighborFinset q ∩ G.neighborFinset r = {x} := by
  classical
  have hcard : ((triangleFreeEdgeGraph G).neighborFinset x).card = 3 := by
    rw [(triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
    exact hx
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp hcard
  have hmem : ∀ w ∈ ({p, q, r} : Finset V),
      (triangleFreeEdgeGraph G).Adj x w := by
    intro w hw
    rw [← hset] at hw
    exact ((triangleFreeEdgeGraph G).mem_neighborFinset x w).mp hw
  have hp : (triangleFreeEdgeGraph G).Adj x p :=
    hmem p (by simp)
  have hq : (triangleFreeEdgeGraph G).Adj x q :=
    hmem q (by simp)
  have hr : (triangleFreeEdgeGraph G).Adj x r :=
    hmem r (by simp)
  exact ⟨p, q, r, hpq, hpr, hqr, hset,
    ⟨not_adj_legs_of_triangleFree_center G hp hq,
      not_adj_legs_of_triangleFree_center G hp hr,
      not_adj_legs_of_triangleFree_center G hq hr⟩,
    common_eq_singleton_of_triangleFree_center G hfree hp hq hpq,
    common_eq_singleton_of_triangleFree_center G hfree hp hr hpr,
    common_eq_singleton_of_triangleFree_center G hfree hq hr hqr⟩

end Erdos85
