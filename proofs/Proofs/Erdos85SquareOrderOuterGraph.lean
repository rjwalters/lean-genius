import Proofs.Erdos85BranchDeficitSymmetry

/-!
# The regular outer graph at a square-order high root

The second layer around a saturated degree-`d+1` root contains
`(d+1)(d-2)` vertices.  When all outer vertices have degree `d`, deleting
their unique parent leaves a `(d-1)`-regular induced graph on that layer.
For the order-49 unique-high sector this is the canonical 6-regular graph on
40 vertices underlying the branch-voltage and cage formulations.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The graph induced by the second layer around a root. -/
def squareOrderOuterGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    SimpleGraph {x : V // x ∈ secondLayer G v} :=
  G.induce (secondLayer G v)

instance squareOrderOuterGraph_decidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    DecidableRel (squareOrderOuterGraph G v).Adj :=
  fun a b => by
    change Decidable (G.Adj a.1 b.1)
    infer_instance

/-- Inducing on the second layer preserves `C4`-freeness. -/
theorem squareOrderOuterGraph_not_containsC4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    (hfree : ¬ containsC4 V G) :
    ¬ containsC4 {x : V // x ∈ secondLayer G v}
      (squareOrderOuterGraph G v) := by
  rintro ⟨f, hf, hadj⟩
  apply hfree
  exact ⟨fun i => (f i).1, Subtype.val_injective.comp hf,
    fun i j hij => hadj i j hij⟩

/-- Its vertex count at a saturated square-order high root. -/
theorem card_squareOrderOuterGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) {v : V}
    (hv : G.degree v = d + 1)
    (hneigh : ∀ y, G.Adj v y → G.degree y = d)
    (hlocal : ∀ s : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree s = 1) :
    Fintype.card {x : V // x ∈ secondLayer G v} = (d + 1) * (d - 2) := by
  rw [Fintype.card_subtype]
  have heq : Finset.univ.filter (fun x => x ∈ secondLayer G v) =
      secondLayer G v := by ext x; simp
  rw [heq]
  exact card_secondLayer_eq_mul_sub_two_of_squareOrder_highRoot
    G hfree hd hv hneigh hlocal

/-- The neighbours of an outer vertex inside the outer graph are exactly
its original neighbours lying in the second layer. -/
theorem squareOrderOuterGraph_degree_eq_card_inter
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    (a : {x : V // x ∈ secondLayer G v}) :
    (squareOrderOuterGraph G v).degree a =
      (G.neighborFinset a.1 ∩ secondLayer G v).card := by
  classical
  rw [← (squareOrderOuterGraph G v).card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun b _ => b.1)
  · intro b hb
    have hab : G.Adj a.1 b.1 :=
      ((squareOrderOuterGraph G v).mem_neighborFinset a b).mp hb
    exact Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset a.1 b.1).mpr hab, b.2⟩
  · intro b hb c hc hbc
    exact Subtype.ext hbc
  · intro b hb
    have hbAdj : G.Adj a.1 b :=
      (G.mem_neighborFinset a.1 b).mp (Finset.mem_inter.mp hb).1
    let b' : {x : V // x ∈ secondLayer G v} :=
      ⟨b, (Finset.mem_inter.mp hb).2⟩
    refine ⟨b', ?_, rfl⟩
    exact ((squareOrderOuterGraph G v).mem_neighborFinset a b').mpr hbAdj

/-- Intersecting an outer neighbourhood with the union of all high-root
branches has cardinality `d-1`. -/
theorem card_neighbors_inter_secondLayer_eq_sub_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} {v : V}
    (hexternal : externalRepairCandidates G v = ∅)
    (s : {z : V // z ∈ G.neighborSet v})
    (a : V) (ha : a ∈ secondLayerBranch G v s)
    (hadegree : G.degree a = d) :
    (G.neighborFinset a ∩ secondLayer G v).card = d - 1 := by
  classical
  let P := {z : V // z ∈ G.neighborSet v}
  have hdisj := secondLayerBranch_pairwiseDisjoint G hfree v
  have hinter : G.neighborFinset a ∩ secondLayer G v =
      Finset.univ.biUnion fun u : P =>
        G.neighborFinset a ∩ secondLayerBranch G v u := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_inter.mp hq with ⟨hqa, hqSecond⟩
      rw [secondLayer] at hqSecond
      rcases Finset.mem_biUnion.mp hqSecond with ⟨u, _, hqu⟩
      exact Finset.mem_biUnion.mpr ⟨u, by simp,
        Finset.mem_inter.mpr ⟨hqa, hqu⟩⟩
    · intro hq
      rcases Finset.mem_biUnion.mp hq with ⟨u, _, hqu⟩
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hqu).1,
        Finset.mem_biUnion.mpr ⟨u, by simp,
          (Finset.mem_inter.mp hqu).2⟩⟩
  have hinterDisj :
      (↑(Finset.univ : Finset P) : Set P).PairwiseDisjoint
        (fun u => G.neighborFinset a ∩ secondLayerBranch G v u) := by
    intro u _ w _ huw
    change Disjoint
      (G.neighborFinset a ∩ secondLayerBranch G v u)
      (G.neighborFinset a ∩ secondLayerBranch G v w)
    rw [Finset.disjoint_left]
    intro q hqu hqw
    exact (Finset.disjoint_left.mp
      (hdisj (by simp) (by simp) huw))
        (Finset.mem_inter.mp hqu).2 (Finset.mem_inter.mp hqw).2
  rw [hinter, Finset.card_biUnion hinterDisj]
  exact sum_card_neighbors_inter_highBranches_eq_degree_sub_one
    G hfree hexternal s a ha hadegree

/-- **Uniform outer regularity.**  The induced second-layer graph at a
saturated square-order high root is `(d-1)`-regular. -/
theorem squareOrderOuterGraph_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hcard : Fintype.card V = d * d) {v : V}
    (hv : G.degree v = d + 1)
    (hneigh : ∀ y, G.Adj v y → G.degree y = d)
    (hlocal : ∀ s : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree s = 1)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = d) :
    ∀ a, (squareOrderOuterGraph G v).degree a = d - 1 := by
  have hexternal := externalRepairCandidates_eq_empty_of_squareOrder_highRoot
    G hfree hd hcard hv hneigh hlocal
  intro a
  rw [squareOrderOuterGraph_degree_eq_card_inter]
  have haSecond := a.2
  change a.1 ∈ (Finset.univ.biUnion fun s :
    {z : V // z ∈ G.neighborSet v} => secondLayerBranch G v s) at haSecond
  rcases Finset.mem_biUnion.mp haSecond with ⟨s, _, has⟩
  exact card_neighbors_inter_secondLayer_eq_sub_one
    G hfree hexternal s a.1 has (houterDegree a.2)

end

end Erdos85
