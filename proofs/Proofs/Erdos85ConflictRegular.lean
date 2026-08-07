import Proofs.Erdos85ProblemConflict

/-!
# The conflict graph of a regular C4-free graph

For a vertex `x`, index all length-two walks starting at `x` by their first
edge.  In a C4-free graph the resulting branches are pairwise disjoint.
Consequently, if the original graph is `d`-regular, its common-neighbour
conflict graph is exactly `d(d-1)`-regular.
-/

open SimpleGraph Finset

namespace Erdos85

/-- The endpoints other than `x` of two-step walks whose first edge is
`x-y`. -/
def conflictBranch {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (y : {z : V // z ∈ G.neighborSet x}) : Finset V :=
  (G.neighborFinset y.1).erase x

/-- Distinct first edges give disjoint conflict branches in a C4-free graph. -/
theorem conflictBranch_pairwiseDisjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x : V) :
    (↑(Finset.univ : Finset {z : V // z ∈ G.neighborSet x}) : Set _).PairwiseDisjoint
      (conflictBranch G x) := by
  intro y _ z _ hyz
  change Disjoint (conflictBranch G x y) (conflictBranch G x z)
  rw [Finset.disjoint_left]
  intro w hwy hwz
  have hyw : G.Adj y.1 w := (G.mem_neighborFinset y.1 w).mp
    (Finset.mem_erase.mp hwy).2
  have hzw : G.Adj z.1 w := (G.mem_neighborFinset z.1 w).mp
    (Finset.mem_erase.mp hwz).2
  have hyzne : y.1 ≠ z.1 := fun h => hyz (Subtype.ext h)
  have hxw : x ≠ w := (Finset.mem_erase.mp hwy).1.symm
  exact hfree (containsC4_of_two_common hyzne hxw y.2 z.2 hyw.symm hzw.symm)

/-- The conflict neighbours of `x` are exactly the union of its two-step
branches. -/
theorem neighborFinset_commonNeighborConflict_eq_biUnion_conflictBranch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (commonNeighborConflict G).neighborFinset x =
      (Finset.univ : Finset {z : V // z ∈ G.neighborSet x}).biUnion
        (conflictBranch G x) := by
  ext w
  constructor
  · intro hw
    have hconf := ((commonNeighborConflict G).mem_neighborFinset x w).mp hw
    have hnon := hconf.2
    change ∃ y, y ∈ G.neighborFinset x ∩ G.neighborFinset w at hnon
    rcases hnon with ⟨y, hymem⟩
    have ⟨hyx, hyw⟩ := Finset.mem_inter.mp hymem
    rw [Finset.mem_biUnion]
    let y' : {z : V // z ∈ G.neighborSet x} :=
      ⟨y, (G.mem_neighborFinset x y).mp hyx⟩
    refine ⟨y', Finset.mem_univ _, ?_⟩
    rw [conflictBranch, Finset.mem_erase]
    exact ⟨hconf.1.symm,
      (G.mem_neighborFinset y w).mpr ((G.mem_neighborFinset w y).mp hyw).symm⟩
  · intro hw
    rw [Finset.mem_biUnion] at hw
    obtain ⟨y, _, hwy⟩ := hw
    rw [conflictBranch, Finset.mem_erase] at hwy
    rw [(commonNeighborConflict G).mem_neighborFinset]
    refine ⟨hwy.1.symm, ?_⟩
    change ∃ z, z ∈ G.neighborFinset x ∩ G.neighborFinset w
    exact ⟨y.1, Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset x y.1).mpr y.2,
       (G.mem_neighborFinset w y.1).mpr
         ((G.mem_neighborFinset y.1 w).mp hwy.2).symm⟩⟩

/-- In a regular graph, every two-step conflict branch has `d-1` vertices. -/
theorem card_conflictBranch_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hreg : ∀ v, G.degree v = d) (x : V)
    (y : {z : V // z ∈ G.neighborSet x}) :
    (conflictBranch G x y).card = d - 1 := by
  rw [conflictBranch, Finset.card_erase_of_mem]
  · simpa [SimpleGraph.card_neighborFinset_eq_degree, hreg y.1]
  · exact (G.mem_neighborFinset y.1 x).mpr y.2.symm

/-- **Exact conflict degree.** The common-neighbour conflict graph of a
`d`-regular C4-free graph is `d(d-1)`-regular. -/
theorem degree_commonNeighborConflict_of_regular_c4Free
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ v, G.degree v = d) (x : V) :
    (commonNeighborConflict G).degree x = d * (d - 1) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_commonNeighborConflict_eq_biUnion_conflictBranch]
  rw [Finset.card_biUnion (conflictBranch_pairwiseDisjoint G hfree x)]
  calc
    ∑ y : {z : V // z ∈ G.neighborSet x}, (conflictBranch G x y).card =
        ∑ _y : {z : V // z ∈ G.neighborSet x}, (d - 1) := by
          apply Finset.sum_congr rfl
          intro y _
          exact card_conflictBranch_of_regular G hreg x y
    _ = G.degree x * (d - 1) := by
      rw [Finset.sum_const, Finset.card_univ,
        SimpleGraph.card_neighborSet_eq_degree]
      simp [nsmul_eq_mul]
    _ = d * (d - 1) := by rw [hreg x]

/-- The independence number of a `k`-regular graph is at most the number of
vertices left after deleting one closed conflict neighbourhood. -/
theorem indepNum_le_card_sub_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {k : ℕ}
    (hreg : ∀ v, H.degree v = k) :
    H.indepNum ≤ Fintype.card V - k := by
  obtain ⟨S, hSind, hScard⟩ := H.exists_isNIndepSet_indepNum
  by_cases hSempty : S = ∅
  · simp [hSempty] at hScard
    omega
  have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSempty
  obtain ⟨x, hxS⟩ := hSne
  rw [SimpleGraph.isIndepSet_iff] at hSind
  have hsub : S.erase x ⊆ Hᶜ.neighborFinset x := by
    intro y hy
    have ⟨hyx, hyS⟩ := Finset.mem_erase.mp hy
    rw [(Hᶜ).mem_neighborFinset]
    exact ⟨hyx.symm, hSind hxS hyS hyx.symm⟩
  have herase : (S.erase x).card + 1 = S.card := by
    simpa using Finset.card_erase_add_one hxS
  have hcardle := Finset.card_le_card hsub
  have hdegcompl := H.degree_compl x
  have hk : k ≤ Fintype.card V - 1 := by
    rw [← hreg x]
    have := H.degree_lt_card_verts x
    omega
  have hVpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
  rw [SimpleGraph.card_neighborFinset_eq_degree, hdegcompl, hreg x] at hcardle
  have hid : Fintype.card V - 1 - k + 1 = Fintype.card V - k := by
    omega
  calc
    H.indepNum = S.card := hScard.symm
    _ = (S.erase x).card + 1 := herase.symm
    _ ≤ (Fintype.card V - 1 - k) + 1 := Nat.add_le_add_right hcardle 1
    _ = Fintype.card V - k := hid

/-- A `d`-regular C4-free graph on `m` vertices has no safe attachment set
larger than its excess `m-d(d-1)` over the two-step count. -/
theorem indepNum_commonNeighborConflict_le_excess
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ v, G.degree v = d) :
    (commonNeighborConflict G).indepNum ≤
      Fintype.card V - d * (d - 1) := by
  apply indepNum_le_card_sub_of_regular
  exact degree_commonNeighborConflict_of_regular_c4Free G hfree hreg

/-- In particular, at the second strict Moore order every safe one-vertex
attachment set has at most three vertices. -/
theorem indepNum_commonNeighborConflict_secondOrder_le_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ v, G.degree v = d)
    (hcard : Fintype.card V = d * (d - 1) + 3) :
    (commonNeighborConflict G).indepNum ≤ 3 := by
  have h := indepNum_commonNeighborConflict_le_excess G hfree hreg
  omega

end Erdos85
