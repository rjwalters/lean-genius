import Proofs.Erdos85CycleIntertwinerPeriodicity
import Proofs.Erdos85CycleGraphIso

/-!
# Restricting a commuting adjacency matrix to two cycle components

This is the algebraic bridge between the global identity `A D = D A` and the
rectangular cycle recurrence used by the periodicity obstruction.
-/

namespace Erdos85

open SimpleGraph

/-- In a degree-two graph, two distinct exhibited neighbors are the entire
neighbor finset. -/
theorem neighborFinset_eq_pair_of_degree_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    {x y z : V} (hdeg : D.degree x = 2)
    (hxy : D.Adj x y) (hxz : D.Adj x z) (hyz : y ≠ z) :
    D.neighborFinset x = {y, z} := by
  have hsub : ({y, z} : Finset V) ⊆ D.neighborFinset x := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact (D.mem_neighborFinset x _).mpr hxy
    · exact (D.mem_neighborFinset x _).mpr hxz
  have hcardD : (D.neighborFinset x).card = 2 := by
    rw [D.card_neighborFinset_eq_degree, hdeg]
  have hcardPair : ({y, z} : Finset V).card = 2 := by simp [hyz]
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

private theorem zmodFinEquiv_val {n : ℕ} [NeZero n] (i : Fin n) :
    (ZMod.finEquiv n i).val = i.val := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rfl

/-- On a cyclic coordinate set of order at least three, the predecessor and
successor of any coordinate are distinct. -/
theorem zmod_sub_one_ne_add_one_of_three_le
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) (z : ZMod n) :
    z - 1 ≠ z + 1 := by
  intro hz
  have htwo : (2 : ZMod n) = 0 := by
    calc
      (2 : ZMod n) = (z + 1) - (z - 1) := by ring
      _ = 0 := by rw [← hz]; simp
  have hdvd : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp htwo
  have hle : n ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- A cycle walk in a two-regular graph admits genuine additive coordinates
in `ZMod p.length`; the two neighbors of coordinate `z` are exactly `z-1`
and `z+1`. -/
theorem exists_zmod_cycleParam_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    {D : SimpleGraph V} [DecidableRel D.Adj]
    {x : V} {p : D.Walk x x} (hp : p.IsCycle)
    (hdeg : ∀ z, D.degree z = 2) :
    ∃ u : ZMod p.length → V, Function.Injective u ∧
      Set.range u = p.toSubgraph.verts ∧
      ∀ z, D.neighborFinset (u z) = {u (z - 1), u (z + 1)} := by
  have hlen : 3 ≤ p.length := hp.three_le_length
  letI : NeZero p.length := ⟨by omega⟩
  letI : Fact (1 < p.length) := ⟨by omega⟩
  let eFin : Fin p.length ≃+ ZMod p.length := ZMod.finEquiv p.length
  let u : ZMod p.length → V := fun z =>
    (cycleVertexEquiv hp (eFin.symm z)).val
  have huinj : Function.Injective u := by
    intro z w hzw
    apply eFin.symm.injective
    apply (cycleVertexEquiv hp).injective
    exact Subtype.ext hzw
  have hurange : Set.range u = p.toSubgraph.verts := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact (cycleVertexEquiv hp (eFin.symm z)).property
    · intro hy
      let yy : {z // z ∈ p.toSubgraph.verts} := ⟨y, hy⟩
      obtain ⟨i, hi⟩ := (cycleVertexEquiv hp).surjective yy
      refine ⟨eFin i, ?_⟩
      change (cycleVertexEquiv hp (eFin.symm (eFin i))).val = y
      rw [eFin.symm_apply_apply]
      exact congrArg Subtype.val hi
  have hone : (eFin.symm (1 : ZMod p.length)).val = 1 := by
    have h := zmodFinEquiv_val (eFin.symm (1 : ZMod p.length))
    change (eFin (eFin.symm (1 : ZMod p.length))).val =
      (eFin.symm (1 : ZMod p.length)).val at h
    rw [eFin.apply_symm_apply] at h
    rw [ZMod.val_one] at h
    omega
  have hminus (z : ZMod p.length) : D.Adj (u z) (u (z - 1)) := by
    let iz := eFin.symm z
    let io := eFin.symm (1 : ZMod p.length)
    have hcoord : eFin.symm (z - 1) = iz - io := by
      exact eFin.symm.map_sub z 1
    have hc : (cycleGraph p.length).Adj iz (iz - io) := by
      rw [cycleGraph_adj']
      left
      change (iz - (iz - io)).val = 1
      have heq : iz - (iz - io) = io := by abel
      rw [heq]
      exact hone
    have hs := ((isCycle_cycleGraphIsoToSubgraph hp).map_rel_iff).mpr hc
    change D.Adj (cycleVertexEquiv hp (eFin.symm z)).val
      (cycleVertexEquiv hp (eFin.symm (z - 1))).val
    rw [hcoord]
    exact p.toSubgraph.adj_sub hs
  have hplus (z : ZMod p.length) : D.Adj (u z) (u (z + 1)) := by
    let iz := eFin.symm z
    let io := eFin.symm (1 : ZMod p.length)
    have hcoord : eFin.symm (z + 1) = iz + io := by
      exact eFin.symm.map_add z 1
    have hc : (cycleGraph p.length).Adj iz (iz + io) := by
      rw [cycleGraph_adj']
      right
      change (iz + io - iz).val = 1
      have heq : iz + io - iz = io := add_sub_cancel_left iz io
      rw [heq]
      exact hone
    have hs := ((isCycle_cycleGraphIsoToSubgraph hp).map_rel_iff).mpr hc
    change D.Adj (cycleVertexEquiv hp (eFin.symm z)).val
      (cycleVertexEquiv hp (eFin.symm (z + 1))).val
    rw [hcoord]
    exact p.toSubgraph.adj_sub hs
  have hdistinct (z : ZMod p.length) : u (z - 1) ≠ u (z + 1) := by
    intro heq
    have hz : z - 1 = z + 1 := huinj heq
    have htwo : (2 : ZMod p.length) = 0 := by
      calc
        (2 : ZMod p.length) = (z + 1) - (z - 1) := by ring
        _ = 0 := by rw [← hz]; simp
    have hdvd : p.length ∣ 2 :=
      (ZMod.natCast_eq_zero_iff 2 p.length).mp htwo
    have hle : p.length ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  refine ⟨u, huinj, hurange, fun z => ?_⟩
  exact neighborFinset_eq_pair_of_degree_two D (hdeg (u z))
    (hminus z) (hplus z) (hdistinct z)

/-- If two parametrized vertex sets have exactly the two prescribed
`D`-neighbors, global commutation of `G` and `D` restricts to the entrywise
cycle-intertwining recurrence on their rectangular `G`-adjacency block. -/
theorem entry_cycleIntertwine_of_adjMatrix_comm
    {V α β : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] [DecidableEq α] [AddCommGroup α]
    [Fintype β] [DecidableEq β] [AddCommGroup β]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : α → V) (v : β → V) (a : α) (b : β)
    (hcomm : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (hu : ∀ x, D.neighborFinset (u x) = {u (x - a), u (x + a)})
    (hv : ∀ y, D.neighborFinset (v y) = {v (y - b), v (y + b)})
    (hua : ∀ x, u (x - a) ≠ u (x + a))
    (hvb : ∀ y, v (y - b) ≠ v (y + b)) :
    ∀ x y,
      G.adjMatrix ℤ (u (x - a)) (v y) +
          G.adjMatrix ℤ (u (x + a)) (v y) =
        G.adjMatrix ℤ (u x) (v (y + b)) +
          G.adjMatrix ℤ (u x) (v (y - b)) := by
  intro x y
  have hentry := congrFun (congrFun hcomm (u x)) (v y)
  rw [D.mul_adjMatrix_apply, D.adjMatrix_mul_apply, hu, hv] at hentry
  simp only [Finset.sum_insert, Finset.sum_singleton,
    Finset.mem_singleton, hua, hvb, not_false_eq_true] at hentry
  simpa [add_comm, G.adj_comm, SimpleGraph.adjMatrix_apply] using hentry.symm

/-- Two cycle walks in a two-regular graph commuting with `G` can be given
additive coordinates in which every column of their rectangular
`G`-adjacency block is periodic in the source coordinate by the length of
the target cycle. -/
theorem exists_cycleBlock_targetLength_periodic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (hcomm : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (hdeg : ∀ z, D.degree z = 2)
    {xp xq : V} {p : D.Walk xp xp} {q : D.Walk xq xq}
    (hp : p.IsCycle) (hq : q.IsCycle) :
    ∃ (u : ZMod p.length → V) (v : ZMod q.length → V),
      Function.Injective u ∧ Function.Injective v ∧
      Set.range u = p.toSubgraph.verts ∧
      Set.range v = q.toSubgraph.verts ∧
      (∀ z, D.neighborFinset (u z) = {u (z - 1), u (z + 1)}) ∧
      (∀ z, D.neighborFinset (v z) = {v (z - 1), v (z + 1)}) ∧
      ∀ z j,
        G.Adj (u (z + q.length • (1 : ZMod p.length))) (v j) ↔
          G.Adj (u z) (v j) := by
  obtain ⟨u, huinj, hurange, hu⟩ :=
    exists_zmod_cycleParam_neighborFinset hp hdeg
  obtain ⟨v, hvinj, hvrange, hv⟩ :=
    exists_zmod_cycleParam_neighborFinset hq hdeg
  have hp3 : 3 ≤ p.length := hp.three_le_length
  have hq3 : 3 ≤ q.length := hq.three_le_length
  letI : NeZero p.length := ⟨by omega⟩
  letI : NeZero q.length := ⟨by omega⟩
  have hupair : ∀ z : ZMod p.length, u (z - 1) ≠ u (z + 1) := by
    intro z heq
    have hz : z - 1 = z + 1 := huinj heq
    have htwo : (2 : ZMod p.length) = 0 := by
      calc
        (2 : ZMod p.length) = (z + 1) - (z - 1) := by ring
        _ = 0 := by rw [← hz]; simp
    have hdvd : p.length ∣ 2 :=
      (ZMod.natCast_eq_zero_iff 2 p.length).mp htwo
    have hle : p.length ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hvpair : ∀ z : ZMod q.length, v (z - 1) ≠ v (z + 1) := by
    intro z heq
    have hz : z - 1 = z + 1 := hvinj heq
    have htwo : (2 : ZMod q.length) = 0 := by
      calc
        (2 : ZMod q.length) = (z + 1) - (z - 1) := by ring
        _ = 0 := by rw [← hz]; simp
    have hdvd : q.length ∣ 2 :=
      (ZMod.natCast_eq_zero_iff 2 q.length).mp htwo
    have hle : q.length ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hinter := entry_cycleIntertwine_of_adjMatrix_comm G D u v
    (1 : ZMod p.length) (1 : ZMod q.length) hcomm hu hv hupair hvpair
  refine ⟨u, v, huinj, hvinj, hurange, hvrange, hu, hv, ?_⟩
  intro z j
  have hperiod := adj_iff_add_targetOrder_of_entry_cycleIntertwine
    G u v (1 : ZMod p.length) (1 : ZMod q.length) hinter z j
  simpa only [ZMod.addOrderOf_one] using hperiod

/-- A nontrivial target-length translation makes two distinct source
vertices have the same neighbors throughout the parametrized target cycle;
in a `C₄`-free graph there is therefore at most one such neighbor. -/
theorem card_cycleBlock_targetNeighbors_le_one
    {V α β : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] [DecidableEq α] [AddCommGroup α]
    [Fintype β] [DecidableEq β]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (u : α → V) (v : β → V)
    (huinj : Function.Injective u) (s : α)
    (hperiod : ∀ z j, G.Adj (u (z + s)) (v j) ↔ G.Adj (u z) (v j))
    (hs : s ≠ 0) (z : α) :
    (((Finset.univ.image v).filter fun y => G.Adj (u z) y).card) ≤ 1 := by
  have hne : u (z + s) ≠ u z := by
    intro heq
    have hz : z + s = z := huinj heq
    apply hs
    have hz' : z + s = z + 0 := by simpa using hz
    exact add_left_cancel hz'
  apply card_filter_adj_le_one_of_periodic G hfree (u z) (u (z + s))
    (Finset.univ.image v) hne
  intro y hy
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
  exact hperiod z j

/-- In a `9`-by-`12` cycle block, target-length periodicity translates the
source coordinate by the nonzero class of `12 = 3 mod 9`.  Hence a source
vertex cannot have four neighbors in the target cycle of a `C₄`-free graph. -/
theorem false_of_nine_twelve_cycleBlock_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u : ZMod 9 → V) (v : ZMod 12 → V)
    (huinj : Function.Injective u)
    (hperiod : ∀ z j,
      G.Adj (u (z + (12 : ZMod 9))) (v j) ↔ G.Adj (u z) (v j))
    (z : ZMod 9)
    (hfour :
      (((Finset.univ.image v).filter fun y => G.Adj (u z) y).card) = 4) :
    False := by
  have hle := card_cycleBlock_targetNeighbors_le_one G hfree u v huinj
    (12 : ZMod 9) hperiod (by decide) z
  omega

end Erdos85
