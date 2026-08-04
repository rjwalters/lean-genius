import Proofs.Erdos85CycleResolvent
import Mathlib.Data.List.NodupEquivFin

namespace Erdos85

open SimpleGraph

theorem isCycle_setOf_mem_dropLast_support_eq_verts
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x : V}
    {p : G.Walk x x} (hp : p.IsCycle) :
    {y | y ∈ p.support.dropLast} = p.toSubgraph.verts := by
  ext y
  rw [Walk.mem_verts_toSubgraph]
  change y ∈ p.support.dropLast ↔ y ∈ p.support
  have hperm := p.tail_support_perm_dropLast_support
  rw [← hperm.mem_iff]
  constructor
  · exact List.mem_of_mem_tail
  · intro hy
    rw [← p.cons_support_tail hp.not_nil] at hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact p.end_mem_tail_support hp.not_nil
    · rw [← p.support_tail_of_not_nil hp.not_nil]
      exact hy

theorem isCycle_length_dropLast_support
    {V : Type*} {G : SimpleGraph V} {x : V} {p : G.Walk x x}
    (hp : p.IsCycle) : p.support.dropLast.length = p.length := by
  rw [List.length_dropLast, p.length_support]
  omega

/-- The cyclic enumeration of the distinct vertices of a simple closed walk. -/
noncomputable def cycleVertexEquiv
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x : V}
    {p : G.Walk x x} (hp : p.IsCycle) :
    Fin p.length ≃ p.toSubgraph.verts :=
  (finCongr (isCycle_length_dropLast_support hp).symm).trans
    ((hp.nodup_dropLast_support.getEquiv p.support.dropLast).trans
      (Equiv.setCongr (isCycle_setOf_mem_dropLast_support_eq_verts hp)))

/-- A simple cycle has as many distinct vertices as edges. -/
theorem isCycle_card_verts_eq_length
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {x : V}
    {p : G.Walk x x} (hp : p.IsCycle) :
    Nat.card p.toSubgraph.verts = p.length := by
  symm
  simpa using Nat.card_congr (cycleVertexEquiv hp)

@[simp] theorem cycleVertexEquiv_apply_val
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x : V}
    {p : G.Walk x x} (hp : p.IsCycle) (i : Fin p.length) :
    (cycleVertexEquiv hp i : V) = p.getVert i := by
  change p.support.dropLast.get
      (finCongr (isCycle_length_dropLast_support hp).symm i) =
    p.getVert i
  rw [p.getVert_eq_support_getElem (Nat.le_of_lt i.isLt)]
  simp only [List.get_eq_getElem, List.getElem_dropLast]
  congr 1

theorem isCycle_getVert_injective_before_end
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x : V}
    {p : G.Walk x x} (hp : p.IsCycle) {i j : ℕ}
    (hi : i < p.length) (hj : j < p.length)
    (hij : p.getVert i = p.getVert j) : i = j := by
  rw [p.getVert_eq_support_getElem hi.le,
    p.getVert_eq_support_getElem hj.le,
    ← List.getElem_dropLast (xs := p.support) (by simpa [p.length_support] using hi),
    ← List.getElem_dropLast (xs := p.support) (by simpa [p.length_support] using hj)] at hij
  exact hp.nodup_dropLast_support.getElem_inj_iff.mp hij

/-- A simple closed walk, with only its traversed edges retained, is a cycle
graph on the length of the walk. -/
noncomputable def isCycle_cycleGraphIsoToSubgraph
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x : V}
    {p : G.Walk x x} (hp : p.IsCycle) :
    cycleGraph p.length ≃g p.toSubgraph.coe where
  toEquiv := cycleVertexEquiv hp
  map_rel_iff' := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp
    simp only [Subgraph.coe_adj, cycleVertexEquiv_apply_val]
    rw [p.toSubgraph_adj_iff, cycleGraph_adj']
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq]
    constructor
    · rintro ⟨w, (h | h), hw⟩
      · rcases h with ⟨hwi, hwj⟩
        by_cases hend : w + 1 = p.length
        · have hwlast : w = p.length - 1 := by omega
          have hiw : i.val = w := (isCycle_getVert_injective_before_end hp i.isLt
            (by omega) hwi.symm)
          have hj0 : j.val = 0 := isCycle_getVert_injective_before_end hp j.isLt
            (by omega : 0 < p.length) (by simpa [hend, p.getVert_length, p.getVert_zero] using hwj.symm)
          right
          change (j - i).val = 1
          rw [Fin.val_sub]
          rw [hiw, hj0, hwlast, show p.length - (p.length - 1) = 1 by omega,
            Nat.mod_eq_of_lt (by omega)]
        · have hw1 : w + 1 < p.length := by omega
          have hiw : i.val = w := (isCycle_getVert_injective_before_end hp i.isLt
            (by omega) hwi.symm)
          have hjw : j.val = w + 1 := (isCycle_getVert_injective_before_end hp j.isLt
            hw1 hwj.symm)
          right
          change (j - i).val = 1
          rw [Fin.val_sub]
          rw [hiw, hjw, show p.length - w + (w + 1) = p.length + 1 by omega]
          simp [Nat.mod_eq_of_lt (by omega : 1 < p.length)]
      · have hwi : p.getVert w = p.getVert j.val := by
          simpa using congrArg Prod.fst h
        have hwj : p.getVert (w + 1) = p.getVert i.val := by
          simpa using congrArg Prod.snd h
        by_cases hend : w + 1 = p.length
        · have hwlast : w = p.length - 1 := by omega
          have hjw : j.val = w := (isCycle_getVert_injective_before_end hp j.isLt
            (by omega) hwi.symm)
          have hi0 : i.val = 0 := isCycle_getVert_injective_before_end hp i.isLt
            (by omega : 0 < p.length) (by simpa [hend, p.getVert_length, p.getVert_zero] using hwj.symm)
          left
          change (i - j).val = 1
          rw [Fin.val_sub]
          rw [hjw, hi0, hwlast, show p.length - (p.length - 1) = 1 by omega,
            Nat.mod_eq_of_lt (by omega)]
        · have hw1 : w + 1 < p.length := by omega
          have hjw : j.val = w := (isCycle_getVert_injective_before_end hp j.isLt
            (by omega) hwi.symm)
          have hiw : i.val = w + 1 := (isCycle_getVert_injective_before_end hp i.isLt
            hw1 hwj.symm)
          left
          change (i - j).val = 1
          rw [Fin.val_sub]
          rw [hiw, hjw, show p.length - w + (w + 1) = p.length + 1 by omega]
          simp [Nat.mod_eq_of_lt (by omega : 1 < p.length)]
    · rintro (hij' | hji')
      · have hz := Fin.intCast_val_sub_eq_sub_add_ite i j
        rw [hij'] at hz
        by_cases hnext : j.val + 1 < p.length
        · have hival : i.val = j.val + 1 := by
            split at hz <;> omega
          refine ⟨j.val, Or.inr ?_, j.isLt⟩
          apply Prod.ext
          · rfl
          · simp [hival]
        · have hjlast : j.val + 1 = p.length := by omega
          have hi0 : i.val = 0 := by
            split at hz <;> omega
          refine ⟨j.val, Or.inr ?_, j.isLt⟩
          apply Prod.ext
          · rfl
          · simp [hjlast, hi0, p.getVert_length, p.getVert_zero]
      · have hz := Fin.intCast_val_sub_eq_sub_add_ite j i
        rw [hji'] at hz
        by_cases hnext : i.val + 1 < p.length
        · have hjval : j.val = i.val + 1 := by
            split at hz <;> omega
          refine ⟨i.val, Or.inl ⟨rfl, ?_⟩, i.isLt⟩
          rw [hjval]
        · have hilast : i.val + 1 = p.length := by omega
          have hj0 : j.val = 0 := by
            split at hz <;> omega
          refine ⟨i.val, Or.inl ⟨rfl, ?_⟩, i.isLt⟩
          simp [hilast, hj0, p.getVert_length, p.getVert_zero]

/-- Reindexing along the cycle isomorphism identifies the two adjacency
matrices. -/
theorem isCycle_reindex_adjMatrix
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x : V}
    {p : G.Walk x x} [DecidableRel p.toSubgraph.coe.Adj]
    (hp : p.IsCycle) (R : Type*) [Zero R] [One R] :
    ((cycleGraph p.length).adjMatrix R).reindex
        (isCycle_cycleGraphIsoToSubgraph hp).toEquiv
        (isCycle_cycleGraphIsoToSubgraph hp).toEquiv =
      p.toSubgraph.coe.adjMatrix R :=
  (isCycle_cycleGraphIsoToSubgraph hp).reindex_adjMatrix R

/-- Consequently a cycle component and the standard cycle graph have the
same adjacency characteristic polynomial. -/
theorem isCycle_charpoly_adjMatrix_eq_cycleGraph
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x : V}
    {p : G.Walk x x} [Fintype p.toSubgraph.verts]
    [DecidableRel p.toSubgraph.coe.Adj] (hp : p.IsCycle) :
    (p.toSubgraph.coe.adjMatrix ℤ).charpoly =
      ((cycleGraph p.length).adjMatrix ℤ).charpoly := by
  rw [← isCycle_reindex_adjMatrix hp ℤ]
  exact Matrix.charpoly_reindex _ _

end Erdos85
