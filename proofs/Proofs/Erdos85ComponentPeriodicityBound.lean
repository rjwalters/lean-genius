import Proofs.Erdos85DefectCycleBlock
import Proofs.Erdos85SecondOrderQuotient

/-!
# Component-quotient bounds from defect-cycle periodicity

This file connects the rectangular cycle-block theorem to the actual
connected-component quotient.  It is the soundness lemma behind the
`periodicCommonNeighborOK` sieve in the degree-six classifier.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- If one distinct source vertex has the same adjacency as another on each
component in `es`, then the *sum* of all corresponding component-neighbor
counts is at most one.  This is the grouped common-neighbor inequality used
by the finite classifier. -/
theorem sum_componentNeighborFinset_card_le_one_of_periodic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent]
    (hfree : ¬ containsC4 V G) (x x' : V)
    (es : Finset D.ConnectedComponent) (hne : x' ≠ x)
    (hperiod : ∀ e ∈ es, ∀ y,
      D.connectedComponentMk y = e → (G.Adj x' y ↔ G.Adj x y)) :
    (∑ e ∈ es, (componentNeighborFinset G D e x).card) ≤ 1 := by
  let t : D.ConnectedComponent → Finset V :=
    fun e => componentNeighborFinset G D e x
  have hdisj : (es : Set D.ConnectedComponent).PairwiseDisjoint t := by
    intro e he f hf hef
    change Disjoint (t e) (t f)
    rw [Finset.disjoint_left]
    intro y hye hyf
    have hyedata : G.Adj x y ∧ D.connectedComponentMk y = e := by
      simpa [t, componentNeighborFinset,
        SimpleGraph.mem_neighborFinset] using hye
    have hyfdata : G.Adj x y ∧ D.connectedComponentMk y = f := by
      simpa [t, componentNeighborFinset,
        SimpleGraph.mem_neighborFinset] using hyf
    have hce : D.connectedComponentMk y = e := by
      exact hyedata.2
    have hcf : D.connectedComponentMk y = f := by
      exact hyfdata.2
    exact hef (hce.symm.trans hcf)
  have hsub : es.biUnion t ⊆
      G.neighborFinset x ∩ G.neighborFinset x' := by
    intro y hy
    obtain ⟨e, he, hye⟩ := Finset.mem_biUnion.mp hy
    have hydata : G.Adj x y ∧ D.connectedComponentMk y = e := by
      simpa [t, componentNeighborFinset,
        SimpleGraph.mem_neighborFinset] using hye
    have hxy : G.Adj x y := by
      exact hydata.1
    have hcomp : D.connectedComponentMk y = e := by
      exact hydata.2
    have hx'y : G.Adj x' y := (hperiod e he y hcomp).mpr hxy
    simp [SimpleGraph.mem_neighborFinset, hxy, hx'y]
  calc
    (∑ e ∈ es, (componentNeighborFinset G D e x).card) =
        (es.biUnion t).card := by
          rw [Finset.card_biUnion hdisj]
    _ ≤ (G.neighborFinset x ∩ G.neighborFinset x').card :=
      Finset.card_le_card hsub
    _ ≤ 1 := common_le_one_of_not_containsC4 hfree x x' hne.symm

/-- Quotient-matrix form of the grouped periodic common-neighbor bound. -/
theorem sum_componentQuotientMatrix_le_one_of_periodic
    {V α : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] [DecidableEq α] [AddCommGroup α]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent]
    (hfree : ¬ containsC4 V G) (c : D.ConnectedComponent)
    (u : α → V) (huinj : Function.Injective u)
    (hurange : Set.range u = c.supp) (s : α) (hs : s ≠ 0)
    (es : Finset D.ConnectedComponent)
    (hperiod : ∀ e ∈ es, ∀ z y,
      D.connectedComponentMk y = e →
        (G.Adj (u (z + s)) y ↔ G.Adj (u z) y)) :
    (∑ e ∈ es, componentQuotientMatrix G D c e) ≤ 1 := by
  have hrep : componentRepresentative D c ∈ Set.range u := by
    rw [hurange]
    exact componentRepresentative_mem D c
  obtain ⟨z, hz⟩ := hrep
  have hne : u (z + s) ≠ u z := by
    intro heq
    have hzs : z + s = z := huinj heq
    apply hs
    have hzs' : z + s = z + 0 := by simpa using hzs
    exact add_left_cancel hzs'
  change (∑ e ∈ es,
    (componentNeighborFinset G D e (componentRepresentative D c)).card) ≤ 1
  rw [← hz]
  apply sum_componentNeighborFinset_card_le_one_of_periodic
    G D hfree (u z) (u (z + s)) es hne
  intro e he y hy
  exact hperiod e he z y hy

/-- Cycle-length form of the grouped quotient bound.  All target components
whose cycle lengths induce the same nonzero source translation contribute at
most one in total. -/
theorem sum_componentQuotientMatrix_le_one_of_equal_targetLengthResidue
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hcomm : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (hdeg : ∀ z, D.degree z = 2)
    (c : D.ConnectedComponent) {xp : V} {p : D.Walk xp xp}
    (hp : p.IsCycle) (hpverts : p.toSubgraph.verts = c.supp)
    (es : Finset D.ConnectedComponent)
    (xq : D.ConnectedComponent → V)
    (q : ∀ e, D.Walk (xq e) (xq e))
    (hqcycle : ∀ e ∈ es, (q e).IsCycle)
    (hqverts : ∀ e ∈ es, (q e).toSubgraph.verts = e.supp)
    (s : ZMod p.length)
    (hsame : ∀ e ∈ es, (q e).length • (1 : ZMod p.length) = s)
    (hs : s ≠ 0) :
    (∑ e ∈ es, componentQuotientMatrix G D c e) ≤ 1 := by
  have hp3 : 3 ≤ p.length := hp.three_le_length
  letI : NeZero p.length := ⟨by omega⟩
  obtain ⟨u, huinj, hurange, hu⟩ :=
    exists_zmod_cycleParam_neighborFinset hp hdeg
  apply sum_componentQuotientMatrix_le_one_of_periodic
    G D hfree c u huinj (hurange.trans hpverts) s hs es
  intro e he z y hycomp
  have hqe : (q e).IsCycle := hqcycle e he
  have hq3 : 3 ≤ (q e).length := hqe.three_le_length
  letI : NeZero (q e).length := ⟨by omega⟩
  obtain ⟨v, hvinj, hvrange, hv⟩ :=
    exists_zmod_cycleParam_neighborFinset hqe hdeg
  have hyrange : y ∈ Set.range v := by
    rw [hvrange, hqverts e he]
    exact hycomp
  obtain ⟨j, rfl⟩ := hyrange
  have hupair : ∀ a : ZMod p.length, u (a - 1) ≠ u (a + 1) := by
    intro a
    exact huinj.ne (zmod_sub_one_ne_add_one_of_three_le hp3 a)
  have hvpair : ∀ b : ZMod (q e).length, v (b - 1) ≠ v (b + 1) := by
    intro b
    exact hvinj.ne (zmod_sub_one_ne_add_one_of_three_le hq3 b)
  have hinter := entry_cycleIntertwine_of_adjMatrix_comm G D u v
    (1 : ZMod p.length) (1 : ZMod (q e).length)
    hcomm hu hv hupair hvpair
  have hperiod := adj_iff_add_targetOrder_of_entry_cycleIntertwine
    G u v (1 : ZMod p.length) (1 : ZMod (q e).length) hinter z j
  simpa only [ZMod.addOrderOf_one, hsame e he] using hperiod

/-- If the target component length gives a nonzero translation on the source
component, the corresponding component-quotient entry is at most one. -/
theorem componentQuotientMatrix_le_one_of_targetLength
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hcomm : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (hdeg : ∀ z, D.degree z = 2)
    (c e : D.ConnectedComponent)
    {xp xe : V} {p : D.Walk xp xp} {q : D.Walk xe xe}
    (hp : p.IsCycle) (hq : q.IsCycle)
    (hpverts : p.toSubgraph.verts = c.supp)
    (hqverts : q.toSubgraph.verts = e.supp)
    (hshift : q.length • (1 : ZMod p.length) ≠ 0) :
    componentQuotientMatrix G D c e ≤ 1 := by
  letI : NeZero p.length := ⟨by have := hp.three_le_length; omega⟩
  letI : NeZero q.length := ⟨by have := hq.three_le_length; omega⟩
  obtain ⟨u, v, huinj, -, hurange, hvrange, -, -, hperiod⟩ :=
    exists_cycleBlock_targetLength_periodic G D hcomm hdeg hp hq
  have hrep : componentRepresentative D c ∈ Set.range u := by
    rw [hurange, hpverts]
    exact componentRepresentative_mem D c
  obtain ⟨z, hz⟩ := hrep
  have hbound := card_cycleBlock_targetNeighbors_le_one G hfree u v huinj
    (q.length • (1 : ZMod p.length)) hperiod hshift z
  have himage : Finset.univ.image v = e.supp.toFinset := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_toFinset]
    rw [← hqverts, ← hvrange]
    rfl
  have hcomponent : componentNeighborFinset G D e (u z) =
      (e.supp.toFinset).filter fun y => G.Adj (u z) y := by
    ext y
    simp [componentNeighborFinset, SimpleGraph.mem_neighborFinset,
      SimpleGraph.ConnectedComponent.mem_supp_iff, and_comm]
  change (componentNeighborFinset G D e (componentRepresentative D c)).card ≤ 1
  rw [← hz, hcomponent, ← himage]
  exact hbound

end

end Erdos85
