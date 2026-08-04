import Proofs.Erdos85Problem

/-!
# Paired safe attachment for Erdős Problem 85

The one-vertex attachment criterion in `Erdos85Problem` requires `d` old
neighbours for every new vertex.  A connected pair of new vertices only needs
`d - 1` old neighbours apiece.  This file isolates the exact extra compatibility
conditions which make that construction C₄-free.
-/

namespace Erdos85

open SimpleGraph

/-- The selector for the second endpoint of a newly attached edge: it contains
the first new vertex and the old vertices in `T`. -/
def pairedSelector {V : Type*} [DecidableEq V] (T : Finset V) :
    Finset (Option V) :=
  insert none (T.map ⟨some, Option.some_injective V⟩)

@[simp] theorem mem_pairedSelector_none {V : Type*} [DecidableEq V]
    (T : Finset V) : none ∈ pairedSelector T := by
  simp [pairedSelector]

@[simp] theorem mem_pairedSelector_some {V : Type*} [DecidableEq V]
    (T : Finset V) (x : V) : some x ∈ pairedSelector T ↔ x ∈ T := by
  simp [pairedSelector]

@[simp] theorem card_pairedSelector {V : Type*} [DecidableEq V]
    (T : Finset V) : (pairedSelector T).card = T.card + 1 := by
  rw [pairedSelector, Finset.card_insert_of_notMem]
  · simp
  · simp

/-- Compatibility conditions for attaching a *connected pair* of vertices.

Both old-neighbour sets must separately be safe.  Their intersection has size
at most one (otherwise the two new vertices have two common neighbours), and
there are no edges from `S` to `T` (otherwise such an edge completes a C₄ with
the new edge). -/
def PairedAttachmentCompatible {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) : Prop :=
  CommonNeighborIndependent G S ∧
  CommonNeighborIndependent G T ∧
  (S ∩ T).card ≤ 1 ∧
  ∀ ⦃a⦄, a ∈ S → ∀ ⦃b⦄, b ∈ T → ¬ G.Adj a b

/-- After attaching the first endpoint along `S`, the set consisting of that
endpoint together with `T` is a safe selector.  Thus attaching the second
endpoint creates no C₄. -/
theorem commonNeighborIndependent_pairedSelector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V)
    (hcompat : PairedAttachmentCompatible G S T) :
    CommonNeighborIndependent (attachVertex G S) (pairedSelector T) := by
  rcases hcompat with ⟨hS, hT, hinter, hcross⟩
  intro a ha b hb hab
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
    SimpleGraph.mem_neighborFinset] at hw
  rcases a with _ | a <;> rcases b with _ | b
  · exact (hab rfl).elim
  · rcases w with _ | z
    · exact attachVertex_not_adj_none_none hw.1
    · have hzS : z ∈ S := by simpa using hw.1
      have hbT : b ∈ T := by simpa using hb
      exact hcross hzS hbT (by simpa using hw.2.symm)
  · rcases w with _ | z
    · exact attachVertex_not_adj_none_none hw.2
    · have hzS : z ∈ S := by simpa using hw.2
      have haT : a ∈ T := by simpa using ha
      exact hcross hzS haT (by simpa using hw.1.symm)
  · have haT : a ∈ T := by simpa using ha
    have hbT : b ∈ T := by simpa using hb
    have hab' : a ≠ b := fun h => hab (congrArg some h)
    rcases w with _ | z
    · have haS : a ∈ S := by simpa using hw.1
      have hbS : b ∈ S := by simpa using hw.2
      have haI : a ∈ S ∩ T := Finset.mem_inter.mpr ⟨haS, haT⟩
      have hbI : b ∈ S ∩ T := Finset.mem_inter.mpr ⟨hbS, hbT⟩
      exact hab' (Finset.card_le_one.mp hinter a haI b hbI)
    · have hz : z ∈ G.neighborFinset a ∩ G.neighborFinset b := by
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
          SimpleGraph.mem_neighborFinset]
        exact ⟨by simpa using hw.1, by simpa using hw.2⟩
      have hempty : (G.neighborFinset a ∩ G.neighborFinset b).card = 0 :=
        hT haT hbT hab'
      rw [Finset.card_eq_zero] at hempty
      rw [hempty] at hz
      simp at hz

/-- **Paired attachment theorem.**  Add one vertex along `S`, then an adjacent
second vertex along `T`.  The resulting graph is C₄-free under the three
transparent compatibility conditions above. -/
theorem pairedAttachment_not_containsC4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V)
    (hfree : ¬ containsC4 V G)
    (hcompat : PairedAttachmentCompatible G S T) :
    ¬ containsC4 (Option (Option V))
      (attachVertex (attachVertex G S) (pairedSelector T)) := by
  apply (attachVertex_not_containsC4_iff).2
  constructor
  · exact (attachVertex_not_containsC4_iff).2 ⟨hfree, hcompat.1⟩
  · exact commonNeighborIndependent_pairedSelector G S T hcompat

/-- The compatibility conditions are also necessary: if the connected-pair
attachment is `C₄`-free, both selectors are safe, their overlap has size at
most one, and no old edge crosses between them. -/
theorem pairedAttachmentCompatible_of_not_containsC4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V)
    (hfree : ¬ containsC4 (Option (Option V))
      (attachVertex (attachVertex G S) (pairedSelector T))) :
    PairedAttachmentCompatible G S T := by
  have hsecond := (attachVertex_not_containsC4_iff.mp hfree).2
  have hfirstFree := (attachVertex_not_containsC4_iff.mp hfree).1
  have hS := (attachVertex_not_containsC4_iff.mp hfirstFree).2
  refine ⟨hS, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have haSel : some a ∈ pairedSelector T := by simpa using ha
    have hbSel : some b ∈ pairedSelector T := by simpa using hb
    have hz := hsecond haSel hbSel (by simpa using hab)
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hzm
    have hz' : some z ∈
        (attachVertex G S).neighborFinset (some a) ∩
          (attachVertex G S).neighborFinset (some b) := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        SimpleGraph.mem_neighborFinset]
      rcases Finset.mem_inter.mp hzm with ⟨hza, hzb⟩
      exact ⟨by simpa using hza, by simpa using hzb⟩
    rw [Finset.card_eq_zero] at hz
    rw [hz] at hz'
    simp at hz'
  · rw [Finset.card_le_one_iff]
    intro a b ha hb
    by_contra hab
    have haI := Finset.mem_inter.mp ha
    have hbI := Finset.mem_inter.mp hb
    have haSel : some a ∈ pairedSelector T := by simpa using haI.2
    have hbSel : some b ∈ pairedSelector T := by simpa using hbI.2
    have hz := hsecond haSel hbSel (by simpa using hab)
    have hnone : none ∈
        (attachVertex G S).neighborFinset (some a) ∩
          (attachVertex G S).neighborFinset (some b) := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        SimpleGraph.mem_neighborFinset]
      exact ⟨by simpa using haI.1, by simpa using hbI.1⟩
    rw [Finset.card_eq_zero] at hz
    rw [hz] at hnone
    simp at hnone
  · intro a ha b hb hab
    have hnoneSel : (none : Option V) ∈ pairedSelector T := by simp
    have hbSel : some b ∈ pairedSelector T := by simpa using hb
    have hne : (none : Option V) ≠ some b := by simp
    have hz := hsecond hnoneSel hbSel hne
    have hsomea : some a ∈
        (attachVertex G S).neighborFinset none ∩
          (attachVertex G S).neighborFinset (some b) := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        SimpleGraph.mem_neighborFinset]
      exact ⟨by simpa using ha, by simpa using hab.symm⟩
    rw [Finset.card_eq_zero] at hz
    rw [hz] at hsomea
    simp at hsomea

/-- **Exact connected-pair attachment criterion.** -/
theorem pairedAttachment_not_containsC4_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) :
    ¬ containsC4 (Option (Option V))
        (attachVertex (attachVertex G S) (pairedSelector T)) ↔
      ¬ containsC4 V G ∧ PairedAttachmentCompatible G S T := by
  constructor
  · intro h
    have hfirst := (attachVertex_not_containsC4_iff.mp h).1
    exact ⟨(attachVertex_not_containsC4_iff.mp hfirst).1,
      pairedAttachmentCompatible_of_not_containsC4 G S T h⟩
  · rintro ⟨hG, hcompat⟩
    exact pairedAttachment_not_containsC4 G S T hG hcompat

/-- The degree cost of cross-edge removal is unavoidable for *any* spanning
subgraph supporting the same paired attachment, not only for the canonical
`deleteCrossEdges` construction. -/
theorem degree_add_crossNeighbors_le_of_pairedCompatible_subgraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hKH : K ≤ H) (S T : Finset V)
    (hcompat : PairedAttachmentCompatible K S T)
    (v : V) (hvS : v ∈ S) :
    K.degree v + (H.neighborFinset v ∩ T).card ≤ H.degree v := by
  classical
  let A := K.neighborFinset v
  let B := H.neighborFinset v ∩ T
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro u huA huB
    have hvu : K.Adj v u := by
      simpa [A, SimpleGraph.mem_neighborFinset] using huA
    have huT : u ∈ T := (Finset.mem_inter.mp huB).2
    exact hcompat.2.2.2 hvS huT hvu
  have hsub : A ∪ B ⊆ H.neighborFinset v := by
    intro u hu
    rcases Finset.mem_union.mp hu with huA | huB
    · rw [SimpleGraph.mem_neighborFinset]
      apply hKH
      simpa [A, SimpleGraph.mem_neighborFinset] using huA
    · exact (Finset.mem_inter.mp huB).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  simpa [A, B, SimpleGraph.card_neighborFinset_eq_degree] using hcard

theorem degree_add_crossNeighbors_le_of_pairedCompatible_subgraph_right
    {V : Type*} [Fintype V] [DecidableEq V]
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hKH : K ≤ H) (S T : Finset V)
    (hcompat : PairedAttachmentCompatible K S T)
    (v : V) (hvT : v ∈ T) :
    K.degree v + (H.neighborFinset v ∩ S).card ≤ H.degree v := by
  have hcompat' : PairedAttachmentCompatible K T S := by
    exact ⟨hcompat.2.1, hcompat.1, by simpa [Finset.inter_comm] using hcompat.2.2.1,
      fun a ha b hb hab => hcompat.2.2.2 hb ha hab.symm⟩
  exact degree_add_crossNeighbors_le_of_pairedCompatible_subgraph
    H K hKH T S hcompat' v hvT

/-- Degree-facing form of paired attachment: if `T` has at least `d - 1`
old vertices, the second endpoint's selector has at least `d` vertices (the
first endpoint supplies the extra neighbour). -/
theorem le_card_pairedSelector_of_pred_le {V : Type*} [DecidableEq V]
    (T : Finset V) {d : ℕ} (hT : d - 1 ≤ T.card) (hd : 1 ≤ d) :
    d ≤ (pairedSelector T).card := by
  rw [card_pairedSelector]
  omega

/-- Consequently the second endpoint of the attached edge reaches degree `d`
from only `d - 1` old neighbours. -/
theorem le_degree_secondEndpoint_of_pred_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V)
    {d : ℕ} (hT : d - 1 ≤ T.card) (hd : 1 ≤ d) :
    d ≤ (attachVertex (attachVertex G S) (pairedSelector T)).degree none := by
  exact le_trans (le_card_pairedSelector_of_pred_le T hT hd)
    (card_le_attachVertex_degree_none (attachVertex G S) (pairedSelector T))

end Erdos85
