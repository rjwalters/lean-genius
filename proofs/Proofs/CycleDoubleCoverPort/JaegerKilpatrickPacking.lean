import Proofs.CycleDoubleCoverPort.NashWilliams4
import Proofs.CycleDoubleCoverPort.JaegerKilpatrickEvenCover

-- Ported from openai/cdc-lean, JaegerKilpatrick.lean (lines 180-397), vendored with
-- adaptation per operator decision 2026-08-03. Part of epic #37507.

/-!
# Jaeger--Kilpatrick, segment 2: tree packing in the doubled graph

This file is the second segment of the port of upstream `JaegerKilpatrick.lean`. The
first segment (`JaegerKilpatrickEvenCover`) reduced the group-valued eight-flow
theorem to a *supply* problem: produce three spanning trees such that every edge is
missing from at least one of them. This file supplies them, for three-edge-connected
graphs, and closes out the direct Jaeger construction.

The argument is the classical one:

* **Doubling** (`doubleGraph`): replace every edge object by two parallel copies,
  indexed by `E × Fin 2`. Doubling multiplies every partition's crossing-edge count by
  two (`crossingEdges_doubleGraph_card`).

* **Counting** (`sum_card_cut_classFinset`): summing `|cut(C)|` over the classes `C` of
  a partition counts every crossing edge exactly twice, because a crossing edge lies in
  the cut of precisely the two classes containing its ends (the private helper
  `sum_xor_eq_two` is the two-element count behind this).

* **Nash-Williams--Tutte** (`doubleGraph_satisfiesTreePackingCondition_of_threeEdgeConnected`):
  three-edge-connectivity says every proper nonempty cut has at least three edges, so
  summing over classes gives `3 · |Quotient P| ≤ 2 · |crossingEdges P|`, which is
  exactly the packing condition for three trees in the doubled graph.

* **Projection** (`exists_three_spanningTrees_omitting_each_edge`): pack three
  edge-disjoint spanning trees in the doubled graph (`nashWilliamsTutte`) and forget
  which of the two copies was used. The images stay spanning trees because
  `symEdge_injOn_of_spanningTree` makes the projection injective on each tree, and no
  edge can survive in all three images: that would give three distinct copies of a
  two-element fibre, contradicting `Fin 3 ↪ Fin 2`.

Feeding those trees to segment 1 yields `nowhereZeroGammaFlow_of_threeEdgeConnected`.

## Adaptations from upstream

* Upstream unfolds `crossingEdges` and `cut` with `simp`. In this port both are
  `open Classical`/tactic-defined `noncomputable` definitions that do not unfold under
  `simp`, so membership goes through the `mem_crossingEdges` (`NashWilliams`) and
  `mem_cut` characterisations instead.
* `mem_cut` itself lives in `Expansion`, whose import would pull the whole cubic
  subtree in for a single one-line iff; it is restated here as the private
  `mem_cut_iff` with the same one-line proof.
* Upstream's `Finset.product` is written with the `×ˢ` notation that
  `Finset.card_product` is stated against.

The remaining upstream material (edge contraction and the reduction of the general
case to the three-edge-connected one) is a later segment.
-/

namespace CycleDoubleCover

namespace FiniteGraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (H : FiniteGraph V E)

omit [DecidableEq V] [DecidableEq E] in
/-- Membership in a cut. This restates `Expansion.mem_cut` so that this segment does
not have to import the cubic-expansion subtree; the proof is the same one line. -/
private theorem mem_cut_iff {S : Finset V} {e : E} : e ∈ H.cut S ↔ H.Crosses S e := by
  classical
  simp [cut]

/-- Every proper nonempty vertex cut has at least three edge objects. -/
def IsThreeEdgeConnected : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → 3 ≤ (H.cut S).card

/-- Two parallel copies of every genuine edge object. -/
def doubleGraph : FiniteGraph V (E × Fin 2) where
  endAt e i := H.endAt e.1 i
  loopless e := H.loopless e.1

/-- The vertex set belonging to one class of a setoid partition. -/
noncomputable def classFinset (P : Setoid V) (q : Quotient P) : Finset V := by
  classical
  exact Finset.univ.filter fun v => Quotient.mk P v = q

omit [DecidableEq V] [DecidableEq E] in
@[simp]
theorem mem_classFinset {P : Setoid V} {q : Quotient P} {v : V} :
    v ∈ classFinset P q ↔ Quotient.mk P v = q := by
  classical
  simp [classFinset]

omit [DecidableEq V] [DecidableEq E] in
theorem classFinset_nonempty (P : Setoid V) (q : Quotient P) :
    (classFinset P q).Nonempty := by
  induction q using Quotient.inductionOn with
  | _ v => exact ⟨v, by simp⟩

omit [DecidableEq V] [DecidableEq E] in
theorem classFinset_ne_univ (P : Setoid V) [Nontrivial (Quotient P)]
    (q : Quotient P) : classFinset P q ≠ Finset.univ := by
  obtain ⟨r, hr⟩ := exists_ne q
  induction r using Quotient.inductionOn with
  | _ v =>
      intro hEq
      have hv : v ∈ classFinset P q := by rw [hEq]; simp
      exact hr (by simpa using hv)

omit [DecidableEq V] [DecidableEq E] in
/-- Doubling edge objects doubles the number of crossing edges of every partition. -/
theorem crossingEdges_doubleGraph_card (P : Setoid V) :
    ((H.doubleGraph).crossingEdges P).card =
      2 * (H.crossingEdges P).card := by
  classical
  have hEq : (H.doubleGraph).crossingEdges P =
      (H.crossingEdges P) ×ˢ (Finset.univ : Finset (Fin 2)) := by
    ext e
    simp [mem_crossingEdges, Finset.mem_product, doubleGraph]
  rw [hEq, Finset.card_product]
  simp [Nat.mul_comm]

private theorem sum_xor_eq_two {α : Type*} [Fintype α] [DecidableEq α]
    (a b : α) (hab : a ≠ b) :
    ∑ q : α, (if (a = q) ≠ (b = q) then 1 else 0) = 2 := by
  calc
    ∑ q : α, (if (a = q) ≠ (b = q) then 1 else 0) =
        ∑ q : α, ((if a = q then 1 else 0) + if b = q then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro q _
      by_cases ha : a = q
      · by_cases hb : b = q
        · exact (hab (ha.trans hb.symm)).elim
        · simp [ha, hb]
      · by_cases hb : b = q <;> simp [ha, hb]
    _ = (∑ q : α, if a = q then 1 else 0) +
        ∑ q : α, if b = q then 1 else 0 := Finset.sum_add_distrib
    _ = 2 := by simp

omit [DecidableEq V] [DecidableEq E] in
@[simp]
theorem mem_cut_classFinset {P : Setoid V} {q : Quotient P} {e : E} :
    e ∈ H.cut (classFinset P q) ↔
      (Quotient.mk P (H.endAt e 0) = q) ≠
        (Quotient.mk P (H.endAt e 1) = q) := by
  classical
  simp [H.mem_cut_iff, Crosses]

omit [DecidableEq V] in
/-- Summing the cuts of all partition classes counts each crossing edge twice. -/
theorem sum_card_cut_classFinset (P : Setoid V) :
    (∑ q : Quotient P, (H.cut (classFinset P q)).card) =
      2 * (H.crossingEdges P).card := by
  classical
  calc
    (∑ q : Quotient P, (H.cut (classFinset P q)).card) =
        ∑ q : Quotient P, ∑ e : E,
          if e ∈ H.cut (classFinset P q) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      calc
        (H.cut (classFinset P q)).card =
            ∑ e ∈ H.cut (classFinset P q), 1 := Finset.card_eq_sum_ones _
        _ = ∑ e : E, if e ∈ H.cut (classFinset P q) then 1 else 0 := by
          rw [← Finset.sum_filter]
          congr 1
          ext e
          simp
    _ = ∑ e : E, ∑ q : Quotient P,
          if e ∈ H.cut (classFinset P q) then 1 else 0 := Finset.sum_comm
    _ = ∑ e : E, if e ∈ H.crossingEdges P then 2 else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      let a : Quotient P := Quotient.mk P (H.endAt e 0)
      let b : Quotient P := Quotient.mk P (H.endAt e 1)
      by_cases hab : a = b
      · have hrel : P.r (H.endAt e 0) (H.endAt e 1) := Quotient.eq'.mp hab
        have hnot : e ∉ H.crossingEdges P := fun hmem =>
          (H.mem_crossingEdges.mp hmem) hrel
        simp [mem_cut_classFinset, a, b, hab, hnot]
      · have hnrel : ¬ P.r (H.endAt e 0) (H.endAt e 1) := by
          intro hrel
          exact hab (Quotient.sound hrel)
        have hmem : e ∈ H.crossingEdges P := H.mem_crossingEdges.mpr hnrel
        rw [if_pos hmem]
        simpa [mem_cut_classFinset, a, b] using sum_xor_eq_two a b hab
    _ = 2 * (H.crossingEdges P).card := by
      calc
        (∑ e : E, if e ∈ H.crossingEdges P then 2 else 0) =
            ∑ e ∈ H.crossingEdges P, 2 := by
          rw [← Finset.sum_filter]
          congr 1
          ext e
          simp
        _ = 2 * (H.crossingEdges P).card := by
          simp [Nat.mul_comm]

omit [DecidableEq V] in
/-- Three-edge-connectivity of `H` makes its doubled graph satisfy the
Nash-Williams--Tutte condition for three spanning trees. -/
theorem doubleGraph_satisfiesTreePackingCondition_of_threeEdgeConnected [Nonempty V]
    (h3 : H.IsThreeEdgeConnected) :
    (H.doubleGraph).SatisfiesTreePackingCondition 3 := by
  intro P
  by_cases hsub : Subsingleton (Quotient P)
  · have hcard : Nat.card (Quotient P) ≤ 1 := by
      simpa [Nat.card_eq_fintype_card] using
        (Fintype.card_le_one_iff_subsingleton.mpr hsub)
    omega
  · letI : Nontrivial (Quotient P) := not_subsingleton_iff_nontrivial.mp hsub
    have hsum : (∑ _q : Quotient P, 3) ≤
        ∑ q : Quotient P, (H.cut (classFinset P q)).card := by
      apply Finset.sum_le_sum
      intro q _
      exact h3 (classFinset P q) (classFinset_nonempty P q)
        (classFinset_ne_univ P q)
    have hleft : (∑ _q : Quotient P, 3) = 3 * Nat.card (Quotient P) := by
      simp [Nat.card_eq_fintype_card, Nat.mul_comm]
    rw [hleft, H.sum_card_cut_classFinset P] at hsum
    rw [H.crossingEdges_doubleGraph_card P]
    omega

/-- A three-edge-connected graph has three spanning trees such that every original edge
is omitted by at least one of them.  Pack three trees in the doubled multigraph and then
forget which of the two copies was used. -/
theorem exists_three_spanningTrees_omitting_each_edge [Nonempty V]
    (h3 : H.IsThreeEdgeConnected) :
    ∃ T : Fin 3 → Finset E,
      (∀ i, H.IsSpanningTree (T i)) ∧
        ∀ e : E, ∃ i : Fin 3, e ∉ T i := by
  classical
  have hpack : (H.doubleGraph).HasTreePacking 3 :=
    ((H.doubleGraph).nashWilliamsTutte 3).2
      (H.doubleGraph_satisfiesTreePackingCondition_of_threeEdgeConnected h3)
  obtain ⟨U, hUtree, hUdisj⟩ := hpack
  let T : Fin 3 → Finset E := fun i => (U i).image Prod.fst
  have hTtree : ∀ i, H.IsSpanningTree (T i) := by
    intro i
    have hconn : H.Connects (T i) := by
      refine { preconnected := ?_ }
      intro u v
      apply FiniteGraph.reachable_of_adj_reachable
        (H := (H.doubleGraph).supportGraph (U i))
        (K := H.supportGraph (T i))
      · intro x y hxy
        rw [(H.doubleGraph).supportGraph_adj_iff (U i) x y] at hxy
        apply SimpleGraph.Adj.reachable
        rw [H.supportGraph_adj_iff (T i) x y]
        rcases hxy with ⟨hxy, e, heU, hends⟩
        refine ⟨hxy, e.1, ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨e, heU, rfl⟩
        · simpa [doubleGraph] using hends
      · exact (hUtree i).1.preconnected u v
    have hinj : Set.InjOn Prod.fst (U i : Set (E × Fin 2)) := by
      intro a ha b hb hab
      apply (H.doubleGraph).symEdge_injOn_of_spanningTree (hUtree i) ha hb
      simp [symEdge, doubleGraph, hab]
    have hcard : (T i).card = (U i).card := by
      exact Finset.card_image_of_injOn hinj
    exact ⟨hconn, by rw [hcard]; exact (hUtree i).2⟩
  refine ⟨T, hTtree, ?_⟩
  intro e
  by_contra hall
  push Not at hall
  choose x hxU hxe using fun i => Finset.mem_image.mp (hall i)
  let j : Fin 3 → Fin 2 := fun i => (x i).2
  have hjinj : Function.Injective j := by
    intro i k hj
    have hx : x i = x k := by
      apply Prod.ext
      · exact (hxe i).trans (hxe k).symm
      · exact hj
    by_contra hik
    exact (Finset.disjoint_left.mp (hUdisj i k hik)
      (hxU i) (hx ▸ hxU k)).elim
  have hle := Fintype.card_le_of_injective j hjinj
  norm_num at hle

/-- The direct Jaeger construction in the three-edge-connected case. -/
theorem nowhereZeroGammaFlow_of_threeEdgeConnected [Nonempty V]
    (h3 : H.IsThreeEdgeConnected) :
    Nonempty (H.NowhereZeroFlow Gamma) := by
  obtain ⟨T, hTtree, homit⟩ := H.exists_three_spanningTrees_omitting_each_edge h3
  choose F hEven hsup using fun i =>
    H.exists_even_superset_compl_of_spanningTree (T i) (hTtree i)
  apply H.nowhereZeroGammaFlow_of_evenCover F hEven
  intro e
  obtain ⟨i, hei⟩ := homit e
  exact ⟨i, hsup i e hei⟩

end FiniteGraph

end CycleDoubleCover
