/-
Copyright (c) 2024-2026 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Minimum-Degree Corollary of Mantel's Theorem

Mantel's theorem bounds the *number of edges* of a triangle-free graph by `⌊n²/4⌋`.
A complementary, often more useful local statement bounds the *minimum degree*:

> Every triangle-free (`K₃`-free, i.e. `CliqueFree 3`) simple graph on `n ≥ 1` vertices has a
> vertex of degree at most `⌊n/2⌋`.

## Approach

The proof is the classical neighbourhood-disjointness argument and does **not** require the full
edge bound of `MantelTheorem.lean`:

* For an edge `u ~ v` in a triangle-free graph the neighbourhoods `N(u)` and `N(v)` are disjoint:
  a common neighbour `x` would make `{u, v, x}` a triangle
  (`neighborFinset_disjoint_of_adj`).
* Hence for any edge `u ~ v` we get `deg u + deg v = |N(u) ∪ N(v)| ≤ n`
  (`degree_add_degree_le_card_of_adj`).
* If *every* vertex had degree `> n/2`, the graph would have an edge (every vertex has positive
  degree), and its two endpoints would violate the degree-sum bound. So some vertex has degree
  `≤ ⌊n/2⌋` (`exists_degree_two_mul_le_card`, `exists_degree_le_card_div_two`).

The contrapositive is a Turán-type *forcing* statement: a large minimum degree guarantees a
triangle (`exists_triangle_of_min_degree_large`).

The `⌊n/2⌋` bound is sharp: a balanced complete bipartite graph is triangle-free and every vertex
has degree `⌈n/2⌉` or `⌊n/2⌋`, so the minimum degree is exactly `⌊n/2⌋`.
-/

open Finset SimpleGraph

namespace MantelMinDegree

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In a triangle-free graph the neighbourhoods of two adjacent vertices are disjoint: a common
neighbour `x` of `u` and `v` would complete the triangle `{u, v, x}`. -/
theorem neighborFinset_disjoint_of_adj (h : G.CliqueFree 3) {u v : V} (huv : G.Adj u v) :
    Disjoint (G.neighborFinset u) (G.neighborFinset v) := by
  rw [Finset.disjoint_left]
  intro x hxu hxv
  have hux : G.Adj u x := (G.mem_neighborFinset u x).mp hxu
  have hvx : G.Adj v x := (G.mem_neighborFinset v x).mp hxv
  exact h {u, v, x} (G.is3Clique_triple_iff.mpr ⟨huv, hux, hvx⟩)

/-- For an edge `u ~ v` of a triangle-free graph the degrees of the endpoints sum to at most the
number of vertices, since their neighbourhoods are disjoint subsets of the vertex set. -/
theorem degree_add_degree_le_card_of_adj (h : G.CliqueFree 3) {u v : V} (huv : G.Adj u v) :
    G.degree u + G.degree v ≤ Fintype.card V := by
  have hdisj := neighborFinset_disjoint_of_adj G h huv
  have hunion : (G.neighborFinset u ∪ G.neighborFinset v).card = G.degree u + G.degree v := by
    rw [Finset.card_union_of_disjoint hdisj, G.card_neighborFinset_eq_degree,
      G.card_neighborFinset_eq_degree]
  have hle : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ Fintype.card V := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  omega

/-- **Minimum-degree corollary of Mantel's theorem.** A triangle-free simple graph on a nonempty
vertex set has a vertex `v` with `2 · deg v ≤ n`, i.e. `deg v ≤ ⌊n/2⌋`. -/
theorem exists_degree_two_mul_le_card [Nonempty V] (h : G.CliqueFree 3) :
    ∃ v, 2 * G.degree v ≤ Fintype.card V := by
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ v, Fintype.card V < 2 * G.degree v`
  set v₀ := Classical.arbitrary V with hv₀
  have hcard_pos : 0 < Fintype.card V := Fintype.card_pos
  have hpos : 0 < G.degree v₀ := by have := hcon v₀; omega
  have hne : (G.neighborFinset v₀).Nonempty := by
    rw [← Finset.card_pos, G.card_neighborFinset_eq_degree]; exact hpos
  obtain ⟨w, hw⟩ := hne
  have hadj : G.Adj v₀ w := (G.mem_neighborFinset v₀ w).mp hw
  have hkey := degree_add_degree_le_card_of_adj G h hadj
  have h1 := hcon v₀
  have h2 := hcon w
  omega

/-- Restatement of the minimum-degree corollary with explicit floor: a triangle-free graph on a
nonempty vertex set has a vertex of degree at most `⌊n/2⌋`. -/
theorem exists_degree_le_card_div_two [Nonempty V] (h : G.CliqueFree 3) :
    ∃ v, G.degree v ≤ Fintype.card V / 2 := by
  obtain ⟨v, hv⟩ := exists_degree_two_mul_le_card G h
  exact ⟨v, by omega⟩

/-- **Turán-type forcing (contrapositive).** If every vertex of a graph on a nonempty vertex set
has degree strictly greater than `n/2` (`n < 2 · deg v` for all `v`), the graph contains a
triangle. -/
theorem exists_triangle_of_min_degree_large [Nonempty V]
    (hdeg : ∀ v, Fintype.card V < 2 * G.degree v) :
    ∃ s, G.IsNClique 3 s := by
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ s, ¬ G.IsNClique 3 s`, i.e. `G.CliqueFree 3`
  obtain ⟨v, hv⟩ := exists_degree_two_mul_le_card G hcon
  exact absurd (hdeg v) (by omega)

end MantelMinDegree
