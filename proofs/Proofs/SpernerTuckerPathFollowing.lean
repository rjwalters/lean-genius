/-
# Abstract path-following parity engine for Tucker's lemma (n ≥ 2)

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam
from abstract door-counting").

## Background

Sperner's lemma is proved by a *door-counting* parity argument: a certain target
object (a panchromatic cell) is counted modulo 2 and shown to be odd, hence
non-empty.  The companion file `SpernerTuckerOneDim.lean` shows that **n = 1
Tucker** (the combinatorial core of 1-D Borsuk–Ulam) is exactly such a direct
parity statement: the number of *complementary edges* of a sign labelling that is
antipodal on the boundary is always odd.

That direct route **provably does not lift to n ≥ 2**: `SpernerTuckerHexagon.lean`
exhibits, in Lean, antipodal labellings of the hexagon+centre triangulation of
`B²` whose complementary-edge counts have *both* parities
(`count_parity_not_invariant`).  So one cannot "count the complementary simplices
and show the total is odd."

The standard remedy (Freund–Todd 1981; Prescott–Su) is **path-following**.  One
builds a graph `G` on the *almost-complementary* simplices, where two such
simplices are adjacent when they share a complementary facet (a "door").  Every
almost-complementary simplex has at most two such doors, so **`G` has maximum
degree ≤ 2** — it is a disjoint union of paths and cycles.  The *endpoints* of
these paths (degree-1 vertices) are exactly:

* the genuinely **complementary** simplices (the interior target), and
* the almost-complementary simplices lying on the **boundary**.

The antipodal boundary condition forces the number of boundary endpoints to be
**odd** (this is the lower-dimensional Tucker statement, used as an induction
hypothesis).  Since the *total* number of endpoints is **even** (handshaking
lemma), an **odd**, hence non-zero, number of endpoints must be interior — a
complementary simplex exists.

## What this file proves

This file isolates and machine-checks the **combinatorial heart** of that
argument, fully abstractly over an arbitrary finite simple graph:

* `even_card_degree_one` — in any finite simple graph of maximum degree ≤ 2, the
  number of degree-1 vertices is even (the handshaking lemma specialised to
  paths-and-cycles graphs).
* `exists_interior_degree_one` — the **path-following step**: if a "boundary"
  predicate `B` marks an *odd* number of the degree-1 vertices, then some degree-1
  vertex is *interior* (`¬ B`).

Instantiating `G` with the almost-complementary-simplex graph and `B` with "lies
on the antipodal boundary" turns `exists_interior_degree_one` into the existence
of an interior complementary simplex, i.e. Tucker's lemma.  The geometric
construction of that graph (and the proof that boundary endpoints are odd) is the
remaining, dimension-specific work; the parity bookkeeping that *drives* it is
verified here, 0 sorries, 0 axioms.
-/
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

namespace SpernerTuckerPathFollowing

open Finset SimpleGraph

variable {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]

/-- In a graph where every vertex has degree at most `2`, having odd degree is the
same as having degree exactly `1`.  (Degrees lie in `{0, 1, 2}`; the odd one is
`1`.) -/
theorem odd_degree_iff_eq_one (h : ∀ v, G.degree v ≤ 2) (v : V) :
    Odd (G.degree v) ↔ G.degree v = 1 := by
  rw [Nat.odd_iff]
  have := h v
  omega

/-- **Path-following parity engine.**  In a finite simple graph in which every
vertex has degree at most `2` — equivalently, a disjoint union of paths and
cycles — the number of degree-1 vertices is **even**.

These degree-1 vertices are the endpoints of the constituent paths; this is the
handshaking lemma specialised to the almost-complementary-simplex graph used in
the Freund–Todd / Prescott–Su proof of Tucker's lemma. -/
theorem even_card_degree_one (h : ∀ v, G.degree v ≤ 2) :
    Even #{v | G.degree v = 1} := by
  have hset : ({v | G.degree v = 1} : Finset V) = ({v | Odd (G.degree v)} : Finset V) := by
    apply Finset.filter_congr
    intro v _
    exact (odd_degree_iff_eq_one G h v).symm
  rw [hset]
  exact G.even_card_odd_degree_vertices

/-- **Tucker path-following step.**  Let `B` be a "boundary" predicate on the
vertices of a maximum-degree-≤2 graph.  If an **odd** number of degree-1 vertices
are boundary vertices, then there is a degree-1 vertex that is **not** a boundary
vertex (an *interior* endpoint).

In the path-following proof of Tucker's lemma, `G` is the graph of
almost-complementary simplices, the degree-1 vertices are the path endpoints, and
`B v` says "`v` lies on the antipodal boundary".  The antipodal boundary
condition makes the number of boundary endpoints odd, so this lemma yields an
interior endpoint, i.e. a complementary simplex. -/
theorem exists_interior_degree_one {B : V → Prop} [DecidablePred B]
    (h : ∀ v, G.degree v ≤ 2)
    (hbdry : Odd #{v | G.degree v = 1 ∧ B v}) :
    ∃ v, G.degree v = 1 ∧ ¬ B v := by
  classical
  have heven : Even #{v | G.degree v = 1} := even_card_degree_one G h
  -- Split the degree-1 vertices according to the boundary predicate `B`:
  -- the boundary part `s.filter B` is the boundary-endpoint count, and the
  -- complementary part is the interior-endpoint count.
  have e1 : #(({v | G.degree v = 1} : Finset V).filter B)
      = #{v | G.degree v = 1 ∧ B v} := by
    rw [Finset.filter_filter]
  have e2 : #(({v | G.degree v = 1} : Finset V).filter (fun a => ¬ B a))
      = #{v | G.degree v = 1 ∧ ¬ B v} := by
    rw [Finset.filter_filter]
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := ({v | G.degree v = 1} : Finset V)) (p := B)
  rw [e1, e2] at hsplit
  -- Total endpoints is even; boundary endpoints odd ⟹ interior endpoints odd > 0.
  rw [Nat.even_iff] at heven
  rw [Nat.odd_iff] at hbdry
  have hpos : 0 < #{v | G.degree v = 1 ∧ ¬ B v} := by omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hv
  exact ⟨v, hv.2⟩

end SpernerTuckerPathFollowing
