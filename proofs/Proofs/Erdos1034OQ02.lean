/-
Erdős Problem #1034 — OQ-02: The book-lemma lower-bound mechanism, made exact

Erdős #1034 asks: if `G` has `n` vertices and `> n²/4` edges, must there exist a
triangle `T` and `> (1/2 - o(1))n` vertices each adjacent to at least two vertices
of `T`?  This was **disproved** by Ma–Tang, who give a construction with at most
`(2 - √(5/2) + o(1))n ≈ 0.419n` such "good neighbours".  The current bounds on the
threshold function `h(n)` are

        (1/6 - o(1))·n  ≤  h(n)  ≤  (2 - √(5/2) + o(1))·n.

The lower bound `n/6` comes from the **book lemma**: a graph with `> n²/4` edges
contains an edge lying in many common-neighbour triangles (a "book"), and the pages
of that book are automatically good neighbours of any triangle on the spine.

OQ-02 asks whether `n/6` can be improved *beyond* the book lemma.  This file does
not resolve that (genuinely open) question.  Instead it **formalizes the engine of
the lower bound exactly**:

  * `book_le_goodNeighborCount` — the general structural theorem.  If `{a,b}` is an
    edge and `P` is a set of common neighbours of `a` and `b` (a book with spine
    `{a,b}` and pages `P`), then the triangle `{a, b, p₀}` on the spine has at least
    `|P| - 1` good neighbours.  This is the precise mechanism translating "book of
    size `k`" into "triangle with `k - 1` good neighbours".

  * `book_goodNeighborCount_eq` — for the *pure* book graph (spine plus independent
    pages) the count is **exactly** `|P| - 1`: the book method delivers neither more
    nor fewer good neighbours than its page count.  Verified with a concrete witness
    on `Fin 5` by `decide` (no `native_decide`, so the result is axiom-free).

Every result is fully machine-checked with no `sorry`, no `axiom`, and no
`native_decide`.

Reference: https://erdosproblems.com/1034
-/
import Mathlib

open Finset

namespace Erdos1034OQ02

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A triangle in `G`: three mutually adjacent distinct vertices. -/
structure Triangle (G : SimpleGraph V) where
  v1 : V
  v2 : V
  v3 : V
  ne12 : v1 ≠ v2
  ne23 : v2 ≠ v3
  ne13 : v1 ≠ v3
  adj12 : G.Adj v1 v2
  adj23 : G.Adj v2 v3
  adj13 : G.Adj v1 v3

namespace Triangle
variable {G : SimpleGraph V}

/-- The three vertices of a triangle. -/
def vertices (T : Triangle G) : Finset V := {T.v1, T.v2, T.v3}

omit [Fintype V] in
@[simp] lemma mem_vertices {T : Triangle G} {y : V} :
    y ∈ T.vertices ↔ y = T.v1 ∨ y = T.v2 ∨ y = T.v3 := by
  simp [vertices]

end Triangle

/-- Number of triangle vertices adjacent to `y`. -/
def adjacentCount (G : SimpleGraph V) [DecidableRel G.Adj] (T : Triangle G) (y : V) : ℕ :=
  (T.vertices.filter (fun v => G.Adj y v)).card

/-- The set of **good neighbours** of `T`: vertices outside `T` adjacent to at least
two of `T`'s vertices. -/
def goodNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (T : Triangle G) : Finset V :=
  univ.filter (fun y => 2 ≤ adjacentCount G T y ∧ y ∉ T.vertices)

/-- The number of good neighbours of `T`. -/
def goodNeighborCount (G : SimpleGraph V) [DecidableRel G.Adj] (T : Triangle G) : ℕ :=
  (goodNeighbors G T).card

/-!
## The book bridge (general lower bound)

If `{a, b}` is an edge and `P` is a finset of common neighbours of `a` and `b`
(disjoint from `{a, b}`), then any triangle `{a, b, p₀}` on the spine has at least
`|P| - 1` good neighbours: every page other than `p₀` is adjacent to both `a` and
`b`, hence to two vertices of the triangle.
-/

theorem book_le_goodNeighborCount (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b p0 : V} (P : Finset V)
    (hp0 : p0 ∈ P) (haP : a ∉ P) (hbP : b ∉ P)
    (hab : G.Adj a b)
    (hPa : ∀ p ∈ P, G.Adj p a) (hPb : ∀ p ∈ P, G.Adj p b) :
    ∃ T : Triangle G, T.v1 = a ∧ T.v2 = b ∧ T.v3 = p0 ∧
      P.card - 1 ≤ goodNeighborCount G T := by
  -- assemble the spine triangle `{a, b, p0}`
  have hap0 : a ≠ p0 := fun h => haP (h ▸ hp0)
  have hbp0 : b ≠ p0 := fun h => hbP (h ▸ hp0)
  refine ⟨{ v1 := a, v2 := b, v3 := p0,
            ne12 := hab.ne, ne23 := hbp0, ne13 := hap0,
            adj12 := hab, adj23 := (hPb p0 hp0).symm, adj13 := (hPa p0 hp0).symm },
          rfl, rfl, rfl, ?_⟩
  set T : Triangle G :=
    { v1 := a, v2 := b, v3 := p0,
      ne12 := hab.ne, ne23 := hbp0, ne13 := hap0,
      adj12 := hab, adj23 := (hPb p0 hp0).symm, adj13 := (hPa p0 hp0).symm } with hT
  -- every page other than `p0` is a good neighbour
  have hsub : P.erase p0 ⊆ goodNeighbors G T := by
    intro q hq
    obtain ⟨hqp0, hqP⟩ := Finset.mem_erase.mp hq
    have hqa : G.Adj q a := hPa q hqP
    have hqb : G.Adj q b := hPb q hqP
    -- `{a, b}` sits inside the adjacency filter, giving count ≥ 2
    have hpair : ({a, b} : Finset V) ⊆ T.vertices.filter (fun v => G.Adj q v) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_filter.mpr ⟨by simp [T, Triangle.vertices], hqa⟩
      · rw [Finset.mem_singleton] at hx; subst hx
        exact Finset.mem_filter.mpr ⟨by simp [T, Triangle.vertices], hqb⟩
    have hcount : 2 ≤ adjacentCount G T q := by
      show 2 ≤ (T.vertices.filter (fun v => G.Adj q v)).card
      have hle := Finset.card_le_card hpair
      rwa [Finset.card_pair hab.ne] at hle
    -- `q` is outside the triangle
    have hqnot : q ∉ T.vertices := by
      simp only [Triangle.mem_vertices, hT]
      push_neg
      refine ⟨?_, ?_, hqp0⟩
      · exact fun h => haP (h ▸ hqP)
      · exact fun h => hbP (h ▸ hqP)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ q, hcount, hqnot⟩
  calc P.card - 1 = (P.erase p0).card := (Finset.card_erase_of_mem hp0).symm
    _ ≤ (goodNeighbors G T).card := Finset.card_le_card hsub
    _ = goodNeighborCount G T := rfl

/-!
## Sharpness: the pure book graph realizes the bound exactly

For the **pure** book graph — spine edge `{a, b}` together with pages that are
pairwise non-adjacent and joined only to `a` and `b` — the spine triangle has
*exactly* `|P| - 1` good neighbours.  Concretely, take spine `{0, 1}` and pages
`{2, 3, 4}` on `Fin 5`; the triangle `{0, 1, 2}` has good neighbours exactly
`{3, 4}`, i.e. `|P| - 1 = 2`.  So the book lemma's output equals its page count:
no good neighbours are gained or lost beyond the pages themselves.
-/

namespace Book

/-- Spine edge `{0,1}` plus pages `2,3,4`, each joined only to the spine. -/
def baseEdges : List (Fin 5 × Fin 5) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4)]

/-- The (symmetric) adjacency relation of the pure book graph on `Fin 5`. -/
def isEdge (i j : Fin 5) : Prop := (i, j) ∈ baseEdges ∨ (j, i) ∈ baseEdges

instance : DecidableRel isEdge := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The pure book graph on `Fin 5`. -/
def bookG : SimpleGraph (Fin 5) where
  Adj := isEdge
  symm := by intro i j h; exact h.symm
  loopless := by intro i; fin_cases i <;> decide

instance : DecidableRel bookG.Adj := fun i j => inferInstanceAs (Decidable (isEdge i j))

/-- The spine triangle `{0, 1, 2}` of the book graph. -/
def bookT : Triangle bookG where
  v1 := 0
  v2 := 1
  v3 := 2
  ne12 := by decide
  ne23 := by decide
  ne13 := by decide
  adj12 := by decide
  adj23 := by decide
  adj13 := by decide

/-- The pages of the book. -/
def pages : Finset (Fin 5) := {2, 3, 4}

/-- The spine triangle has exactly `|pages| - 1 = 2` good neighbours: the book
mechanism delivers precisely its page count. -/
theorem book_goodNeighborCount_eq : goodNeighborCount bookG bookT = pages.card - 1 := by
  decide

/-- Spelled out: the good neighbours are exactly the two pages `{3, 4}`. -/
theorem book_goodNeighbors_eq : goodNeighbors bookG bookT = {3, 4} := by
  decide

end Book

end Erdos1034OQ02
