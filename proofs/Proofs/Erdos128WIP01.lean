import Mathlib

/-
# Erdős #128 — foundational structure: triangle-freeness is hereditary, edge count is monotone
# (erdos-128-wip-01)

## The Problem

**Erdős Problem #128** ($250, OPEN). If every induced subgraph of an `n`-vertex
graph `G` on `≥ ⌊n/2⌋` vertices has more than `n²/50` edges, must `G` contain a
triangle? The constant `1/50` is conjectured optimal (blow-ups of `C₅` are
triangle-free with subgraph density `> 1/50`).

The scaffold `Erdos128Problem.lean` sets up the objects — `Graph`, `edgeCount`,
`induce`, `hasTriangle`, `triangleFree`, `denseSubgraphs` — and records the known
partial results (EFRS `1/16`, Krivelevich, Razborov `27/1024`, Norin–Yepremyan)
as prose, but proves **no theorems** (and currently fails to build: a missing
`DecidablePred` instance and trailing docstrings). This file is therefore
self-contained, re-declaring the objects (with classical decidability for the
edge count), and supplies their first structural theorems.

## Result

The two monotonicity properties of induced subgraphs that any analysis uses:

1. `hasTriangle_induce` — a triangle in an induced subgraph is a triangle of the
   ambient graph.

2. `triangleFree_induce` — hence **triangle-freeness is hereditary**: every
   induced subgraph of a triangle-free graph is triangle-free. (The extremal
   `C₅`-blow-up witnesses are triangle-free precisely because all their induced
   subgraphs are.)

3. `edgeCount_induce_le` — the **edge count is monotone**: an induced subgraph has
   no more edges than the whole graph.

4. `triangleFree_of_no_edges` — a graph with no edges is triangle-free.

## Summary: 0 sorries, 0 axioms, no `native_decide`. Self-contained over Mathlib.
-/

set_option linter.unusedVariables false

open Classical

namespace Erdos128WIP01

/-- A simple graph on `n` vertices. -/
structure Graph (n : ℕ) where
  adj : Fin n → Fin n → Prop
  symm : ∀ u v, adj u v → adj v u
  irrefl : ∀ v, ¬ adj v v

/-- The number of edges in a graph. -/
noncomputable def Graph.edgeCount {n : ℕ} (G : Graph n) : ℕ :=
  Finset.card ((Finset.univ.product Finset.univ).filter
    (fun p : Fin n × Fin n => p.1 < p.2 ∧ G.adj p.1 p.2))

/-- The induced subgraph on a subset `S` of vertices. -/
def Graph.induce {n : ℕ} (G : Graph n) (S : Finset (Fin n)) : Graph n where
  adj u v := u ∈ S ∧ v ∈ S ∧ G.adj u v
  symm u v h := ⟨h.2.1, h.1, G.symm u v h.2.2⟩
  irrefl v h := G.irrefl v h.2.2

/-- `G` contains a triangle: three mutually adjacent vertices. -/
def Graph.hasTriangle {n : ℕ} (G : Graph n) : Prop :=
  ∃ u v w : Fin n, u ≠ v ∧ v ≠ w ∧ u ≠ w ∧
    G.adj u v ∧ G.adj v w ∧ G.adj u w

/-- `G` is triangle-free. -/
def Graph.triangleFree {n : ℕ} (G : Graph n) : Prop := ¬ G.hasTriangle

/-- **A triangle in an induced subgraph is a triangle of the whole graph.** The
    induced adjacency `(G.induce S).adj u v` entails `G.adj u v`. -/
theorem hasTriangle_induce {n : ℕ} (G : Graph n) (S : Finset (Fin n))
    (h : (G.induce S).hasTriangle) : G.hasTriangle := by
  obtain ⟨u, v, w, huv, hvw, huw, a1, a2, a3⟩ := h
  exact ⟨u, v, w, huv, hvw, huw, a1.2.2, a2.2.2, a3.2.2⟩

/-- **Triangle-freeness is hereditary.** Every induced subgraph of a triangle-free
    graph is triangle-free — the contrapositive of `hasTriangle_induce`. -/
theorem triangleFree_induce {n : ℕ} (G : Graph n) (S : Finset (Fin n))
    (hG : G.triangleFree) : (G.induce S).triangleFree :=
  fun hInd => hG (hasTriangle_induce G S hInd)

/-- **The edge count is monotone under taking induced subgraphs.** Induction only
    deletes edges, so `(G.induce S).edgeCount ≤ G.edgeCount`. -/
theorem edgeCount_induce_le {n : ℕ} (G : Graph n) (S : Finset (Fin n)) :
    (G.induce S).edgeCount ≤ G.edgeCount := by
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1, hp.2.2.2.2⟩

/-- **The degenerate base case.** A graph whose adjacency is everywhere false has
    no triangle. -/
theorem triangleFree_of_no_edges {n : ℕ} (G : Graph n)
    (hG : ∀ u v, ¬ G.adj u v) : G.triangleFree := by
  rintro ⟨u, v, w, -, -, -, a1, -, -⟩
  exact hG u v a1

/-
## Significance

Erdős #128 asks whether sufficient edge density on every large induced subgraph
forces a triangle. Any approach manipulates two basic monotonicities of the
induced-subgraph operation, which the scaffold leaves unproved (and which fail to
even compile there). This file supplies them: triangle-freeness passes to induced
subgraphs (`triangleFree_induce`), and the edge count cannot increase under
induction (`edgeCount_induce_le`). The first is exactly why the extremal
`C₅`-blow-up witnesses are triangle-free — the property is hereditary — and the
second is the monotonicity underlying the density hypothesis `denseSubgraphs`.
These are the first theorems on the scaffold's objects; the hard analytic core
(the optimal constant `1/50`) remains open.
-/

end Erdos128WIP01
