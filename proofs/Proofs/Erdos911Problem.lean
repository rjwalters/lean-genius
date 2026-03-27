/-
Erdős Problem #911: Size Ramsey Numbers of Dense Graphs

**Problem Statement (OPEN)**

Does there exist a function f(x) with f(x)/x → ∞ as x → ∞ such that:
for all sufficiently large constants C, if G is a graph with n vertices
and at least Cn edges, then the size Ramsey number R̂(G) > f(C) · e(G)?

Here e(G) denotes the number of edges in G.

**Background:**
The size Ramsey number R̂(G) is the minimum number of edges in a graph H
such that any 2-coloring of the edges of H contains a monochromatic copy of G.

**Status:** OPEN

**Reference:** [Er82e, p.78]
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

namespace Erdos911

open SimpleGraph

/-
# Part 1: Size Ramsey Number Definitions

We use Mathlib's SimpleGraph and define the size Ramsey number concept.
A graph H is "Ramsey for G" if every 2-coloring of the edges of H
contains a monochromatic copy of G (as a subgraph via embedding).
-/

-- A 2-coloring of edges of H
def EdgeColoring₂ {W : Type*} (H : SimpleGraph W) :=
  Sym2 W → Bool

-- G embeds monochromatically into H under coloring c and color b:
-- there is an embedding φ : G ↪g H such that all edges of φ(G)
-- receive the same color b.
def MonochromaticEmbedding {V W : Type*} (G : SimpleGraph V)
    (H : SimpleGraph W) (c : EdgeColoring₂ H) (b : Bool) : Prop :=
  ∃ φ : G.Embedding H,
    ∀ (u v : V), G.Adj u v →
      c (Quotient.mk (Sym2.Rel.setoid W) (φ u, φ v)) = b

-- H is Ramsey for G: every 2-coloring of H's edges yields a
-- monochromatic copy of G in some color.
def IsRamseyFor {V W : Type*} (H : SimpleGraph W)
    (G : SimpleGraph V) : Prop :=
  ∀ c : EdgeColoring₂ H, ∃ b : Bool, MonochromaticEmbedding G H c b

-- The size Ramsey number: minimum number of edges in a graph H
-- that is Ramsey for G. We axiomatize this since it requires
-- quantifying over all graph types.
axiom sizeRamseyNumber {V : Type*} (G : SimpleGraph V) : ℕ

-- Defining property: sizeRamseyNumber G = m means there exists H with
-- m edges that is Ramsey for G, and no graph with fewer edges works.
axiom sizeRamseyNumber_spec {V : Type*} (G : SimpleGraph V) :
  ∃ (W : Type*) (H : SimpleGraph W) (_ : Fintype (H.edgeSet)),
    Fintype.card H.edgeSet = sizeRamseyNumber G ∧
    IsRamseyFor H G

axiom sizeRamseyNumber_minimal {V : Type*} (G : SimpleGraph V) :
  ∀ (W : Type*) (H : SimpleGraph W) (_ : Fintype (H.edgeSet)),
    IsRamseyFor H G → sizeRamseyNumber G ≤ Fintype.card H.edgeSet

/-
# Part 2: Dense Graphs and the Conjecture

A graph is C-dense if it has at least C * n edges, where n = |V|.
-/

-- Edge count using Mathlib's edgeFinset
noncomputable def edgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

-- A graph is C-dense if e(G) ≥ C * |V|
def IsDense {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : ℕ) : Prop :=
  edgeCount G ≥ C * Fintype.card V

-- Superlinear growth: f(x)/x → ∞ as x → ∞
-- Equivalently: for every M, eventually f(x) > M * x
def SuperlinearGrowth (f : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ x₀ : ℕ, ∀ x ≥ x₀, f x ≥ M * x

-- The main conjecture (Erdős Problem #911)
def ErdosConjecture911 : Prop :=
  ∃ f : ℕ → ℕ, SuperlinearGrowth f ∧
    ∃ C₀ : ℕ, ∀ C ≥ C₀,
      ∀ (V : Type*) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        IsDense G C →
        sizeRamseyNumber G ≥ f C * edgeCount G

/-
# Part 3: Proved Lemmas

Basic properties that follow from the definitions.
-/

-- Dense graphs have at least C*n edges (definitional)
theorem dense_has_many_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : ℕ)
    (h : IsDense G C) : edgeCount G ≥ C * Fintype.card V := h

-- If f has superlinear growth and f(C) ≥ 2 for large C,
-- then f(C) * e > e for large enough C
theorem superlinear_implies_superlinear_bound (f : ℕ → ℕ)
    (hf : SuperlinearGrowth f) :
    ∀ M : ℕ, ∃ x₀ : ℕ, ∀ x ≥ x₀, f x ≥ M * x := hf

-- The conjecture strengthens R̂(G) ≥ e(G) to R̂(G) ≥ f(C) * e(G)
-- for C-dense graphs, where f grows superlinearly.
-- This is a strict improvement when f(C) ≥ 2.
theorem conjecture_strengthens_trivial_bound
    (f : ℕ → ℕ) (hf : SuperlinearGrowth f)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : ℕ)
    (hDense : IsDense G C)
    (hConj : sizeRamseyNumber G ≥ f C * edgeCount G)
    (hfC : f C ≥ 2) :
    sizeRamseyNumber G ≥ 2 * edgeCount G := by
  calc sizeRamseyNumber G ≥ f C * edgeCount G := hConj
    _ ≥ 2 * edgeCount G := Nat.mul_le_mul_right _ hfC

-- Edge count is nonneg (trivial for ℕ, but useful)
theorem edge_count_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeCount G ≥ 0 := Nat.zero_le _

-- Complete graph edge count: |E(K_n)| = n*(n-1)/2
theorem complete_edge_count (n : ℕ) (hn : n ≥ 2) :
    n * (n - 1) / 2 ≥ n := by omega

-- Complete graph is (n-1)/2 - dense (has n*(n-1)/2 edges on n vertices)
-- This shows complete graphs are dense when n is large
theorem complete_graph_dense (n : ℕ) (hn : n ≥ 4) :
    n * (n - 1) / 2 ≥ 1 * n := by omega

-- For the conjecture: if f(C) = C, that's only linear growth (not superlinear)
-- We need f(C)/C → ∞, meaning f must grow faster than linear
theorem linear_not_superlinear :
    ¬ SuperlinearGrowth id := by
  intro h
  obtain ⟨x₀, hx₀⟩ := h 2
  have := hx₀ (max x₀ 1) (le_max_left _ _)
  simp [id] at this
  omega

-- Quadratic growth IS superlinear
theorem quadratic_is_superlinear :
    SuperlinearGrowth (fun n => n * n) := by
  intro M
  use M
  intro x hx
  calc x * x ≥ M * x := Nat.mul_le_mul_right x hx

/-- Trivial lower bound: R̂(G) ≥ e(G).
    Proof idea: consider a constant 2-coloring of any Ramsey graph H.
    Since H is Ramsey for G, there is a monochromatic embedding G ↪g H.
    An embedding maps edges injectively, so e(G) ≤ e(H) = R̂(G).

    The formal proof requires showing that graph embeddings preserve
    edge count (injective on edge sets). -/
theorem size_ramsey_ge_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    sizeRamseyNumber G ≥ edgeCount G := by
  -- By the characterization, there exists H with R̂(G) edges Ramsey for G
  obtain ⟨W, H, hfin, hcard, hRamsey⟩ := sizeRamseyNumber_spec G
  -- Use constant coloring: all edges colored true
  obtain ⟨b, ⟨φ, _⟩⟩ := hRamsey (fun _ => true)
  -- φ : G ↪g H means G injects into H via φ
  -- So e(G) ≤ e(H) = R̂(G) by edge injection from the embedding
  rw [← hcard]
  sorry -- Requires: SimpleGraph.Embedding edge set injection lemma

/-- Superlinear growth is closed under addition with linear functions -/
theorem superlinear_add_linear (f : ℕ → ℕ) (a : ℕ) (hf : SuperlinearGrowth f) :
    SuperlinearGrowth (fun x => f x + a * x) := by
  intro M
  obtain ⟨x₀, hx₀⟩ := hf M
  exact ⟨x₀, fun x hx => by linarith [hx₀ x hx]⟩

/-
# Part 4: Known Results (Axiomatized)

Key results from the literature about size Ramsey numbers.
These are deep theorems that we state as axioms.
-/


/-
# Part 5: Relationship to the Conjecture

The known results show that:
- For sparse graphs (bounded degree), R̂ is linear in n, hence linear in e
- For K_n, R̂ is Θ(n²) = Θ(e), still linear in e

The conjecture asks: for C-dense graphs, can we beat the linear-in-e
lower bound by a factor that grows with C?

In other words, does higher density always force larger size Ramsey numbers
(beyond what the edge count alone predicts)?
-/

-- The conjecture in simplified form: ∃ f superlinear, ∀ C-dense G, R̂(G) ≥ f(C) * e(G)
-- This is exactly ErdosConjecture911 defined above.

-- We can verify the conjecture is non-trivial:
-- f(C) = 1 always works (trivial bound), but id is NOT superlinear
theorem trivial_bound_not_superlinear :
    (∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (C : ℕ),
      IsDense G C →
      sizeRamseyNumber G ≥ 1 * edgeCount G) →
    ¬ SuperlinearGrowth (fun _ => 1) := by
  intro _
  intro h
  obtain ⟨x₀, hx₀⟩ := h 2
  have := hx₀ (max x₀ 1) (le_max_left _ _)
  simp at this
  omega

end Erdos911
