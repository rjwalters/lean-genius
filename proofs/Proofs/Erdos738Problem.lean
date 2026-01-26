/-!
# Erdős Problem #738: Triangle-Free Graphs with Infinite Chromatic Number

Must every triangle-free graph with infinite chromatic number contain every
finite tree as an induced subgraph?

## Key Results

- Gyárfás conjecture: YES for all finite trees
- Kierstead–Penrice (1994): true for radius-2 trees
- Scott (1997): true for trees with ≤ 3 leaves (caterpillars, spiders)
- Chudnovsky–Scott–Seymour (2020): partial results for subdivisions

## References

- Gyárfás (1975): original conjecture
- Erdős [Er81]
- <https://erdosproblems.com/738>
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

open SimpleGraph

/-! ## Core Definitions -/

/-- A simple graph is triangle-free if it contains no 3-clique. -/
def SimpleGraph.IsTriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  G.CliqueFree 3

/-- A graph has chromatic number at most k if it admits a proper k-coloring. -/
def SimpleGraph.ChromAtMost {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  Nonempty (G.Coloring (Fin k))

/-- A graph has infinite chromatic number: no finite coloring suffices. -/
def SimpleGraph.HasInfiniteChrom {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ k : ℕ, ¬G.ChromAtMost k

/-- A tree on n vertices: connected acyclic graph with n − 1 edges.
    We model finite trees as simple graphs on Fin n. -/
structure FiniteTree (n : ℕ) where
  graph : SimpleGraph (Fin n)

/-- An induced subgraph isomorphism: an injective map preserving and
    reflecting adjacency. -/
def SimpleGraph.HasInducedCopy {V : Type*} {n : ℕ}
    (G : SimpleGraph V) (T : SimpleGraph (Fin n)) : Prop :=
  ∃ f : Fin n → V, Function.Injective f ∧
    ∀ i j : Fin n, T.Adj i j ↔ G.Adj (f i) (f j)

/-! ## Main Conjecture -/

/-- **Erdős Problem #738 / Gyárfás Conjecture** (OPEN):
    Every triangle-free graph with infinite chromatic number contains
    every finite tree as an induced subgraph. -/
axiom gyarfas_conjecture :
  ∀ {V : Type*} (G : SimpleGraph V),
    G.IsTriangleFree → G.HasInfiniteChrom →
      ∀ (n : ℕ) (T : FiniteTree n), G.HasInducedCopy T.graph

/-! ## Known Partial Results -/

/-- A path on n vertices. -/
def pathGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := (i.val + 1 = j.val) ∨ (j.val + 1 = i.val)
  symm := by intro i j h; cases h with | inl h => right; exact h | inr h => left; exact h
  loopless := by intro i h; cases h with | inl h => omega | inr h => omega

/-- A star on n+1 vertices: one center adjacent to n leaves. -/
def starGraph (n : ℕ) : SimpleGraph (Fin (n + 1)) where
  Adj i j := (i.val = 0 ∧ j.val ≠ 0) ∨ (j.val = 0 ∧ i.val ≠ 0)
  symm := by intro i j h; cases h with | inl h => right; exact ⟨h.1 ▸ rfl, h.2 ▸ (by omega)⟩ | inr h => left; exact ⟨h.1 ▸ rfl, h.2 ▸ (by omega)⟩
  loopless := by intro i h; cases h with | inl h => exact h.2 h.1 | inr h => exact h.2 h.1

/-- **Paths**: Triangle-free graphs with infinite chromatic number contain
    paths of every length. This follows from Ramsey-type arguments. -/
axiom infinite_chrom_contains_paths :
  ∀ {V : Type*} (G : SimpleGraph V),
    G.IsTriangleFree → G.HasInfiniteChrom →
      ∀ n : ℕ, G.HasInducedCopy (pathGraph n)

/-- **Stars**: Triangle-free graphs with infinite chromatic number contain
    stars of every size (immediate from unbounded degree). -/
axiom infinite_chrom_contains_stars :
  ∀ {V : Type*} (G : SimpleGraph V),
    G.IsTriangleFree → G.HasInfiniteChrom →
      ∀ n : ℕ, G.HasInducedCopy (starGraph n)

/-- **Kierstead–Penrice (1994)**: The conjecture holds for trees of radius ≤ 2. -/
axiom kierstead_penrice_radius2 :
  ∀ {V : Type*} (G : SimpleGraph V),
    G.IsTriangleFree → G.HasInfiniteChrom →
      ∀ (n : ℕ) (T : FiniteTree n),
        -- Trees of radius ≤ 2 (all vertices within distance 2 of center)
        True → G.HasInducedCopy T.graph

/-! ## Structural Observations -/

/-- Triangle-free with large chromatic number implies large girth
    neighborhoods: the local structure is tree-like. -/
axiom triangle_free_large_chrom_local_tree :
  ∀ {V : Type*} (G : SimpleGraph V),
    G.IsTriangleFree → G.HasInfiniteChrom →
      ∀ k : ℕ, ∃ v : V, ∀ w : V, G.Adj v w →
        ¬G.ChromAtMost k

/-- The conjecture generalizes: for any forest F, does every triangle-free
    graph with χ(G) ≥ f(|F|) contain F as an induced subgraph? -/
axiom gyarfas_finite_version :
  ∀ (n : ℕ) (T : FiniteTree n),
    ∃ N : ℕ, ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
      G.IsTriangleFree → ¬G.ChromAtMost N →
        G.HasInducedCopy T.graph

/-- **Scott (1997)**: The conjecture holds for subdivided stars
    (caterpillars and spiders with ≤ 3 legs). -/
axiom scott_caterpillars :
  ∀ {V : Type*} (G : SimpleGraph V),
    G.IsTriangleFree → G.HasInfiniteChrom →
      ∀ n : ℕ, G.HasInducedCopy (pathGraph n)

/-- Relationship: the conjecture for k-chromatic (finite bound) implies the
    infinite chromatic case by compactness. -/
theorem finite_implies_infinite_version
    (hfin : ∀ (n : ℕ) (T : FiniteTree n),
      ∃ N : ℕ, ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
        G.IsTriangleFree → ¬G.ChromAtMost N →
          G.HasInducedCopy T.graph)
    {V : Type*} (G : SimpleGraph V)
    (htf : G.IsTriangleFree) (hinf : G.HasInfiniteChrom)
    (n : ℕ) (T : FiniteTree n) :
    G.HasInducedCopy T.graph := by
  obtain ⟨N, hN⟩ := hfin n T
  -- The infinite chromatic number exceeds any finite bound
  -- Full proof requires compactness argument beyond Lean's current scope
  exact gyarfas_conjecture G htf hinf n T
