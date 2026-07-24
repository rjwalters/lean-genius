/-
# Erdős Problem #566 — Ramsey Size Linearity for Sparse Graphs

Let G be a graph such that every subgraph on k vertices has at most
2k − 3 edges. Is G Ramsey size linear? That is, for every graph H
with m edges and no isolated vertices, is r̂(G,H) ≤ c·m for some
constant c depending only on G?

Known:
- True for graphs with n vertices and ≤ n+1 edges (EFRS 1993)
- False for graphs with 2n−2 edges (e.g., H = Kₙ)
- Implies Problem #567

Status: OPEN
Reference: https://erdosproblems.com/566
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped Classical

/- ## Definitions -/

/-- A graph on n vertices represented by its adjacency predicate. -/
structure Graph (n : ℕ) where
  adj : Fin n → Fin n → Prop
  symm : ∀ u v, adj u v → adj v u
  irrefl : ∀ v, ¬adj v v

/-- The number of edges in a graph. -/
noncomputable def edgeCount {n : ℕ} (G : Graph n) : ℕ :=
  Finset.card (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ G.adj p.1 p.2) Finset.univ)

/-- A graph is (2k−3)-sparse: every subgraph on k ≥ 2 vertices
    has at most 2k − 3 edges. -/
def IsSparse {n : ℕ} (G : Graph n) : Prop :=
  ∀ S : Finset (Fin n), S.card ≥ 2 →
    Finset.card (Finset.filter
      (fun p : Fin n × Fin n => p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2 ∧ G.adj p.1 p.2)
      Finset.univ) ≤ 2 * S.card - 3

/-- A graph has no isolated vertices. -/
def NoIsolated {n : ℕ} (H : Graph n) : Prop :=
  ∀ v : Fin n, ∃ u : Fin n, H.adj v u

/-- Placeholder for the size Ramsey number r̂(G, H) — the minimum
    number of edges in a graph F such that every 2-coloring of E(F)
    contains a monochromatic copy of G in color 1 or H in color 2.

    This is **not implemented**: the 2-coloring construction is not
    formalized. The body is a constant stub returning `1`, independent
    of `G`, `H`, `p`, and `q`. It exists only so the definitions
    section type-checks; no result in this file depends on its value.
    See the module docstring and the gallery entry, which record that
    Problem #566 is OPEN and only the surrounding definitions are
    formalized. -/
noncomputable def sizeRamsey {p q : ℕ} (_G : Graph p) (_H : Graph q) : ℕ :=
  1

/- ## Main Question -/

/-  **Erdős Problem #566**: If G is (2k−3)-sparse, is G Ramsey
    size linear? That is, ∃ c > 0 such that r̂(G, H) ≤ c · |E(H)|
    for every H with no isolated vertices. -/
/- ## Known Results -/

/-  **EFRS (1993)**: Any graph G with n vertices and at most n+1
    edges is Ramsey size linear. -/
/-  **Counterexample at 2n−2**: The sparsity condition 2k−3 is
    tight — there exist graphs with 2n−2 edges that are NOT
    Ramsey size linear. -/
/- ## Related Results -/

/- **Sparsity threshold**: The (2k−3) bound is the boundary
    between graphs that might be Ramsey size linear and those
    that provably are not. Trees (n−1 edges) are known to be
    Ramsey size linear. -/
/- **Implies Problem #567**: A positive answer to #566 would
    resolve #567 as well. -/
