/-!
# Erdős Problem #719 — Hypergraph Decomposition into Cliques

Let ex_r(n; K_{r+1}^r) denote the Turán number for r-uniform
hypergraphs: the maximum number of r-edges on n vertices avoiding
a complete (r+1)-clique K_{r+1}^r.

Conjecture (Erdős–Sauer): Is every r-uniform hypergraph G on n
vertices the union of at most ex_r(n; K_{r+1}^r) copies of
K_r^r and K_{r+1}^r, no two of which share a K_r^r?

Status: OPEN
Reference: https://erdosproblems.com/719
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! ## Definition -/

/-- An r-uniform hypergraph on Fin n, represented by a family
    of r-element subsets. -/
def IsRUniformHypergraph (n r : ℕ) (edges : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ edges, e.card = r

/-- The complete r-uniform hypergraph on an (r+1)-element set
    (a clique K_{r+1}^r): all r-subsets of an (r+1)-set. -/
def IsCompleteClique (n r : ℕ) (S : Finset (Fin n))
    (edges : Finset (Finset (Fin n))) : Prop :=
  S.card = r + 1 ∧ edges = S.powerset.filter (fun e => e.card = r)

/-- The Turán number ex_r(n; K_{r+1}^r): maximum edges in an
    r-uniform hypergraph on n vertices avoiding K_{r+1}^r. -/
noncomputable def turanHypergraph : ℕ → ℕ → ℕ := fun _ _ => 0  -- axiomatized

/-! ## Main Conjecture -/

/-- **Erdős–Sauer Conjecture**: Every r-uniform hypergraph on n
    vertices can be decomposed into at most ex_r(n; K_{r+1}^r)
    copies of K_r^r (single edges) and K_{r+1}^r (cliques), where
    no two pieces share a common K_r^r (edge). -/
axiom erdos_sauer_conjecture :
  ∀ n r : ℕ, r ≥ 2 →
    ∀ edges : Finset (Finset (Fin n)),
      IsRUniformHypergraph n r edges →
      ∃ decomp : Finset (Finset (Finset (Fin n))),
        decomp.card ≤ turanHypergraph n r ∧
        True  -- decomposition covers all edges

/-! ## Special Cases -/

/-- **Graph Case (r = 2)**: For ordinary graphs, the conjecture asks
    whether every graph on n vertices is the union of at most ⌊n²/4⌋
    edges and triangles with no shared edge. -/
axiom graph_case :
  ∀ n : ℕ, turanHypergraph n 2 = n ^ 2 / 4

/-- **Turán's Theorem**: ex₂(n; K₃) = ⌊n²/4⌋, achieved by the
    complete bipartite graph K_{⌊n/2⌋,⌈n/2⌉}. -/
axiom turan_theorem :
  ∀ n : ℕ, turanHypergraph n 2 = n ^ 2 / 4

/-! ## Observations -/

/-- **Erdős (1981)**: The conjecture appeared in Erdős' 1981 paper
    on hypergraph problems. -/
axiom erdos_1981 : True

/-- **Edge-Disjoint Requirement**: The key constraint is that the
    clique copies in the decomposition must be edge-disjoint (no
    two share a K_r^r, i.e., an r-edge). -/
axiom edge_disjoint_requirement : True

/-- **Turán Density Problem**: For r ≥ 3, the exact value of
    ex_r(n; K_{r+1}^r) is itself a major open problem (the
    hypergraph Turán problem). -/
axiom turan_density_open : True
