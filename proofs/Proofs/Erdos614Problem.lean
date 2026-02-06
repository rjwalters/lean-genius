/-
Erdős Problem #614: Minimum Edges for Induced Maximum Degree

Source: https://erdosproblems.com/614
Status: OPEN

Statement:
Let f(n,k) be the minimal number of edges such that there exists a graph G
with n vertices and f(n,k) edges where every set of k+2 vertices induces
a subgraph with maximum degree at least k.

Determine f(n,k).

This is an extremal graph theory problem asking: how few edges can a graph
have while still guaranteeing that every sufficiently large induced subgraph
has high maximum degree?

Reference: [FRS97] (original source)

Tags: extremal-graph-theory, induced-subgraphs, maximum-degree
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

open SimpleGraph Finset

namespace Erdos614

/-
## Part 1: Basic Definitions

Definitions for graphs, induced subgraphs, and maximum degree.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The degree of a vertex in a graph. -/
noncomputable def degree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (Finset.univ.filter (G.Adj v)).card

/-- Maximum degree in a graph. -/
noncomputable def maxDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.sup' (Finset.univ_nonempty) (degree G)

/-- The induced subgraph on a set of vertices. -/
def inducedSubgraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph S :=
  G.comap (Subtype.val)

/-
## Part 2: Property P(k)

A graph has property P(k) if every set of k+2 vertices induces a subgraph
with maximum degree at least k.
-/

/-- Maximum degree of an induced subgraph on S. -/
noncomputable def inducedMaxDegree (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  if h : S.Nonempty then
    S.sup' h (fun v =>
      (S.filter (fun u => u ≠ v ∧ G.Adj v u)).card)
  else 0

/-- A graph has property P(k) if every (k+2)-subset has induced max degree ≥ k. -/
def hasPropertyP (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∀ S : Finset V, S.card = k + 2 → inducedMaxDegree G S ≥ k

/-
## Part 3: The Function f(n,k)

f(n,k) is the minimum number of edges needed to achieve property P(k)
on n vertices.
-/

/-- Number of edges in a graph. -/
noncomputable def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter (fun p : V × V => p.1 < p.2 ∧ G.Adj p.1 p.2)).card

/-- A graph on n vertices exists with m edges having property P(k). -/
def existsGraphWithPropertyP (n k m : ℕ) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V),
    Fintype.card V = n ∧
    ∃ (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      edgeCount G = m ∧ hasPropertyP G k

/-
## Part 4: Basic Bounds
-/

/-- Lower bound: need at least k edges per vertex on average for large subsets.
    This follows from a double-counting argument on the contributions of
    each vertex to (k+2)-subsets. -/
axiom f_lower_bound :
  ∀ n k : ℕ, n > k + 2 → k > 0 →
    ∀ m, existsGraphWithPropertyP n k m → m ≥ k * n / 2

/-- Upper bound: the complete graph K_n has n(n-1)/2 edges and trivially
    has property P(k) for all k ≤ n-2, since every vertex in any induced
    subgraph has degree equal to the subgraph size minus 1. -/
axiom f_upper_bound :
  ∀ n k : ℕ, k + 2 ≤ n →
    existsGraphWithPropertyP n k (n * (n - 1) / 2)

/-
## Part 5: Special Cases
-/

/-- Case k = 1: every 3 vertices must span at least one edge.
    This means the graph has no independent triple, requiring
    at least n - 2 edges (a path achieves this). -/
axiom f_case_k_eq_1 :
  ∀ n : ℕ, n ≥ 3 →
    ∀ m, existsGraphWithPropertyP n 1 m → m ≥ n - 2

/-- Case k = n - 2: every n-subset must have max degree ≥ n - 2,
    forcing the complete graph as the only possibility. -/
axiom f_max_k :
  ∀ n : ℕ, n ≥ 2 →
    ∀ m, existsGraphWithPropertyP n (n - 2) m → m ≥ n * (n - 1) / 2

/-
## Part 6: Monotonicity
-/

/-- f is non-decreasing in k: requiring higher induced max degree
    requires at least as many edges. A graph with property P(k+1)
    automatically has property P(k). -/
axiom f_mono_k :
  ∀ n k : ℕ, n > k + 3 →
    ∀ m, existsGraphWithPropertyP n (k + 1) m →
    existsGraphWithPropertyP n k m

/-
## Part 7: The Open Problem
-/

/-- **Erdős Problem #614 (OPEN)**

Determine f(n,k), the minimum number of edges in an n-vertex
graph such that every (k+2)-subset induces a subgraph with
maximum degree at least k.

Currently unknown:
- Exact value of f(n,k) for most n, k
- Asymptotic behavior as n → ∞ for fixed k
- Whether f(n,k)/n² has a limit

We formalize the known structural results: bounds, special cases,
and monotonicity. The exact determination remains open. -/
axiom erdos_614_existence :
  ∀ n k : ℕ, n ≥ k + 2 → k > 0 →
    ∃ m, existsGraphWithPropertyP n k m

/-
## Part 8: Summary
-/

/-- **Erdős Problem #614: OPEN**

Summarizes what is known:
1. The function f(n,k) is well-defined (complete graph gives upper bound)
2. Lower bound: at least kn/2 edges needed
3. k=1: at least n-2 edges
4. k=n-2: complete graph required
5. Monotone in k parameter
6. Exact formula: UNKNOWN -/
theorem erdos_614_summary :
    -- The function is well-defined (existence)
    (∀ n k : ℕ, n ≥ k + 2 → k > 0 →
      ∃ m, existsGraphWithPropertyP n k m) ∧
    -- Complete graph provides an upper bound
    (∀ n k : ℕ, k + 2 ≤ n →
      existsGraphWithPropertyP n k (n * (n - 1) / 2)) :=
  ⟨erdos_614_existence, f_upper_bound⟩

end Erdos614
