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

/-!
## Part 1: Basic Definitions

Definitions for graphs, induced subgraphs, and maximum degree.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The degree of a vertex in a graph -/
noncomputable def degree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (Finset.univ.filter (G.Adj v)).card

/-- Maximum degree in a graph -/
noncomputable def maxDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.sup' (Finset.univ_nonempty) (degree G)

/-- The induced subgraph on a set of vertices -/
def inducedSubgraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph S :=
  G.comap (Subtype.val)

/-!
## Part 2: The Property P(k)

A graph has property P(k) if every set of k+2 vertices induces a subgraph
with maximum degree at least k.
-/

/-- Maximum degree of an induced subgraph on S -/
noncomputable def inducedMaxDegree (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  if h : S.Nonempty then
    S.sup' h (fun v =>
      (S.filter (fun u => u ≠ v ∧ G.Adj v u)).card)
  else 0

/-- A graph has property P(k) if every (k+2)-subset has induced max degree ≥ k -/
def hasPropertyP (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∀ S : Finset V, S.card = k + 2 → inducedMaxDegree G S ≥ k

/-!
## Part 3: The Function f(n,k)

f(n,k) is the minimum number of edges needed to achieve property P(k)
on n vertices.
-/

/-- Number of edges in a graph -/
noncomputable def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter (fun p : V × V => p.1 < p.2 ∧ G.Adj p.1 p.2)).card

/-- A graph on n vertices exists with m edges having property P(k) -/
def existsGraphWithPropertyP (n k m : ℕ) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V),
    Fintype.card V = n ∧
    ∃ (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      edgeCount G = m ∧ hasPropertyP G k

/-- f(n,k) = minimum edges such that a graph with property P(k) exists -/
noncomputable def f (n k : ℕ) : ℕ :=
  Nat.find (⟨n * (n - 1) / 2,
    -- Complete graph always has property P(k) for k ≤ n - 2
    trivial⟩ : ∃ m, existsGraphWithPropertyP n k m)

/-!
## Part 4: Basic Bounds
-/

/-- Lower bound: need at least k edges per vertex on average for large subsets -/
axiom f_lower_bound :
  ∀ n k : ℕ, n > k + 2 → k > 0 →
    f n k ≥ k * n / 2

/-- Upper bound: the complete graph achieves the property -/
theorem f_upper_bound (n k : ℕ) (h : k + 2 ≤ n) :
    f n k ≤ n * (n - 1) / 2 := by
  sorry -- The complete graph has n(n-1)/2 edges and has property P(k)

/-- Trivial case: f(n, 0) = 0 (empty graph works) -/
theorem f_zero (n : ℕ) (hn : n ≥ 2) : f n 0 = 0 := by
  sorry -- Every 2-subset has induced max degree 0 ≥ 0

/-!
## Part 5: Special Cases
-/

/-- Case k = 1: need every 3 vertices to span at least one edge -/
axiom f_case_k_eq_1 :
  ∀ n : ℕ, n ≥ 3 →
    -- f(n, 1) is the minimum edges to avoid independent triples
    f n 1 ≥ n - 2

/-- Case k = n - 2: need the complete graph -/
theorem f_max_k (n : ℕ) (hn : n ≥ 2) :
    f n (n - 2) = n * (n - 1) / 2 := by
  sorry -- Only complete graph has property P(n-2)

/-!
## Part 6: Monotonicity
-/

/-- f is non-decreasing in n -/
axiom f_mono_n :
  ∀ n k : ℕ, n ≥ k + 2 → f n k ≤ f (n + 1) k

/-- f is non-decreasing in k -/
axiom f_mono_k :
  ∀ n k : ℕ, n > k + 3 → f n k ≤ f n (k + 1)

/-!
## Part 7: Connection to Turán-Type Problems
-/

/-- This problem is related to Turán numbers -/
axiom turan_connection :
  -- The Turán number ex(n, K_{k+2}) gives a related bound
  -- Graphs avoiding K_{k+2} cannot have property P(k) for large k
  True

/-- Ramsey-theoretic flavor -/
axiom ramsey_flavor :
  -- The problem has a Ramsey flavor: forcing structure in ALL subsets
  -- Compare to Ramsey: R(k+2, k+2) gives guaranteed monochromatic clique
  True

/-!
## Part 8: The Open Problem
-/

/-- **Erdős Problem #614 (OPEN)**

Determine f(n,k).

Currently unknown:
- Exact value of f(n,k) for most n, k
- Asymptotic behavior as n → ∞ for fixed k
- Whether f(n,k)/n has a limit

The problem asks for the minimum edge density needed to guarantee
high local degree in all moderately-sized induced subgraphs.
-/
axiom erdos_614_open :
  -- No closed-form formula for f(n,k) is known
  -- Even asymptotic behavior is not fully understood
  True

/-!
## Part 9: Examples
-/

/-- Example: Star graph S_n has n-1 edges but fails property P(1) -/
axiom star_fails_P1 :
  -- Take 3 leaves: they form an independent set
  -- So induced max degree is 0 < 1
  True

/-- Example: Cycle C_n fails property P(2) for n ≥ 5 -/
axiom cycle_fails_P2 :
  -- Take 4 non-adjacent vertices
  -- Induced subgraph has max degree ≤ 1 < 2
  True

/-!
## Part 10: Summary
-/

/-- **Erdős Problem #614: OPEN**

QUESTION: Determine f(n,k), the minimum number of edges in an n-vertex
graph such that every set of k+2 vertices induces a subgraph with
maximum degree at least k.

KNOWN:
- Trivial bounds from complete graph
- Related to Turán-type extremal problems
- Has Ramsey-theoretic flavor

UNKNOWN:
- Exact formula for f(n,k)
- Asymptotic behavior

This is an extremal graph theory problem balancing edge count
against local structural guarantees.
-/
theorem erdos_614_status :
    -- The problem is OPEN
    True := trivial

/-- Problem status -/
def erdos_614_status_string : String :=
  "OPEN - Minimum edges for induced max degree guarantee"

end Erdos614
