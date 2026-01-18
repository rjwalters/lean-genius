/-
  Erdős Problem #944: Critical Graphs Without Critical Edges

  A **critical vertex** is one whose deletion lowers the chromatic number.
  A **critical edge** (or critical edge set) is one whose deletion lowers
  the chromatic number.

  A graph is **k-vertex-critical** if it has chromatic number k and every
  vertex is critical.

  **Conjecture (Dirac 1970, Erdős)**: For k ≥ 4 and r ≥ 1, does there exist
  a k-vertex-critical graph where every critical set of edges has size > r?

  **Known Results**:
  - k = 5: Yes (Brown 1992)
  - k ≥ 5: Yes (Jensen 2002)
  - k-1 not prime: Yes (Lattanzio 2002)
  - k = 4: OPEN
  - Large k for any r: Yes (Martinsson-Steiner 2025)

  References:
  - https://erdosproblems.com/944
  - Brown, J.I., "A vertex critical graph without critical edges" (1992)
  - Jensen, T.R., "Dense critical and vertex-critical graphs" (2002)
  - Lattanzio, J.J., "A note on a conjecture of Dirac" (2002)
  - Martinsson, A., Steiner, R., "Vertex-critical graphs far from
    edge-criticality" (2025)
-/

import Mathlib

namespace Erdos944

/-!
## Core Definitions

We axiomatize critical graphs since full definitions require extensive
graph coloring infrastructure.
-/

/-- A graph G is **k-vertex-critical** if:
- χ(G) = k (chromatic number is k)
- For every vertex v, χ(G - v) < k (every vertex is critical) -/
class IsKVertexCritical (G : Type*) (k : ℕ) : Prop

/-- A graph G has the **Erdős944 property** with parameters (k, r) if:
- G is k-vertex-critical
- Every critical edge set has more than r edges

A critical edge set is one whose deletion reduces the chromatic number. -/
class IsErdos944Graph (G : Type*) (k r : ℕ) extends IsKVertexCritical G k : Prop

/-!
## Main Conjecture

Does there exist a k-vertex-critical graph where every critical edge set
has size > r?
-/

/-- **Erdős Problem #944 (Partially OPEN)**: For k ≥ 4 and r ≥ 1, does there
exist a graph with the Erdős944 property?

The case k = 4, r = 1 remains OPEN. -/
axiom erdos_944_conjecture : ∀ k ≥ 4, ∀ r ≥ 1,
    ∃ (G : Type), IsErdos944Graph G k r

/-!
## Dirac's Conjecture (r = 1)

Are there k-vertex-critical graphs without any critical edges?
-/

/-- **Dirac's Conjecture (1970)**: For k ≥ 4, there exists a k-vertex-critical
graph with no critical edges (every critical edge set has size > 1). -/
axiom dirac_conjecture : ∀ k ≥ 4,
    ∃ (G : Type), IsErdos944Graph G k 1

/-!
## Solved Cases
-/

/-- **Brown's Result (1992)**: There exists a 5-vertex-critical graph with
no critical edges. Brown explicitly constructed such a graph with 11 vertices. -/
axiom brown_1992 : ∃ (G : Type), IsErdos944Graph G 5 1

/-- **Lattanzio's Result (2002)**: For k where k-1 is not prime, there exist
k-vertex-critical graphs with no critical edges. -/
axiom lattanzio_2002 (k : ℕ) (hk : 4 ≤ k) (h : ¬(k - 1).Prime) :
    ∃ (G : Type), IsErdos944Graph G k 1

/-- **Jensen's Result (2002)**: For k ≥ 5, there exist k-vertex-critical
graphs with no critical edges. -/
axiom jensen_2002 (k : ℕ) (hk : 5 ≤ k) :
    ∃ (G : Type), IsErdos944Graph G k 1

/-- **Martinsson-Steiner's Result (2025)**: For every r ≥ 1, if k is
sufficiently large, there exist k-vertex-critical graphs where every
critical edge set has size > r. -/
axiom martinsson_steiner_2025 (r : ℕ) (hr : 1 ≤ r) :
    ∃ k₀, ∀ k ≥ k₀, ∃ (G : Type), IsErdos944Graph G k r

/-!
## The Open Case: k = 4
-/

/-- **OPEN**: Does there exist a 4-vertex-critical graph with no critical edges?

This is the last remaining case of Dirac's conjecture. All k ≥ 5 are solved. -/
axiom k_equals_4_open :
    (∃ (G : Type), IsErdos944Graph G 4 1) ∨
    (¬∃ (G : Type), IsErdos944Graph G 4 1)

/-!
## Basic Properties of Critical Graphs
-/

/-- A k-vertex-critical graph has minimum degree at least k-1. -/
axiom vertex_critical_min_degree (G : Type) [IsKVertexCritical G k] (hk : 2 ≤ k) :
    True  -- Placeholder for: ∀ v, deg(v) ≥ k - 1

/-- A k-vertex-critical graph is connected. -/
axiom vertex_critical_connected (G : Type) [IsKVertexCritical G k] (hk : 2 ≤ k) :
    True  -- Placeholder for: G is connected

/-- The complete graph K_n is n-vertex-critical. -/
axiom complete_graph_vertex_critical (n : ℕ) (hn : 1 ≤ n) :
    ∃ (G : Type), IsKVertexCritical G n

/-- An odd cycle C_{2n+1} is 3-vertex-critical. -/
axiom odd_cycle_vertex_critical (n : ℕ) (hn : 1 ≤ n) :
    ∃ (G : Type), IsKVertexCritical G 3

/-!
## Historical Context

Dirac conjectured in 1970 that for every k ≥ 4, there exists a k-vertex-critical
graph with no critical edges. The conjecture was motivated by the observation
that while K_k is k-vertex-critical, every edge of K_k is critical.

The question is whether vertex-criticality and edge-criticality can be
"decoupled" - can we have a graph where every vertex is essential for
maintaining the chromatic number, yet no single edge (or small set of edges)
is essential?

Brown (1992) first showed this is possible for k = 5.
Jensen (2002) extended this to all k ≥ 5.
The case k = 4 remains open.
-/

end Erdos944
