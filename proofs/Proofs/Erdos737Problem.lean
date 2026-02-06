/-
Erdős Problem #737: Edge in All Large Cycles

Source: https://erdosproblems.com/737
Status: SOLVED (Thomassen 1983)

Statement:
Let G be a graph with chromatic number ℵ₁.
Must there exist an edge e such that, for all large n,
G contains a cycle of length n containing e?

Background:
- Erdős, Hajnal, and Shelah (1974) posed this problem
- They proved G must contain all sufficiently large cycles
- Thomassen (1983) proved YES: such an edge exists

Key Insight:
Uncountable chromatic number forces rich cycle structure.
Not only do all large cycles exist, but they can be "routed"
through a single edge.

References:
- [EHS74] Erdős, Hajnal, Shelah, "On some general properties of chromatic numbers"
          Topics in Topology (1974), pp. 243-255
- [Th83] Thomassen, "Cycles in graphs of uncountable chromatic number"
         Combinatorica (1983), pp. 133-134
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Nat.Basic

open SimpleGraph Cardinal

namespace Erdos737

/-
## Part I: Graph Concepts

Basic definitions for graphs, chromatic number, and cycles.
We axiomatize chromatic number and cycle predicates since full
formalization of these for infinite graphs is beyond Mathlib.
-/

variable {V : Type*} (G : SimpleGraph V)

/-- The chromatic number of a graph G, axiomatized.
    For infinite graphs this requires careful set-theoretic treatment. -/
axiom chromaticNumber (G : SimpleGraph V) : Cardinal

/-- G has chromatic number exactly ℵ₁. -/
def hasChromaticNumberAleph1 : Prop :=
  chromaticNumber G = Cardinal.aleph 1

/-
## Part II: Cycles and Edges

Cycle predicates axiomatized. A full formalization of cycles
in infinite graphs requires walk theory beyond current Mathlib.
-/

/-- G contains a cycle of length n (axiomatized). -/
axiom hasCycleOfLength (G : SimpleGraph V) (n : ℕ) : Prop

/-- An edge (u, v) is contained in a cycle of length n (axiomatized). -/
axiom edgeInCycleOfLength (G : SimpleGraph V) (u v : V) (h : G.Adj u v) (n : ℕ) : Prop

/-- An edge (u, v) is in cycles of all lengths ≥ N. -/
def edgeInAllLargeCycles (u v : V) (h : G.Adj u v) (N : ℕ) : Prop :=
  ∀ n ≥ N, edgeInCycleOfLength G u v h n

/-- There exists an edge that is in all sufficiently large cycles. -/
def existsEdgeInAllLargeCycles : Prop :=
  ∃ u v : V, ∃ h : G.Adj u v, ∃ N : ℕ, edgeInAllLargeCycles G u v h N

/-
## Part III: The Erdős-Hajnal-Shelah Result (1974)

If G has chromatic number ℵ₁, then G contains all sufficiently large cycles.
-/

/-- Erdős-Hajnal-Shelah (1974): graphs with χ = ℵ₁ contain all large cycles. -/
axiom erdos_hajnal_shelah_1974 (G : SimpleGraph V)
    (hχ : hasChromaticNumberAleph1 G) :
    ∃ N : ℕ, ∀ n ≥ N, hasCycleOfLength G n

/-
## Part IV: Thomassen's Theorem (1983) — Main Result

Thomassen strengthened EHS: not only do all large cycles exist,
but they can all be routed through a single edge.
-/

/-- Thomassen's Theorem (1983): If χ(G) = ℵ₁, there exists an edge e
    such that G contains a cycle of length n through e for all large n. -/
axiom thomassen_1983 (G : SimpleGraph V)
    (hχ : hasChromaticNumberAleph1 G) :
    existsEdgeInAllLargeCycles G

/-- Thomassen's theorem resolves Erdős Problem #737 affirmatively. -/
theorem erdos_737_resolved (G : SimpleGraph V)
    (hχ : hasChromaticNumberAleph1 G) :
    existsEdgeInAllLargeCycles G :=
  thomassen_1983 G hχ

/-
## Part V: Structural Properties

Graphs with χ = ℵ₁ are "eventually pancyclic" and have the
"routing through one edge" property.
-/

/-- Graphs with χ(G) = ℵ₁ are "eventually pancyclic":
    they contain cycles of all sufficiently large lengths. -/
theorem eventually_pancyclic (G : SimpleGraph V)
    (hχ : hasChromaticNumberAleph1 G) :
    ∃ N : ℕ, ∀ n ≥ N, hasCycleOfLength G n :=
  erdos_hajnal_shelah_1974 G hχ

/-- An edge is a "universal cycle edge" if it lies in all large cycles. -/
def isUniversalCycleEdge (u v : V) (h : G.Adj u v) : Prop :=
  ∃ N : ℕ, edgeInAllLargeCycles G u v h N

/-- In graphs with χ = ℵ₁, universal cycle edges exist (Thomassen). -/
theorem universal_edges_exist (G : SimpleGraph V)
    (hχ : hasChromaticNumberAleph1 G) :
    ∃ u v : V, ∃ h : G.Adj u v, isUniversalCycleEdge G u v h := by
  obtain ⟨u, v, h, N, hN⟩ := thomassen_1983 G hχ
  exact ⟨u, v, h, N, hN⟩

/-
## Part VI: Summary

**Erdős Problem #737 — SOLVED (Thomassen 1983)**

**Problem (Erdős-Hajnal-Shelah):**
Let G have chromatic number ℵ₁.
Must there exist an edge e in cycles of all large lengths?

**Answer:** YES (Thomassen 1983).

**Key Points:**
1. EHS (1974) proved G contains all large cycles
2. Thomassen strengthened this: cycles can be routed through one edge
3. ℵ₁ is the critical threshold — finite or countable χ doesn't suffice
4. This connects chromatic structure to cycle structure deeply
-/

theorem erdos_737_summary (G : SimpleGraph V)
    (hχ : hasChromaticNumberAleph1 G) :
    existsEdgeInAllLargeCycles G :=
  thomassen_1983 G hχ

end Erdos737
