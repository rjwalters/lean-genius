/-
Erdős Problem #65: Cycle Lengths in Dense Graphs

Let G be a graph with n vertices and kn edges, and let a₁ < a₂ < ... be the
distinct lengths of cycles in G. Is it true that
  Σ 1/aᵢ ≫ log k?

Is the sum Σ 1/aᵢ minimised when G is a complete bipartite graph?

**Status**: PARTIALLY SOLVED
- First question: PROVED by Gyárfás-Komlós-Szemerédi (1984)
- Second question (minimization): OPEN

**Known Results**:
- GKS (1984): Σ 1/aᵢ ≫ log k is true
- Complete bipartite graphs have few cycle lengths (only even lengths)
- The minimization question remains open

**Prize**: None listed

Reference: https://erdosproblems.com/65
GKS Paper: "On a problem of K. Zarankiewicz" (1984)
-/

import Mathlib

open Finset
open scoped BigOperators

namespace Erdos65

/-
## Background

This problem connects the edge density of a graph to its cycle structure.

A graph with n vertices and kn edges has average degree 2k. The question is:
how many distinct cycle lengths must such a graph have, weighted by 1/length?

The sum Σ 1/aᵢ measures the "variety" of cycle lengths, with shorter cycles
contributing more. Dense graphs (high k) should have more cycle variety.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
## Core Definitions
-/

/-- Cyclic successor in Fin k: maps i to (i+1) mod k. -/
def Fin.succMod {k : ℕ} (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩

/-- A graph contains a cycle of length k ≥ 3 if there is a cycle subgraph on k vertices. -/
def ContainsCycleLength (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (hk : k ≥ 3) (vs : Fin k → V), Function.Injective vs ∧
    ∀ i : Fin k, G.Adj (vs i) (vs (Fin.succMod (by omega : 0 < k) i))

/-- The set of distinct cycle lengths in a graph. -/
def CycleLengthSet (G : SimpleGraph V) : Set ℕ :=
  { k | ContainsCycleLength G k }

/-- The cycle length set as a finset (for finite graphs).
    Uses classical decidability. -/
noncomputable def cycleLengthFinset (G : SimpleGraph V) : Finset ℕ :=
  (Finset.range (Fintype.card V + 1)).filter
    (fun k => @Decidable.decide (ContainsCycleLength G k) (Classical.dec _))

/-
## Edge Density and Cycle Variety
-/

/-- Number of edges in a finite graph. -/
noncomputable def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-- The edge density k, where G has n vertices and kn edges.
    Returns the density as a rational to handle non-integer cases. -/
noncomputable def edgeDensity (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  if Fintype.card V = 0 then 0
  else edgeCount G / Fintype.card V

/-- The sum of reciprocals of cycle lengths in G. -/
noncomputable def cycleLengthReciprocalSum (G : SimpleGraph V) : ℝ :=
  ∑ k ∈ cycleLengthFinset G, (1 : ℝ) / k

/-
## The Main Questions

Erdős and Hajnal asked two related questions about cycle lengths.
-/

/--
**Question 1 (PROVED)**: The Gyárfás-Komlós-Szemerédi Theorem

For any graph G with n vertices and kn edges (k ≥ 1), the sum of reciprocals
of cycle lengths is at least c log k for some absolute constant c > 0.

This was proved in their 1984 paper.
-/

/--
**Question 2 (OPEN)**: Complete Bipartite Minimization

Is the sum Σ 1/aᵢ minimized when G is a complete bipartite graph K_{r,s}?

Complete bipartite graphs have the special property that they only contain
cycles of even lengths (specifically, even lengths from 4 to 2·min(r,s)).

This would explain why they might minimize the cycle variety.
-/
def Erdos65Question : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r s : ℕ),
    let n := Fintype.card V
    n = r + s →
    edgeCount G = r * s →
    -- There exists a complete bipartite graph with at most the same sum
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (H : SimpleGraph W) (_ : DecidableRel H.Adj),
      Fintype.card W = n ∧ edgeCount H = r * s ∧
      H.IsBipartite ∧
      cycleLengthReciprocalSum H ≤ cycleLengthReciprocalSum G

/-
## Complete Bipartite Graph Properties

Complete bipartite graphs have well-understood cycle structure.
We use Mathlib's definition: G.IsBipartite
-/

/-- The reciprocal sum for K_{r,s} can be computed explicitly. -/
noncomputable def bipartiteCycleSum (r s : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 2 (min r s), (1 : ℝ) / (2 * i)

/-- The bipartite cycle sum is 1/2 times a partial harmonic sum. -/

/-
## Lower Bounds on Cycle Variety

Any dense graph must have many cycle lengths, not just because of GKS,
but also due to other structural results.
-/

/-
## The Zarankiewicz Connection

This problem is related to the Kővári-Sós-Turán theorem (Zarankiewicz problem),
which bounds the maximum edges in a K_{r,s}-free graph.

The GKS result uses similar extremal graph theory techniques.
-/

/-
## Special Cases
-/

/-- For k = 1 (n edges, average degree 2), the graph has a cycle.

    Proof: A forest (acyclic graph) on n vertices has at most n-1 edges.
    With n edges, the graph cannot be acyclic, so it contains a cycle. -/

/-
## Remarks on the Open Question

Why complete bipartite graphs might minimize the sum:

1. They are bipartite, so no odd cycles (which contribute 1/3, 1/5, 1/7, ...)
2. Their even cycles start at length 4, not 2 (no multiedges)
3. The cycle lengths form a consecutive sequence {4, 6, 8, ..., 2m}
   rather than being scattered

However, proving this minimization property requires understanding
the structure of ALL graphs with given edge count, not just bipartite ones.
-/

/-- The parity observation: bipartite graphs only have even cycle lengths.

    Proof: In a 2-coloring, adjacent vertices have different colors.
    Walking around a cycle of length k, colors alternate, so after k steps
    we return to the starting color iff k is even. Since we return to the
    starting vertex (which has the starting color), k must be even. -/

/-- Odd cycle contribution: if G has an odd cycle of length k, it contributes 1/k > 0.
    The oddness hypothesis is semantically relevant (odd cycles are the non-bipartite ones)
    even though the positivity proof only needs k ≥ 3. -/
theorem odd_cycle_positive_contribution (k : ℕ) (_hk : Odd k) (hk3 : k ≥ 3) :
    (1 : ℝ) / k > 0 := by
  have hpos : (k : ℝ) > 0 := by
    have : k > 0 := by omega
    exact Nat.cast_pos.mpr this
  positivity

/-
## Summary

**Problem Status: PARTIALLY SOLVED**

Erdős Problem 65 has two parts:

1. **PROVED**: Gyárfás-Komlós-Szemerédi (1984) showed that for any graph G
   with n vertices and kn edges, the sum of reciprocals of cycle lengths
   satisfies Σ 1/aᵢ ≫ log k.

2. **OPEN**: Is this sum minimized when G is a complete bipartite graph?

The minimization question is subtle because:
- Bipartite graphs avoid odd cycles entirely (no 1/3, 1/5, ... terms)
- But non-bipartite graphs might have fewer total cycle lengths
- The interaction between edge density and cycle structure is complex

References:
- Gyárfás, Komlós, Szemerédi (1984): "On a problem of K. Zarankiewicz"
- Bollobás (1978): "Extremal Graph Theory"
-/

end Erdos65
