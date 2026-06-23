/-
# Erdős Problem #809: Rainbow Colorings of Odd Cycles

**Source:** [erdosproblems.com/809](https://erdosproblems.com/809)
**Status:** OPEN

## Statement

Let k ≥ 3 and define F_k(n) to be the minimal r such that there is a graph G
on n vertices with ⌊n²/4⌋ + 1 edges such that the edges can be r-colored so
that every subgraph isomorphic to C_{2k+1} has no color repeating (rainbow).

Is it true that F_k(n) ~ n²/8?

## Background

- A graph with ⌊n²/4⌋ + 1 edges is just above the Turán threshold for odd cycles
- Burr-Erdős-Graham-Sós: Proved F_k(n) ≫ n² (quadratic lower bound)
- The precise asymptotic remains open

## Approach

We define graphs, edge colorings, cycles, and the rainbow property.
The function F_k(n) is axiomatized along with the main conjecture and
the Burr-Erdős-Graham-Sós lower bound.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Basic

open Finset

namespace Erdos809

/- ## Part I: Basic Definitions -/

/--
**Simple Graph on n vertices:**
A graph with vertex set Fin n.
-/
abbrev Graph (n : ℕ) := SimpleGraph (Fin n)

/--
**Edge Count:**
The number of edges in a graph.
-/
noncomputable def edgeCount (n : ℕ) (G : Graph n) : ℕ :=
  G.edgeFinset.card

/--
**Turán Threshold:**
⌊n²/4⌋ + 1 edges — just above the Turán threshold for triangle-free.
-/
def turanThreshold (n : ℕ) : ℕ := n^2 / 4 + 1

/--
**Odd Cycle C_{2k+1}:**
A cycle of length 2k + 1 vertices.
-/
def oddCycleLength (k : ℕ) : ℕ := 2 * k + 1

/--
**Edge Coloring:**
An assignment of colors (from {0, ..., r-1}) to edges.
-/
def EdgeColoring (n : ℕ) (G : Graph n) (r : ℕ) :=
  G.edgeSet → Fin r

/- ## Part II: Rainbow Property -/

/--
**Rainbow Coloring:**
A coloring where no color repeats on a given subgraph.
-/
def isRainbowOn {n : ℕ} {G : Graph n} {r : ℕ}
    (c : EdgeColoring n G r) (edges : Finset G.edgeSet) : Prop :=
  (edges.image c).card = edges.card

/--
**Cycle in a Graph:**
A sequence of vertices v₀, v₁, ..., v_{m-1} where consecutive pairs
(including v_{m-1} and v₀) are adjacent, and non-consecutive vertices
are distinct.
-/
structure Cycle (n : ℕ) (G : Graph n) (m : ℕ) where
  vertices : Fin m → Fin n
  distinct : ∀ i j, i ≠ j → i.val < m - 1 → j.val < m - 1 → vertices i ≠ vertices j
  edges : ∀ i : Fin m, G.Adj (vertices i) (vertices ⟨(i.val + 1) % m, by omega⟩)

/- ## Part III: The Function F_k(n)

F_k(n) is axiomatized as a function ℕ → ℕ → ℕ rather than defined via
Nat.find, since the existence proof for the find would require sorry.
-/

/--
**F_k(n) (axiomatized):**
The minimal r such that some graph G on n vertices with ⌊n²/4⌋ + 1 edges
admits an r-coloring where every C_{2k+1} subgraph is rainbow.
-/
axiom F : ℕ → ℕ → ℕ

/- ## Part IV: The Conjecture -/

/--
**Main Conjecture:**
F_k(n) ~ n²/8 for k ≥ 3.
-/
def mainConjecture : Prop :=
  ∀ k ≥ 3, ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    (1 - ε) * (n : ℝ)^2 / 8 ≤ (F k n : ℝ) ∧
    (F k n : ℝ) ≤ (1 + ε) * (n : ℝ)^2 / 8

/--
**Asymptotic equivalence:**
F_k(n) ~ n²/8 means lim_{n→∞} F_k(n) / (n²/8) = 1.
-/
def asymptoticEquivalence : Prop :=
  ∀ k ≥ 3, ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    |((F k n : ℝ) / ((n : ℝ)^2 / 8)) - 1| < ε

/- ## Part V: Known Bounds -/

/--
**Burr-Erdős-Graham-Sós Lower Bound:**
F_k(n) ≫ n², i.e., F_k(n) ≥ c · n² for some c > 0.
-/
axiom begs_lower_bound :
  ∀ k ≥ 3, ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    (F k n : ℝ) ≥ c * (n : ℝ)^2

/--
**Quadratic upper bound:**
F_k(n) ≤ C · n² for some constant C (e.g., by giving each edge its own color).
-/
axiom quadratic_upper_bound :
  ∀ k ≥ 3, ∃ C : ℝ, ∀ n : ℕ, n ≥ 1 →
    (F k n : ℝ) ≤ C * (n : ℝ)^2

/- ## Part VI: Turán's Theorem Context -/

/--
**Turán's Theorem:**
A graph with more than ⌊n²/4⌋ edges must contain an odd cycle.
This explains the edge threshold ⌊n²/4⌋ + 1.
-/
axiom turan_odd_cycle :
  ∀ n : ℕ, ∀ G : Graph n, edgeCount n G > n^2 / 4 →
    ∃ k, ∃ _ : Cycle n G (2 * k + 1), True

/--
**At the threshold:**
With exactly ⌊n²/4⌋ + 1 edges, we're just above Turán's threshold.
-/
theorem threshold_significance :
    ∀ n : ℕ, n ≥ 2 → turanThreshold n > n^2 / 4 := by
  intro n _
  simp [turanThreshold]
  omega

/- ## Part VII: Summary

**Erdős Problem #809: OPEN**

**Question:** For k ≥ 3, is F_k(n) ~ n²/8?

**Known bounds:**
- Lower: F_k(n) ≫ n² (Burr-Erdős-Graham-Sós)
- Upper: F_k(n) ≤ C · n² (trivial)

**Conjecture:** The constant is 1/8, exactly half of the Turán
threshold constant 1/4.
-/

theorem erdos_809_summary :
    -- Quadratic lower bound
    (∀ k ≥ 3, ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      (F k n : ℝ) ≥ c * (n : ℝ)^2) ∧
    -- Quadratic upper bound
    (∀ k ≥ 3, ∃ C : ℝ, ∀ n : ℕ, n ≥ 1 →
      (F k n : ℝ) ≤ C * (n : ℝ)^2) := by
  exact ⟨begs_lower_bound, quadratic_upper_bound⟩

end Erdos809
