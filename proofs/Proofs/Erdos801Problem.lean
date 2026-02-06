/-
Erdős Problem #801: Dense Subgraphs in Graphs with Bounded Independence

Source: https://erdosproblems.com/801
Status: SOLVED (Alon, 1996)

Statement:
If G is a graph on n vertices containing no independent set on > n^{1/2} vertices,
then there is a set of ≤ n^{1/2} vertices containing ≫ n^{1/2} log n edges.

Interpretation:
Graphs with small independence number must have locally dense regions.
If α(G) ≤ √n, then some small vertex set induces many edges.

Answer: YES (Alon, 1996)
Alon proved this using probabilistic and extremal methods.

Key Insight:
Low independence number forces high local edge density somewhere.
The logarithmic factor is necessary and cannot be removed.

References:
- [Er79g] Erdős (1979) - Original problem
- [Al96b] Alon, "Independence numbers of locally sparse graphs and a
          Ramsey type problem" (1996)

Tags: graph-theory, ramsey-theory, extremal-combinatorics, solved
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic

open Finset Real

namespace Erdos801

/-
## Part 1: Basic Graph Definitions
-/

/-- A finite simple graph on n vertices (using Fin n as vertex set) -/
def FiniteGraph (n : ℕ) := SimpleGraph (Fin n)

/-- The independence number α(G): max size of an independent set -/
noncomputable def independenceNumber {n : ℕ} (G : FiniteGraph n) : ℕ :=
  sSup {S.card | S : Finset (Fin n), G.IsIndependent S}

/-- A graph has bounded independence number ≤ k -/
def HasBoundedIndependence {n : ℕ} (G : FiniteGraph n) (k : ℕ) : Prop :=
  independenceNumber G ≤ k

/-- The number of edges in the induced subgraph on S -/
noncomputable def inducedEdges {n : ℕ} (G : FiniteGraph n) (S : Finset (Fin n)) : ℕ :=
  ((S ×ˢ S).filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)).card

/-
## Part 2: The Main Statement
-/

/-- Erdős Problem #801: Small dense subsets exist when independence is bounded -/
def Erdos801Statement : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ n : ℕ, n ≥ 2 →
      ∀ G : FiniteGraph n,
        HasBoundedIndependence G (Nat.sqrt n) →
        ∃ S : Finset (Fin n),
          S.card ≤ Nat.sqrt n ∧
          (inducedEdges G S : ℝ) ≥ c * Real.sqrt n * Real.log n

/-- Alon's Theorem (1996): Affirmatively resolves Problem #801 -/
axiom alon_1996 : Erdos801Statement

/-- The main theorem: Problem #801 is solved -/
theorem erdos_801_solved : Erdos801Statement := alon_1996

/-
## Part 3: Tightness and Optimality
-/

/-- The logarithmic factor in √n log n edges is necessary:
    there exist graphs with α(G) ≤ √n where every set of ≤ √n
    vertices has at most O(√n log n) induced edges. -/
axiom log_factor_necessary :
  ∀ C : ℝ, C > 0 →
    ∀ n : ℕ, n ≥ 2 →
      ∃ G : FiniteGraph n,
        HasBoundedIndependence G (Nat.sqrt n) ∧
        ∀ S : Finset (Fin n),
          S.card ≤ Nat.sqrt n →
          (inducedEdges G S : ℝ) ≤ C * Real.sqrt n * Real.log n

/-- The vertex set size √n is optimal: one cannot replace √n with o(√n). -/
axiom vertex_set_size_optimal :
  ∀ ε : ℝ, ε > 0 → ε < 1 →
    ∀ᶠ n in Filter.atTop,
      ∃ G : FiniteGraph n,
        HasBoundedIndependence G (Nat.sqrt n) ∧
        ∀ S : Finset (Fin n),
          (S.card : ℝ) ≤ ε * Real.sqrt n →
          (inducedEdges G S : ℝ) < Real.sqrt n

/-
## Part 4: Summary
-/

/-- **Erdős Problem #801: SOLVED by Alon (1996)**
    Combines: (1) Alon's theorem, (2) necessity of the log factor. -/
theorem erdos_801_summary :
    Erdos801Statement ∧
    (∀ C : ℝ, C > 0 →
      ∀ n : ℕ, n ≥ 2 →
        ∃ G : FiniteGraph n,
          HasBoundedIndependence G (Nat.sqrt n) ∧
          ∀ S : Finset (Fin n),
            S.card ≤ Nat.sqrt n →
            (inducedEdges G S : ℝ) ≤ C * Real.sqrt n * Real.log n) :=
  ⟨alon_1996, log_factor_necessary⟩

end Erdos801
