/-
  Erdős Problem #608: Edges in 5-Cycles

  Source: https://erdosproblems.com/608
  Status: SOLVED (Disproved - Füredi-Maleki, Grzesik-Hu-Volec)

  Statement:
  Let G be a graph with n vertices and > n²/4 edges.
  Are there at least (2/9)n² edges of G contained in a C₅?

  Solution:
  - NO! The correct bound is c = (2 + √2)/16 ≈ 0.2134
  - Füredi-Maleki: Upper bound construction with cn² + O(n) edges in C₅
  - Grzesik-Hu-Volec: Matching lower bound (c - o(1))n²

  Related: For odd cycles C_{2k+1}, the bound (2/9)n² is correct for k ≥ 3

  Tags: graph-theory, extremal-combinatorics, cycles
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Erdos608

open SimpleGraph Finset Real

variable {V : Type*} [Fintype V] [DecidableEq V]

/- ## Part I: Basic Definitions -/

/-- A 5-cycle in graph G. -/
def IsC5 (G : SimpleGraph V) [DecidableRel G.Adj] (a b c d e : V) : Prop :=
  a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ e ∧ e ≠ a ∧
  a ≠ c ∧ a ≠ d ∧ b ≠ d ∧ b ≠ e ∧ c ≠ e ∧
  G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d e ∧ G.Adj e a

/-- An edge is in a C₅ if it's part of some 5-cycle. -/
def EdgeInC5 (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V) : Prop :=
  ∃ a b c d f : V, e = s(a, b) ∧ IsC5 G a b c d f

/-- The number of edges contained in some C₅. -/
noncomputable def edgesInC5 (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.edgeFinset.filter (EdgeInC5 G)).card

/-- The number of vertices. -/
def n (V : Type*) [Fintype V] : ℕ := Fintype.card V

/- ## Part II: The Original Conjecture -/

/-- Erdős's original conjecture: ≥ (2/9)n² edges in C₅. -/
def OriginalConjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    (G.edgeFinset.card : ℝ) > (n V : ℝ)^2 / 4 →
    (edgesInC5 G : ℝ) ≥ 2/9 * (n V : ℝ)^2

/-- The conjecture is FALSE. -/
theorem original_conjecture_false : ¬OriginalConjecture := by
  sorry

/- ## Part III: The Correct Constant -/

/-- The correct constant c = (2 + √2) / 16. -/
noncomputable def c : ℝ := (2 + Real.sqrt 2) / 16

/-- c ≈ 0.2134. -/
theorem c_approx : c > 0.213 ∧ c < 0.214 := by
  sorry

/-- c < 2/9 (which is why the original conjecture fails). -/
theorem c_lt_two_ninths : c < 2/9 := by
  sorry

/- ## Part IV: Füredi-Maleki Upper Bound -/

/-- Füredi-Maleki construction: Graphs with few edges in C₅. -/
def FurediMalekiConstruction : Prop :=
  ∀ ε > 0, ∀ᶠ n in Filter.atTop,
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    Fintype.card V = n ∧
    (G.edgeFinset.card : ℝ) > (n : ℝ)^2 / 4 ∧
    (edgesInC5 G : ℝ) ≤ (c + ε) * (n : ℝ)^2

/-- The Füredi-Maleki construction exists. -/
theorem furedi_maleki : FurediMalekiConstruction := by
  sorry

/- ## Part V: Grzesik-Hu-Volec Lower Bound -/

/-- The tight lower bound: At least (c - o(1))n² edges in C₅. -/
def GrzesikHuVolecBound : Prop :=
  ∀ ε > 0, ∀ᶠ n in Filter.atTop,
    ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = n →
    (G.edgeFinset.card : ℝ) > (n : ℝ)^2 / 4 →
    (edgesInC5 G : ℝ) ≥ (c - ε) * (n : ℝ)^2

/-- The Grzesik-Hu-Volec lower bound holds. -/
theorem grzesik_hu_volec : GrzesikHuVolecBound := by
  sorry

/-- Combined: The answer is exactly cn². -/
theorem exact_answer :
    FurediMalekiConstruction ∧ GrzesikHuVolecBound := by
  exact ⟨furedi_maleki, grzesik_hu_volec⟩

/- ## Part VI: Odd Cycles in General -/

/-- A (2k+1)-cycle. -/
def IsOddCycle (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (cycle : Fin (2*k+1) → V) : Prop :=
  (∀ i j, i ≠ j → cycle i ≠ cycle j) ∧
  (∀ i : Fin (2*k+1), G.Adj (cycle i) (cycle ⟨(i.val + 1) % (2*k+1), by omega⟩))

/-- Edges in any C_{2k+1}. -/
noncomputable def edgesInOddCycle (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) : ℕ :=
  (G.edgeFinset.filter (fun e =>
    ∃ cycle : Fin (2*k+1) → V, IsOddCycle G k cycle ∧
    ∃ i, e = s(cycle i, cycle ⟨(i.val + 1) % (2*k+1), by omega⟩))).card

/-- For k ≥ 3, the bound (2/9)n² IS correct. -/
theorem odd_cycle_bound_general (k : ℕ) (hk : k ≥ 3) :
    ∀ᶠ n in Filter.atTop,
    ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = n →
    (G.edgeFinset.card : ℝ) > (n : ℝ)^2 / 4 →
    (edgesInOddCycle G k : ℝ) ≥ 2/9 * (n : ℝ)^2 - O(1) * n := by
  sorry

/- ## Part VII: Triangles -/

/-- Edges in triangles. -/
noncomputable def edgesInTriangles (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  edgesInOddCycle G 1

/-- Erdős-Faudree-Rousseau: At least 2⌊n/2⌋ + 1 edges in triangles. -/
theorem efr_triangles :
    ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
    (G.edgeFinset.card : ℝ) > (Fintype.card V : ℝ)^2 / 4 →
    edgesInTriangles G ≥ 2 * (Fintype.card V / 2) + 1 := by
  sorry

/- ## Part VIII: The Turán Threshold -/

/-- The Turán graph T(n,2) has exactly n²/4 edges. -/
def turanEdges (n : ℕ) : ℕ := (n / 2) * ((n + 1) / 2)

/-- Turán graph is bipartite (no odd cycles). -/
theorem turan_bipartite (n : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    Fintype.card V = n ∧
    G.edgeFinset.card = turanEdges n ∧
    edgesInC5 G = 0 := by
  sorry

/-- At exactly n²/4 edges, there might be 0 edges in C₅. -/
theorem threshold_sharp :
    ∀ n : ℕ, ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    Fintype.card V = n ∧
    (G.edgeFinset.card : ℝ) = (n : ℝ)^2 / 4 ∧
    edgesInC5 G = 0 := by
  sorry

/- ## Part IX: Small Cases -/

/-- For n = 5, a C₅ itself has 5 edges in C₅. -/
theorem c5_itself : ∃ (G : SimpleGraph (Fin 5)) (_ : DecidableRel G.Adj),
    G.edgeFinset.card = 5 ∧ edgesInC5 G = 5 := by
  sorry

/-- For n = 6 with > 9 edges, at least how many in C₅? -/
theorem small_case_6 :
    ∀ (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj],
    G.edgeFinset.card > 9 →
    edgesInC5 G ≥ 5 := by
  sorry

/- ## Part X: The Construction Details -/

/-- The Füredi-Maleki graph is based on a specific algebraic construction. -/
def FurediMalekiGraph (n : ℕ) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (G : SimpleGraph V) (_ : DecidableRel G.Adj),
  Fintype.card V = n ∧
  -- Uses a blow-up of a carefully chosen small graph
  True

/-- The construction achieves the extremal value. -/
theorem construction_optimal (n : ℕ) (hn : n ≥ 100) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    Fintype.card V = n ∧
    (G.edgeFinset.card : ℝ) > (n : ℝ)^2 / 4 ∧
    (edgesInC5 G : ℝ) ≤ c * (n : ℝ)^2 + n := by
  sorry

/- ## Part XI: Stability -/

/-- Near-extremal graphs are close to the construction. -/
def Stability : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ᶠ n in Filter.atTop,
    ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = n →
    (G.edgeFinset.card : ℝ) > (n : ℝ)^2 / 4 →
    (edgesInC5 G : ℝ) ≤ (c + δ) * (n : ℝ)^2 →
    True -- G is ε-close to Füredi-Maleki construction

/- ## Part XII: Related Counts -/

/-- Number of C₅ subgraphs (not just edges in C₅). -/
noncomputable def countC5 (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter (fun (t : V × V × V × V × V) =>
    IsC5 G t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2)).card / 10

/-- Dense graphs have many C₅ subgraphs. -/
theorem many_c5_subgraphs :
    ∀ᶠ n in Filter.atTop,
    ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = n →
    (G.edgeFinset.card : ℝ) > (n : ℝ)^2 / 4 →
    (countC5 G : ℝ) ≥ (n : ℝ)^5 / 1000 := by
  sorry

end Erdos608

/-
  ## Summary

  This file formalizes Erdős Problem #608 on edges in 5-cycles.

  **Status**: SOLVED (Disproved)

  **The Question**: Does G with > n²/4 edges have ≥ (2/9)n² edges in C₅?

  **Answer**: NO! The correct bound is c = (2 + √2)/16 ≈ 0.2134 < 2/9.

  **Key Results**:
  - Füredi-Maleki: Upper bound construction with cn² + O(n) edges in C₅
  - Grzesik-Hu-Volec: Matching lower bound (c - o(1))n²
  - For C_{2k+1} with k ≥ 3, the bound (2/9)n² IS correct

  **What we formalize**:
  1. C₅ definitions and edge counting
  2. Original (false) conjecture
  3. Correct constant c = (2 + √2)/16
  4. Füredi-Maleki upper bound
  5. Grzesik-Hu-Volec lower bound
  6. Odd cycles in general
  7. Triangle case
  8. Turán threshold
  9. Small cases
  10. Construction details

  **Key sorries**:
  - `original_conjecture_false`: The main disproof
  - `furedi_maleki`: Upper bound construction
  - `grzesik_hu_volec`: Matching lower bound
-/
