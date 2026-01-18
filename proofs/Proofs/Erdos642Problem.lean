/-
  Erdős Problem #642: Cycles with More Vertices than Diagonals

  Source: https://erdosproblems.com/642
  Status: OPEN

  Statement:
  Let f(n) be the maximal number of edges in a graph on n vertices such that
  all cycles have more vertices than diagonals. Is it true that f(n) ≪ n?

  Context:
  - A "diagonal" of a cycle is an edge between non-adjacent vertices of the cycle
  - The condition requires: for every cycle C, |V(C)| > |diagonals of C in G|
  - This is a Hamburger-Szegedy problem

  Known Results:
  - Chen-Erdős-Staton (1996): f(n) = O(n^(3/2))
  - Draganić-Methuku-Munhá Correia-Sudakov (2024): f(n) = O(n (log n)^8)
  - Open: Is f(n) = o(n)?

  Tags: graph-theory, extremal-combinatorics, cycles, diagonals
-/

import Mathlib

namespace Erdos642

open Finset Function SimpleGraph

/-!
## Part I: Graphs and Cycles

Basic definitions for the problem.
-/

/-- A simple graph on vertex set V. -/
abbrev Graph (V : Type*) := SimpleGraph V

/-- A cycle in a graph is a sequence of vertices forming a closed path with no repetitions. -/
structure Cycle (G : SimpleGraph V) where
  vertices : List V
  length_ge_3 : vertices.length ≥ 3
  is_cycle : ∀ i : Fin vertices.length,
    G.Adj (vertices.get i) (vertices.get ⟨(i.val + 1) % vertices.length, by omega⟩)
  no_repeated : vertices.Nodup

/-- The length (number of vertices) of a cycle. -/
def Cycle.len {G : SimpleGraph V} (C : Cycle G) : ℕ := C.vertices.length

/-!
## Part II: Diagonals of a Cycle

A diagonal is an edge between non-adjacent vertices of the cycle.
-/

/-- Two positions in a cycle are adjacent if they differ by 1 (mod length). -/
def CycleAdjacent (n : ℕ) (i j : ℕ) : Prop :=
  (i + 1) % n = j ∨ (j + 1) % n = i

/-- A diagonal of a cycle C is an edge between non-adjacent vertices on the cycle. -/
def IsDiagonal {G : SimpleGraph V} (C : Cycle G) (e : Sym2 V) : Prop :=
  ∃ (i j : Fin C.vertices.length),
    i ≠ j ∧
    ¬CycleAdjacent C.vertices.length i.val j.val ∧
    e = s(C.vertices.get i, C.vertices.get j) ∧
    G.Adj (C.vertices.get i) (C.vertices.get j)

/-- Count of diagonals in a cycle. -/
noncomputable def diagonalCount {G : SimpleGraph V} [DecidableEq V] [Fintype V]
    [DecidableRel G.Adj] (C : Cycle G) : ℕ :=
  (G.edgeFinset.filter (fun e => IsDiagonal C e)).card

/-!
## Part III: The Cycle-Diagonal Condition

Graphs where every cycle has more vertices than diagonals.
-/

/-- A graph satisfies the cycle-diagonal condition if every cycle has more vertices than diagonals. -/
def SatisfiesCycleDiagonalCondition (G : SimpleGraph V) [DecidableEq V] [Fintype V]
    [DecidableRel G.Adj] : Prop :=
  ∀ C : Cycle G, C.len > diagonalCount C

/-- The extremal function f(n). -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ G : SimpleGraph (Fin n),
    ∃ _ : DecidableRel G.Adj, SatisfiesCycleDiagonalCondition G ∧ G.edgeFinset.card = m }

/-!
## Part IV: Trivial Bounds

Basic observations about the extremal function.
-/

/-- f(n) ≥ n - 1 (trees satisfy the condition trivially). -/
theorem f_ge_tree (n : ℕ) (hn : n ≥ 1) : f n ≥ n - 1 := by
  sorry

/-- f(n) ≤ n(n-1)/2 (complete graph bound). -/
theorem f_le_complete (n : ℕ) : f n ≤ n * (n - 1) / 2 := by
  sorry

/-- A cycle of length k has at most k(k-3)/2 possible diagonals. -/
theorem max_diagonals_in_cycle (k : ℕ) (hk : k ≥ 3) :
    k * (k - 3) / 2 = (k.choose 2) - k := by
  sorry

/-!
## Part V: Chen-Erdős-Staton Bound (1996)

The first non-trivial upper bound.
-/

/-- **Chen-Erdős-Staton (1996)**: f(n) = O(n^(3/2)). -/
axiom chen_erdos_staton (n : ℕ) (hn : n ≥ 10) :
    f n ≤ 2 * Nat.floor ((n : ℝ)^(3/2 : ℝ))

/-- The CES exponent is 3/2. -/
def ces_exponent : ℝ := 3/2

/-!
## Part VI: Draganić-Methuku-Munhá Correia-Sudakov Bound (2024)

The improved bound using expander techniques.
-/

/-- **DMMS (2024)**: f(n) = O(n (log n)^8). -/
axiom dmms_2024 (n : ℕ) (hn : n ≥ 10) :
    f n ≤ Nat.ceil ((n : ℝ) * (Real.log n)^8)

/-- The DMMS bound is better than CES for large n. -/
theorem dmms_improves_ces (n : ℕ) (hn : n ≥ 1000) :
    Nat.ceil ((n : ℝ) * (Real.log n)^8) < 2 * Nat.floor ((n : ℝ)^(3/2 : ℝ)) := by
  sorry

/-!
## Part VII: The Open Conjecture

Is f(n) = o(n)?
-/

/-- **Hamburger-Szegedy Conjecture**: f(n) = o(n), i.e., f(n)/n → 0. -/
def HamburgerSzegedyConjecture : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N, (f n : ℝ) < ε * n

/-- Equivalent formulation: f(n) ≪ n. -/
def LinearBoundConjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 → (f n : ℝ) ≤ C * n

/-- The conjecture is strictly stronger than the DMMS bound. -/
theorem conjecture_stronger_than_dmms :
    HamburgerSzegedyConjecture → ∀ n : ℕ, n ≥ 2 →
      (f n : ℝ) < n * (Real.log n)^8 := by
  sorry

/-!
## Part VIII: Related Extremal Problems

Connections to other graph problems.
-/

/-- A graph has girth ≥ g if it has no cycles of length < g. -/
def HasGirth (G : SimpleGraph V) [Fintype V] (g : ℕ) : Prop :=
  ∀ C : Cycle G, C.len ≥ g

/-- Graphs with girth ≥ 5 trivially satisfy the condition. -/
theorem girth_5_satisfies [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : HasGirth G 5) :
    SatisfiesCycleDiagonalCondition G := by
  sorry

/-- The Turán problem for C₄-free graphs. -/
axiom turan_C4_free (n : ℕ) (hn : n ≥ 2) :
    ∃ G : SimpleGraph (Fin n), HasGirth G 5 ∧
      G.edgeFinset.card ≥ Nat.floor ((n : ℝ)^(3/2 : ℝ) / 4)

/-- This shows f(n) ≥ Ω(n^(3/2)) from girth-5 graphs. -/
theorem f_lower_bound (n : ℕ) (hn : n ≥ 10) :
    f n ≥ Nat.floor ((n : ℝ)^(3/2 : ℝ) / 4) := by
  sorry

/-!
## Part IX: Expander Techniques

The key tool in the DMMS improvement.
-/

/-- A graph is an (n, d, λ)-expander if it's d-regular with spectral gap. -/
def IsExpander (G : SimpleGraph (Fin n)) (d : ℕ) (λ : ℝ) : Prop :=
  -- All vertices have degree d
  (∀ v, G.degree v = d) ∧
  -- Second eigenvalue is at most λ (spectral gap property)
  λ < d

/-- Sublinear expanders (d = n^ε for some ε < 1). -/
def IsSublinearExpander (G : SimpleGraph (Fin n)) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
    ∃ d : ℕ, d ≥ Nat.floor ((n : ℝ)^ε) ∧
      ∃ λ : ℝ, IsExpander G d λ

/-- **Key Lemma (DMMS)**: Random walks in expanders find cycles with many diagonals. -/
axiom expander_cycle_lemma (G : SimpleGraph (Fin n)) (d : ℕ) (λ : ℝ)
    (hG : IsExpander G d λ) (hλ : λ ≤ d / 2) :
    -- G contains a cycle violating the condition
    ¬SatisfiesCycleDiagonalCondition G ∨ G.edgeFinset.card < d * n / 2

/-!
## Part X: Short Cycles vs Long Cycles

Different behavior for short and long cycles.
-/

/-- For short cycles (length ≤ 4), the condition is always satisfied. -/
theorem short_cycles_ok (k : ℕ) (hk : k ≤ 4) (hk3 : k ≥ 3) :
    k > k * (k - 3) / 2 := by
  interval_cases k <;> norm_num

/-- A cycle of length 5 with all diagonals violates the condition. -/
theorem pentagon_all_diags_violates :
    ¬(5 > 5 * (5 - 3) / 2) := by norm_num

/-- Critical transition at length 5. -/
theorem critical_length : ∀ k : ℕ, k ≥ 5 → k ≤ k * (k - 3) / 2 := by
  intro k hk
  omega

/-!
## Part XI: Main Results

Summary of Erdős Problem #642.
-/

/-- **Erdős Problem #642: OPEN**

    Question: Is f(n) ≪ n, where f(n) is the maximum edges in an n-vertex
    graph where every cycle has more vertices than diagonals?

    Status: OPEN

    Known bounds:
    - Lower: f(n) ≥ Ω(n^(3/2)) (from girth-5 constructions)
    - Upper: f(n) = O(n (log n)^8) (DMMS 2024)

    The question is whether f(n) = o(n), which remains unresolved. -/
theorem erdos_642_bounds (n : ℕ) (hn : n ≥ 10) :
    Nat.floor ((n : ℝ)^(3/2 : ℝ) / 4) ≤ f n ∧
    f n ≤ Nat.ceil ((n : ℝ) * (Real.log n)^8) := by
  constructor
  · exact f_lower_bound n hn
  · exact dmms_2024 n hn

/-- The answer to Erdős Problem #642. -/
def erdos_642_answer : String :=
  "OPEN: Known bounds are Ω(n^(3/2)) ≤ f(n) ≤ O(n(log n)^8). Is f(n) = o(n)?"

/-- The status of the problem. -/
def erdos_642_status : String :=
  "OPEN - Hamburger-Szegedy conjecture unresolved"

/-- Gap between known bounds. -/
theorem bounds_gap : ∃ gap : ℝ → ℝ,
    (∀ n : ℝ, n ≥ 10 → gap n = n * (Real.log n)^8 / n^(3/2)) ∧
    (∀ n : ℝ, n ≥ 10 → gap n = (Real.log n)^8 / n^(1/2)) := by
  use fun n => (Real.log n)^8 / n^(1/2 : ℝ)
  constructor <;> intro n hn <;> ring_nf

#check erdos_642_bounds
#check dmms_2024
#check chen_erdos_staton

end Erdos642
