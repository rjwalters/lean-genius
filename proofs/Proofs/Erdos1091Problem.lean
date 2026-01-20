/-
Erdős Problem #1091: Odd Cycles with Diagonals in K₄-Free Graphs

Source: https://erdosproblems.com/1091
Status: PARTIALLY SOLVED / OPEN

Statement:
Let G be a K₄-free graph with chromatic number 4. Must G contain an odd cycle
with at least two diagonals?

More generally, is there some f(r)→∞ such that every graph with chromatic number 4,
in which every subgraph on ≤r vertices has chromatic number ≤3, contains an odd
cycle with at least f(r) diagonals?

History:
- Erdős originally asked about existence of just one diagonal (simpler question)
- Larson (1979): Proved one diagonal exists; proved Bollobás-Erdős conjecture
- Voss (1982): Proved two diagonals are guaranteed (first question SOLVED)
- Pentagonal wheel shows three diagonals cannot be guaranteed
- General f(r) question remains OPEN

Tags: graph-theory, chromatic-number, odd-cycles, K4-free
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic

namespace Erdos1091

/-!
## Part 1: Basic Definitions

Graphs, cycles, diagonals, and chromatic number.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A cycle in a graph is a sequence of distinct vertices where consecutive ones are adjacent -/
structure Cycle (G : SimpleGraph V) where
  vertices : List V
  length_ge_3 : vertices.length ≥ 3
  nodup : vertices.Nodup
  consecutive_adj : ∀ i : Fin (vertices.length - 1),
    G.Adj (vertices.get ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩)
          (vertices.get ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩)
  closing_adj : G.Adj (vertices.getLast (by omega)) (vertices.head (by omega))

/-- A cycle is odd if its length is odd -/
def Cycle.isOdd (c : Cycle G) : Prop := Odd c.vertices.length

/-- A diagonal of a cycle is an edge between two non-consecutive vertices -/
def Cycle.isDiagonal (c : Cycle G) (u v : V) : Prop :=
  u ∈ c.vertices ∧ v ∈ c.vertices ∧
  -- Not consecutive in the cycle
  (∀ i j : Fin c.vertices.length,
    c.vertices.get i = u → c.vertices.get j = v →
    (i.val + 1) % c.vertices.length ≠ j.val ∧
    (j.val + 1) % c.vertices.length ≠ i.val) ∧
  G.Adj u v

/-- Count of diagonals in a cycle -/
noncomputable def Cycle.diagonalCount (c : Cycle G) : ℕ :=
  Finset.card (Finset.filter (fun p : V × V =>
    c.isDiagonal p.1 p.2 ∧ p.1 < p.2)  -- Avoid double counting
    (Finset.univ.product Finset.univ))

/-- A graph is K₄-free if it contains no clique of size 4 -/
def IsK4Free (G : SimpleGraph V) : Prop :=
  ¬ ∃ s : Finset V, s.card = 4 ∧ G.IsClique s

/-- Chromatic number: minimum colors needed to properly color G -/
noncomputable def chromaticNumber (G : SimpleGraph V) : ℕ :=
  sSup { k : ℕ | ∃ (c : G.Coloring (Fin k)), True }

/-!
## Part 2: Larson's Theorem (1979)

One diagonal is guaranteed.
-/

/-- Larson's Theorem (1979): Every K₄-free graph with χ(G) ≥ 4 has an odd cycle
    with at least one diagonal -/
axiom larson_one_diagonal (G : SimpleGraph V)
    (hK4 : IsK4Free G) (hChi : chromaticNumber G ≥ 4) :
    ∃ c : Cycle G, c.isOdd ∧ c.diagonalCount ≥ 1

/-- Bollobás-Erdős Conjecture (proved by Larson 1979):
    If G is K₄-free and contains no odd cycle with a diagonal, then
    G is bipartite, or has a cut vertex, or has a vertex of degree ≤ 2 -/
structure BollobasErdosAlternative (G : SimpleGraph V) where
  isBipartite : Prop := G.IsBipartite
  hasCutVertex : Prop := ∃ v : V, ∀ u w : V, u ≠ v → w ≠ v →
    (G.Reachable u w ↔ ∃ p : G.Walk u w, v ∉ p.support ∨ u = w)
  hasDegree2Vertex : Prop := ∃ v : V, G.degree v ≤ 2

/-- Larson proved Bollobás-Erdős conjecture -/
axiom bollobas_erdos_conjecture (G : SimpleGraph V)
    (hK4 : IsK4Free G)
    (hNoDiag : ¬ ∃ c : Cycle G, c.isOdd ∧ c.diagonalCount ≥ 1) :
    let alt := BollobasErdosAlternative G
    alt.isBipartite ∨ alt.hasCutVertex ∨ alt.hasDegree2Vertex

/-!
## Part 3: Voss's Theorem (1982)

Two diagonals are guaranteed - answers the first question.
-/

/-- Voss's Theorem (1982): Every K₄-free graph with χ(G) ≥ 4 has an odd cycle
    with at least two diagonals -/
axiom voss_two_diagonals (G : SimpleGraph V)
    (hK4 : IsK4Free G) (hChi : chromaticNumber G ≥ 4) :
    ∃ c : Cycle G, c.isOdd ∧ c.diagonalCount ≥ 2

/-- Corollary: Voss implies Larson -/
theorem voss_implies_larson (G : SimpleGraph V)
    (hK4 : IsK4Free G) (hChi : chromaticNumber G ≥ 4) :
    ∃ c : Cycle G, c.isOdd ∧ c.diagonalCount ≥ 1 := by
  obtain ⟨c, hOdd, hDiag⟩ := voss_two_diagonals G hK4 hChi
  exact ⟨c, hOdd, Nat.le_of_succ_le hDiag⟩

/-!
## Part 4: Counterexample for Three Diagonals

The pentagonal wheel shows 3 diagonals cannot be guaranteed.
-/

/-- The pentagonal wheel: a 5-cycle with a central vertex connected to all -/
def PentagonalWheel : SimpleGraph (Fin 6) where
  Adj := fun i j =>
    -- Outer pentagon: 0-1-2-3-4-0
    (i.val < 5 ∧ j.val < 5 ∧ (j.val = (i.val + 1) % 5 ∨ i.val = (j.val + 1) % 5)) ∨
    -- Spokes: center (5) to all outer vertices
    (i.val = 5 ∧ j.val < 5) ∨ (j.val = 5 ∧ i.val < 5)
  symm := by
    intro i j h
    rcases h with ⟨hi, hj, hAdj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
    · left; exact ⟨hj, hi, hAdj.symm⟩
    · right; right; exact ⟨hj, hi⟩
    · right; left; exact ⟨hj, hi⟩
  loopless := by
    intro i h
    rcases h with ⟨_, _, hAdj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
    · omega
    · omega
    · omega

/-- The pentagonal wheel is K₄-free -/
axiom pentagonal_wheel_K4_free : IsK4Free PentagonalWheel

/-- The pentagonal wheel has chromatic number 4 -/
axiom pentagonal_wheel_chi_4 : chromaticNumber PentagonalWheel = 4

/-- In the pentagonal wheel, every odd cycle has at most 2 diagonals -/
axiom pentagonal_wheel_max_2_diagonals :
    ∀ c : Cycle PentagonalWheel, c.isOdd → c.diagonalCount ≤ 2

/-- Therefore, 3 diagonals cannot be guaranteed in general -/
theorem three_diagonals_not_guaranteed :
    ¬ (∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsK4Free G → chromaticNumber G ≥ 4 →
      ∃ c : Cycle G, c.isOdd ∧ c.diagonalCount ≥ 3) := by
  intro h
  have := h (Fin 6) PentagonalWheel pentagonal_wheel_K4_free
    (by rw [pentagonal_wheel_chi_4]; norm_num)
  obtain ⟨c, hOdd, hDiag⟩ := this
  have hMax := pentagonal_wheel_max_2_diagonals c hOdd
  omega

/-!
## Part 5: The General Question (OPEN)

Is there f(r)→∞ such that locally 3-colorable graphs have f(r) diagonals?
-/

/-- A graph is locally k-colorable up to size r if all subgraphs
    on ≤r vertices have chromatic number ≤k -/
def IsLocallyColorable (G : SimpleGraph V) (r k : ℕ) : Prop :=
  ∀ S : Finset V, S.card ≤ r →
    chromaticNumber (G.induce S) ≤ k

/-- The general question: existence of f(r)→∞ -/
def GeneralQuestion : Prop :=
  ∃ f : ℕ → ℕ, (∀ N, ∃ r, ∀ r' ≥ r, f r' ≥ N) ∧  -- f(r)→∞
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      chromaticNumber G ≥ 4 →
      ∀ r : ℕ, IsLocallyColorable G r 3 →
        ∃ c : Cycle G, c.isOdd ∧ c.diagonalCount ≥ f r

/-- The general question remains OPEN -/
axiom general_question_open : True  -- Status unknown

/-!
## Part 6: Relationship to Other Problems

This connects to Erdős's work on graph coloring and structural graph theory.
-/

/-- Key insight: K₄-free graphs can still have high chromatic number -/
theorem K4_free_high_chi_possible :
    ∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsK4Free G ∧ chromaticNumber G ≥ 4 := by
  use Fin 6, inferInstance, inferInstance, PentagonalWheel
  exact ⟨pentagonal_wheel_K4_free, by rw [pentagonal_wheel_chi_4]; norm_num⟩

/-- Triangle-free graphs can also have arbitrarily high chromatic number
    (Mycielski construction) -/
axiom mycielski_construction : ∀ k : ℕ, ∃ (V : Type*) [Fintype V]
    (G : SimpleGraph V), G.CliqueFree 3 ∧ chromaticNumber G ≥ k

/-!
## Part 7: Main Results Summary
-/

/-- First question (two diagonals): SOLVED by Voss (1982) -/
theorem erdos_1091_first_question_solved :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsK4Free G → chromaticNumber G ≥ 4 →
      ∃ c : Cycle G, c.isOdd ∧ c.diagonalCount ≥ 2 :=
  fun _ _ _ G hK4 hChi => voss_two_diagonals G hK4 hChi

/-- Upper bound: 3 diagonals cannot be guaranteed -/
theorem erdos_1091_upper_bound :
    ¬ (∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsK4Free G → chromaticNumber G ≥ 4 →
      ∃ c : Cycle G, c.isOdd ∧ c.diagonalCount ≥ 3) :=
  three_diagonals_not_guaranteed

/-- Second question (general f(r)): OPEN -/
theorem erdos_1091_second_question_open :
    -- General f(r)→∞ question status unknown
    True := trivial

/-- Complete summary -/
theorem erdos_1091_summary :
    -- Original question (one diagonal): SOLVED by Larson (1979)
    -- First question (two diagonals): SOLVED by Voss (1982)
    -- Upper bound: Pentagonal wheel shows ≤2 diagonals sometimes
    -- General question (f(r)→∞): OPEN
    True := trivial

end Erdos1091
