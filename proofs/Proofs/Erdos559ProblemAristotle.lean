/-
  Aristotle targets for Erdos559Problem

  Routine supporting lemmas for automated proof search.
  See Erdos559Problem.lean for the main formalization (size Ramsey numbers
  of bounded-degree graphs; Beck-Erdős conjecture, disproved by
  Rödl-Szemerédi 2000 for d = 3).

  These lemmas provide elementary building blocks Aristotle can attack:
  - Edge-count arithmetic on small finite graphs
  - Triangular-number identities for K_n edge counts
  - Path / cycle / tree edge count trivia
  - Basic asymptotics: n vs. n*(log n)^c vs. n^{3/2}
  - Trivial small-N witnesses for the open d=3 question
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Erdos559.Aristotle

open Finset

/-
  ## Section 1: K_n edge counts

  The complete graph K_n on n vertices has n*(n-1)/2 edges. We expose the
  small-case arithmetic Aristotle can verify trivially.
-/

/-- Edge count of K_n. -/
def kEdges (n : ℕ) : ℕ := n * (n - 1) / 2

-- Small K_n edge counts (TRIVIAL targets)
theorem kEdges_zero : kEdges 0 = 0 := by unfold kEdges; norm_num
theorem kEdges_one : kEdges 1 = 0 := by unfold kEdges; norm_num
theorem kEdges_two : kEdges 2 = 1 := by unfold kEdges; norm_num
theorem kEdges_three : kEdges 3 = 3 := by unfold kEdges; norm_num
theorem kEdges_four : kEdges 4 = 6 := by unfold kEdges; norm_num
theorem kEdges_five : kEdges 5 = 10 := by unfold kEdges; norm_num
theorem kEdges_six : kEdges 6 = 15 := by unfold kEdges; norm_num
theorem kEdges_seven : kEdges 7 = 21 := by unfold kEdges; norm_num
theorem kEdges_eight : kEdges 8 = 28 := by unfold kEdges; norm_num

-- kEdges matches Nat.choose n 2 (HARD: standard Mathlib equivalence)
theorem kEdges_eq_choose_two (n : ℕ) : kEdges n = Nat.choose n 2 := by sorry

-- kEdges is monotone in n
theorem kEdges_mono {n m : ℕ} (h : n ≤ m) : kEdges n ≤ kEdges m := by sorry

-- kEdges is strictly monotone for n ≥ 2
theorem kEdges_strict_mono {n m : ℕ} (hn : 2 ≤ n) (h : n < m) :
    kEdges n < kEdges m := by sorry

/-
  ## Section 2: Path and Cycle edge counts

  A path on n vertices has n-1 edges; a cycle on n vertices has n edges.
  These are the structural facts behind Beck's and Haxell-Kohayakawa-Luczak's
  linear bounds.
-/

/-- Edge count of a simple path on n vertices. -/
def pathEdges (n : ℕ) : ℕ := if n = 0 then 0 else n - 1

/-- Edge count of a simple cycle on n vertices (cycle requires n ≥ 3). -/
def cycleEdges (n : ℕ) : ℕ := if n < 3 then 0 else n

-- Path edge count small cases (TRIVIAL)
theorem pathEdges_zero : pathEdges 0 = 0 := by unfold pathEdges; simp
theorem pathEdges_one : pathEdges 1 = 0 := by unfold pathEdges; simp
theorem pathEdges_two : pathEdges 2 = 1 := by unfold pathEdges; simp
theorem pathEdges_three : pathEdges 3 = 2 := by unfold pathEdges; simp
theorem pathEdges_four : pathEdges 4 = 3 := by unfold pathEdges; simp
theorem pathEdges_ten : pathEdges 10 = 9 := by unfold pathEdges; simp

-- Cycle edge count small cases (TRIVIAL)
theorem cycleEdges_two : cycleEdges 2 = 0 := by unfold cycleEdges; simp
theorem cycleEdges_three : cycleEdges 3 = 3 := by unfold cycleEdges; simp
theorem cycleEdges_four : cycleEdges 4 = 4 := by unfold cycleEdges; simp
theorem cycleEdges_five : cycleEdges 5 = 5 := by unfold cycleEdges; simp
theorem cycleEdges_ten : cycleEdges 10 = 10 := by unfold cycleEdges; simp

-- Trees on n vertices have exactly n - 1 edges (for n ≥ 1)
def treeEdges (n : ℕ) : ℕ := if n = 0 then 0 else n - 1

theorem treeEdges_eq_pathEdges (n : ℕ) : treeEdges n = pathEdges n := by
  unfold treeEdges pathEdges; rfl

-- Linear-in-n cap: pathEdges n ≤ n (TRIVIAL)
theorem pathEdges_le (n : ℕ) : pathEdges n ≤ n := by
  unfold pathEdges; split <;> omega

-- Linear-in-n cap: cycleEdges n ≤ n (TRIVIAL)
theorem cycleEdges_le (n : ℕ) : cycleEdges n ≤ n := by
  unfold cycleEdges; split <;> omega

/-
  ## Section 3: Max-degree bookkeeping

  A graph with max degree ≤ d on n vertices has at most n*d/2 edges
  (counted with multiplicity via handshake lemma).
-/

/-- Edge-count upper bound from max degree (handshake). -/
def maxDegEdgeBound (n d : ℕ) : ℕ := n * d / 2

-- Small witnesses (TRIVIAL)
theorem maxDegEdgeBound_zero (d : ℕ) : maxDegEdgeBound 0 d = 0 := by
  unfold maxDegEdgeBound; simp
theorem maxDegEdgeBound_zero_deg (n : ℕ) : maxDegEdgeBound n 0 = 0 := by
  unfold maxDegEdgeBound; simp
theorem maxDegEdgeBound_3_3 : maxDegEdgeBound 10 3 = 15 := by
  unfold maxDegEdgeBound; norm_num

-- Monotone in n (HARD)
theorem maxDegEdgeBound_mono_n {n m d : ℕ} (h : n ≤ m) :
    maxDegEdgeBound n d ≤ maxDegEdgeBound m d := by sorry

-- Monotone in d (HARD)
theorem maxDegEdgeBound_mono_d {n d e : ℕ} (h : d ≤ e) :
    maxDegEdgeBound n d ≤ maxDegEdgeBound n e := by sorry

/-
  ## Section 4: Asymptotic separators

  Witnesses that n, n·(log n)^c, n·exp(c·√(log n)), and n^{3/2}
  are pairwise distinct asymptotic regimes — the regimes in play
  for the d=3 size Ramsey lower/upper bounds.
-/

/-- log n eventually exceeds any constant. -/
theorem log_unbounded :
    ∀ M : ℝ, ∃ N : ℝ, ∀ x ≥ N, Real.log x ≥ M := by sorry

/-- n^{3/2} dominates n linearly (n^{3/2} / n → ∞). -/
theorem n_pow_three_halves_dominates_linear :
    ∀ C : ℝ, ∃ N : ℝ, ∀ n : ℕ, (n : ℝ) ≥ N →
      (n : ℝ) ^ (3/2 : ℝ) ≥ C * n := by sorry

/-- exp(c·√(log n)) is unbounded for c > 0. -/
theorem exp_sqrt_log_unbounded (c : ℝ) (hc : c > 0) :
    ∀ M : ℝ, ∃ N : ℝ, ∀ x ≥ N,
      Real.exp (c * Real.sqrt (Real.log x)) ≥ M := by sorry

/-- exp(c·√(log n)) grows slower than any positive power of n. -/
theorem exp_sqrt_log_subpoly (c ε : ℝ) (hc : c > 0) (hε : ε > 0) :
    ∀ᶠ x in Filter.atTop,
      Real.exp (c * Real.sqrt (Real.log x)) ≤ x ^ ε := by sorry

/-
  ## Section 5: Trivial Ramsey witnesses for small N

  These do not establish the open conjecture, but they certify Aristotle's
  handle on the underlying edge counts for small N (no graph on < 2 vertices
  has any edges, etc.).
-/

/-- For N = 0 the size Ramsey number is 0 (empty graph). -/
def trivialRamseyZero : ℕ := 0

theorem trivialRamseyZero_eq : trivialRamseyZero = 0 := rfl

/-- For N = 1 the size Ramsey number is 0 (single vertex). -/
def trivialRamseyOne : ℕ := 0

theorem trivialRamseyOne_eq : trivialRamseyOne = 0 := rfl

/-- For N = 2 the size Ramsey number is at most 1 (single edge). -/
def trivialRamseyTwoBound : ℕ := 1

theorem trivialRamseyTwoBound_eq : trivialRamseyTwoBound = 1 := rfl

-- Each of these elementary witnesses sits below the maxDegEdgeBound (TRIVIAL)
theorem trivialRamseyOne_le_bound : trivialRamseyOne ≤ maxDegEdgeBound 1 1 := by
  unfold trivialRamseyOne maxDegEdgeBound; simp
theorem trivialRamseyTwoBound_le_bound :
    trivialRamseyTwoBound ≤ maxDegEdgeBound 2 1 := by
  unfold trivialRamseyTwoBound maxDegEdgeBound; norm_num

end Erdos559.Aristotle
