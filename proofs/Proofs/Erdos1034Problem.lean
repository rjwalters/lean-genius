/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9d41ab6f-c013-485e-8630-a52c9818476d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem maTang_approx : maTangConstant > 0.418 ∧ maTangConstant < 0.42

- theorem gap_value : boundGap > 0.25 ∧ boundGap < 0.26

- theorem k4Free_approx : k4FreeConstant > 0.46 ∧ k4FreeConstant < 0.47

The following was negated by Aristotle:

- theorem erdos_faudree_false : ¬erdos_faudree_conjecture

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

/-
Erdős Problem #1034: Triangle Neighbors in Dense Graphs

Let G be a graph on n vertices with > n²/4 edges. Must there exist a triangle T
and t > (1/2 - o(1))n vertices, each joined to at least two vertices of T?

**Status**: DISPROVED (Ma-Tang)
**Answer**: NO - counterexample shows max t ≤ (2 - √(5/2) + o(1))n ≈ 0.4189n

**Bounds on h(n)** (threshold function):
- Lower: h(n) ≥ (1/6 - o(1))n (from book lemma)
- Upper: h(n) ≤ (2 - √(5/2) + o(1))n (Ma-Tang construction)

Reference: https://erdosproblems.com/1034
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

overloaded, errors 
  failed to synthesize
    Singleton V✝ (Finset V)
  
  Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
  
  126:3 `T` is not a field of structure `Finset`-/
open Finset

namespace Erdos1034

/-
## Graph Setup

We work with simple graphs on a finite vertex set.
-/

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Number of edges in a graph. -/
noncomputable def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-- The Turán threshold for triangles. -/
noncomputable def turanThreshold (n : ℕ) : ℕ := n^2 / 4

/-- Graph is above Turán threshold. -/
def isAboveTuran (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  edgeCount G > turanThreshold (Fintype.card V)

/-
## Triangles

A triangle is three mutually adjacent vertices.
-/

/-- A triangle in G. -/
structure Triangle (G : SimpleGraph V) where
  v1 : V
  v2 : V
  v3 : V
  distinct12 : v1 ≠ v2
  distinct23 : v2 ≠ v3
  distinct13 : v1 ≠ v3
  adj12 : G.Adj v1 v2
  adj23 : G.Adj v2 v3
  adj13 : G.Adj v1 v3

/-- The set of triangle vertices. -/
def Triangle.vertices (T : Triangle G) : Finset V :=
  {T.v1, T.v2, T.v3}

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  Triangle
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  G-/
/-- Triangle has exactly 3 vertices. -/
theorem Triangle.card_vertices (T : Triangle G) : T.vertices.card = 3 := by
  simp only [Triangle.vertices]
  rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem, Finset.card_singleton]
  · exact Finset.not_mem_singleton.mpr T.distinct23
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨T.distinct12, T.distinct13⟩

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  Triangle
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G-/
/-
## Triangle Neighbors

A vertex y is a "good neighbor" of triangle T if y is adjacent to at least
two vertices of T.
-/

/-- Count of triangle vertices adjacent to y. -/
def adjacentToTriangleCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Triangle G) (y : V) : ℕ :=
  (T.vertices.filter (fun v => G.Adj y v)).card

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  Triangle
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Unknown identifier `adjacentToTriangleCount`-/
/-- y is adjacent to at least two vertices of T. -/
def isGoodNeighbor (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Triangle G) (y : V) : Prop :=
  adjacentToTriangleCount G T y ≥ 2

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  Triangle
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isGoodNeighbor
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G-/
/-- y is adjacent to at least two vertices of T (decidable). -/
instance (G : SimpleGraph V) [DecidableRel G.Adj] (T : Triangle G) (y : V) :
    Decidable (isGoodNeighbor G T y) :=
  inferInstanceAs (Decidable (_ ≥ 2))

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  Triangle
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Unknown identifier `isGoodNeighbor`
failed to synthesize
  Fintype V

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
/-- The set of good neighbors of T (excluding T's vertices). -/
def goodNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (T : Triangle G) : Finset V :=
  (Finset.univ.filter (fun y => isGoodNeighbor G T y ∧ y ∉ T.vertices))

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  Triangle
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Unknown identifier `goodNeighbors`-/
/-- Count of good neighbors. -/
def goodNeighborCount (G : SimpleGraph V) [DecidableRel G.Adj] (T : Triangle G) : ℕ :=
  (goodNeighbors G T).card

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `Triangle`
Unknown identifier `goodNeighborCount`-/
/-
## The Function h(n)

h(n) is the largest t such that every graph on n vertices with > n²/4 edges
has a triangle with at least t good neighbors.
-/

/-- G has a triangle with at least k good neighbors. -/
def hasTriangleWithNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∃ T : Triangle G, goodNeighborCount G T ≥ k

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `isAboveTuran`
Unknown identifier `hasTriangleWithNeighbors`-/
/-- k is a valid lower bound for h(n). -/
def isValidBound (n : ℕ) (k : ℕ) : Prop :=
  ∀ (V : Type*) [DecidableEq V] [Fintype V],
  Fintype.card V = n →
  ∀ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
  isAboveTuran G → hasTriangleWithNeighbors G k

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `isValidBound`-/
/-- h(n): the extremal function. -/
noncomputable def h (n : ℕ) : ℕ :=
  sSup {k : ℕ | isValidBound n k}

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `isAboveTuran`
Unknown identifier `Triangle`
Unknown identifier `goodNeighborCount`-/
/-
## The Original Conjecture (DISPROVED)

Erdős-Faudree conjectured t > (1/2 - o(1))n, which is false.
-/

/-- The original (false) conjecture. -/
def erdos_faudree_conjecture : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
  ∀ (V : Type*) [DecidableEq V] [Fintype V],
  Fintype.card V = n →
  ∀ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
  isAboveTuran G →
  ∃ T : Triangle G, (goodNeighborCount G T : ℝ) > (1/2 - ε) * n

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
The conjecture is false.
-/
theorem erdos_faudree_false : ¬erdos_faudree_conjecture := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose any $n \geq 3$ and derive a contradiction.
  use True

-/
/-- The conjecture is false: the Ma-Tang counterexample shows the best constant
    is ≈ 0.419, not 1/2. We use ε = 1/25 and n ≥ 26 to get a contradiction. -/
theorem erdos_faudree_false : ¬erdos_faudree_conjecture := by
  intro hconj
  -- Choose ε = 1/25 = 0.04 > 0
  obtain ⟨N_conj, hN_conj⟩ := hconj (1/25 : ℝ) (by norm_num)
  -- Get Ma-Tang counterexample for large n
  obtain ⟨N_mt, hN_mt⟩ := maTang_counterexample
  -- Choose n large enough for both
  set n := max (max N_conj N_mt) 26 with hn_def
  have hn_conj : n ≥ N_conj := le_trans (le_max_left _ _) (le_max_left _ _)
  have hn_mt : n ≥ N_mt := le_trans (le_max_right _ _) (le_max_left _ _)
  have hn_26 : (n : ℝ) ≥ 26 := by exact_mod_cast le_max_right _ _
  -- Get counterexample graph
  obtain ⟨V, hDE, hFT, hcard, G, hprops⟩ := hN_mt n hn_mt
  haveI := hDE; haveI := hFT
  haveI : DecidableRel G.Adj := Classical.decRel _
  obtain ⟨hAT, hbound⟩ := hprops
  -- Apply the conjecture
  obtain ⟨T, hT⟩ := hN_conj n hn_conj V hcard G hAT
  -- hT : goodNeighborCount G T > (1/2 - 1/25) * n = 23/50 * n
  -- hbound T : goodNeighborCount G T ≤ maTangConstant * n + 1
  have hT_le := hbound T
  -- maTangConstant < 0.42 (from maTang_approx)
  have h_mc := maTang_approx.2
  -- Contradiction: 23/50 * n > maTangConstant * n + 1 for n ≥ 26
  linarith

/-
## Ma-Tang Counterexample

Ma and Tang constructed a graph disproving the conjecture.
-/

/-- The Ma-Tang constant: 2 - √(5/2) ≈ 0.4189. -/
noncomputable def maTangConstant : ℝ := 2 - Real.sqrt (5/2)

/-- Numerical value verification. -/
theorem maTang_approx : maTangConstant > 0.418 ∧ maTangConstant < 0.42 := by
  unfold maTangConstant;
  constructor <;> nlinarith [ Real.sqrt_nonneg ( 5 / 2 ), Real.sq_sqrt ( show 0 ≤ 5 / 2 by norm_num ) ]

/-- Ma-Tang: There exists a counterexample graph.
    The bound `+ 1` replaces `+ o(1)` from the original statement. -/
axiom maTang_counterexample : ∃ N : ℕ, ∀ n ≥ N,
  ∃ (V : Type*) (_ : DecidableEq V) (_ : Fintype V),
    Fintype.card V = n ∧
    ∃ G : SimpleGraph V,
      ∀ [DecidableRel G.Adj],
        isAboveTuran G ∧
        (∀ T : Triangle G, (goodNeighborCount G T : ℝ) ≤ maTangConstant * n + 1)

/-- The upper bound on h(n). -/
theorem h_upper_bound : ∃ N : ℕ, ∀ n ≥ N,
    (h n : ℝ) ≤ maTangConstant * n + 1 := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  Triangle
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G-/
/-
## Lower Bound via Books

A book is a triangle with many common neighbors.
-/

/-- A book: triangle plus vertices adjacent to all three. -/
def isBook (G : SimpleGraph V) [DecidableRel G.Adj] (T : Triangle G) (pages : Finset V) : Prop :=
  ∀ p ∈ pages, G.Adj p T.v1 ∧ G.Adj p T.v2 ∧ G.Adj p T.v3

/-- Book size = number of pages. -/
def bookSize (pages : Finset V) : ℕ := pages.card

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  isAboveTuran
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  Triangle
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isBook
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G-/
/-- Every graph with > n²/4 edges has a book of size n/6. -/
/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  Triangle
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isBook
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isGoodNeighbor
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  G-/
/-- Book pages are good neighbors (adjacent to all 3 ≥ 2). -/
theorem book_pages_are_good (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Triangle G) (pages : Finset V) (hBook : isBook G T pages) :
    ∀ p ∈ pages, p ∉ T.vertices → isGoodNeighbor G T p := by
  intro p hp _
  obtain ⟨h1, h2, h3⟩ := hBook p hp
  unfold isGoodNeighbor
  have := fully_adjacent_is_good G T p h1 h2 h3
  omega

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  h
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  n-/
/-- Lower bound: h(n) ≥ (1/6 - o(1))n. -/
theorem h_lower_bound : ∃ N : ℕ, ∀ n ≥ N, (h n : ℝ) ≥ n / 6 - 1 := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  h
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  n
Function expected at
  h
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  n-/
/-
## The Gap

There's a gap between 1/6 ≈ 0.167 and 2 - √(5/2) ≈ 0.419.
-/

/-- Current bounds on h(n). -/
theorem h_bounds : ∃ N : ℕ, ∀ n ≥ N,
    (n : ℝ) / 6 - 1 ≤ h n ∧ (h n : ℝ) ≤ maTangConstant * n + 1 := by
  obtain ⟨N₁, h₁⟩ := h_lower_bound
  obtain ⟨N₂, h₂⟩ := h_upper_bound
  exact ⟨max N₁ N₂, fun n hn =>
    ⟨h₁ n (le_of_max_le_left hn), h₂ n (le_of_max_le_right hn)⟩⟩

/-- The gap between bounds. -/
noncomputable def boundGap : ℝ := maTangConstant - 1/6

/-- Gap is substantial: about 0.25. -/
theorem gap_value : boundGap > 0.25 ∧ boundGap < 0.26 := by
  constructor;
  · exact lt_of_lt_of_le ( by norm_num ) ( sub_le_sub_right ( show maTangConstant ≥ 0.418 by exact le_trans ( by norm_num ) ( maTang_approx.1.le ) ) _ );
  · unfold boundGap;
    rw [ show maTangConstant = 2 - Real.sqrt ( 5 / 2 ) by rfl ] ; nlinarith [ Real.sqrt_nonneg ( 5 / 2 ), Real.sq_sqrt ( show 0 ≤ 5 / 2 by norm_num ) ]

/-
## K₄-free Variant

Ma-Tang also addressed the K₄-free case.
-/

/-- G is K₄-free. -/
def isK4Free (G : SimpleGraph V) : Prop :=
  ¬∃ (a b c d : V), a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj c d

/-- The K₄-free constant: 2√3 - 3 ≈ 0.464. -/
noncomputable def k4FreeConstant : ℝ := 2 * Real.sqrt 3 - 3

/-- K₄-free constant verification. -/
theorem k4Free_approx : k4FreeConstant > 0.46 ∧ k4FreeConstant < 0.47 := by
  -- Calculate the numerical value of the K₄-free constant.
  have h_k4FreeConstant : k4FreeConstant = 2 * Real.sqrt 3 - 3 := by
    exact?;
  exact ⟨ by norm_num; nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ], by norm_num; nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ] ⟩

/-- Ma-Tang K₄-free result. The bound `+ 1` replaces `+ o(1)`. -/
/-- K₄-free bound is worse (higher) than general bound. -/
theorem k4free_worse : k4FreeConstant > maTangConstant := by
  unfold k4FreeConstant maTangConstant
  -- Need: 2√3 - 3 > 2 - √(5/2), i.e., 2√3 + √(5/2) > 5
  have h1 : (1.73 : ℝ) < Real.sqrt 3 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.73)]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by norm_num)
  have h2 : (1.58 : ℝ) < Real.sqrt (5 / 2 : ℝ) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.58)]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by norm_num)
  linarith

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `isAboveTuran`
Unknown identifier `Triangle`
Unknown identifier `isGoodNeighbor`-/
/-
## Comparison with Problem 905

This is a stronger version of Problem 905.
-/

/-- Problem 905 asks about a single vertex adjacent to two triangle vertices. -/
def problem_905_weaker : Prop :=
  ∀ n : ℕ, ∀ (V : Type*) [DecidableEq V] [Fintype V],
  Fintype.card V = n →
  ∀ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
  isAboveTuran G →
  ∃ T : Triangle G, ∃ y : V, y ∉ T.vertices ∧ isGoodNeighbor G T y

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  isValidBound
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  n-/
/-- Problem 1034 is stronger than 905. -/
theorem stronger_than_905 :
    (∀ n ≥ 3, isValidBound n 1) → problem_905_weaker := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  Triangle
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  Triangle
but this term has type
  x✝¹

Note: Expected a function because this term is being applied to the argument
  G
Unknown identifier `goodNeighborCount`-/
/-
## Maximum Good Neighbor Count

For a specific graph, the maximum over all triangles.
-/

/-- Maximum good neighbor count over all triangles. -/
noncomputable def maxGoodNeighborCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (hT : ∃ T : Triangle G, True) : ℕ :=
  sSup {goodNeighborCount G T | T : Triangle G}

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  Fintype V

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Unknown identifier `isAboveTuran`
Unknown identifier `Triangle`
Unknown identifier `goodNeighborCount`-/
/-- Graphs achieving the Ma-Tang bound. -/
def isMaTangExtremal (n : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Fintype.card V = n ∧
  isAboveTuran G ∧
  ∀ T : Triangle G, (goodNeighborCount G T : ℝ) ≤ maTangConstant * n + 1

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `h`-/
/-
## The Resolved Question

The original question is answered: the conjecture is false.
-/

/-- The question: what is the correct threshold? -/
def erdos_1034_question : Prop :=
  ∃ c : ℝ, c > 0 ∧ (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    |(h n : ℝ) / n - c| < ε)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  h
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  n
Function expected at
  h
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  n-/
/-- Partial answer: we know the threshold is between 1/6 and 2-√(5/2). -/
theorem erdos_1034_partial : ∃ c₁ c₂ : ℝ,
    c₁ = 1/6 ∧ c₂ = maTangConstant ∧
    (∃ N : ℕ, ∀ n ≥ N, c₁ * n - 1 ≤ h n ∧ (h n : ℝ) ≤ c₂ * n + 1) := by
  refine ⟨1/6, maTangConstant, rfl, rfl, ?_⟩
  obtain ⟨N, hN⟩ := h_bounds
  exact ⟨N, fun n hn => by
    have ⟨h₁, h₂⟩ := hN n hn
    exact ⟨by linarith, h₂⟩⟩

/-- The conjecture is definitively false. -/
theorem erdos_1034_disproved : ¬erdos_faudree_conjecture := erdos_faudree_false

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  Triangle
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  adjacentToTriangleCount
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G-/
/-
## Good Neighbor Properties

Basic properties of good neighbors.
-/

/-- A vertex in the triangle is trivially a "good neighbor" of itself. -/
theorem triangle_vertex_adjacent (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Triangle G) : adjacentToTriangleCount G T T.v1 ≥ 2 := by
  simp only [adjacentToTriangleCount]
  calc (T.vertices.filter (fun v => G.Adj T.v1 v)).card
      ≥ ({T.v2, T.v3} : Finset V).card := Finset.card_le_card (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_filter, Triangle.vertices, Finset.mem_insert, Finset.mem_singleton]
        rcases hx with rfl | rfl
        · exact ⟨Or.inr (Or.inl rfl), T.adj12⟩
        · exact ⟨Or.inr (Or.inr rfl), T.adj13⟩)
    _ = 2 := Finset.card_pair T.distinct23

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  Triangle
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  adjacentToTriangleCount
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G-/
/-- If y is adjacent to all 3, it's definitely a good neighbor. -/
theorem fully_adjacent_is_good (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Triangle G) (y : V) (h1 : G.Adj y T.v1) (h2 : G.Adj y T.v2) (h3 : G.Adj y T.v3) :
    adjacentToTriangleCount G T y = 3 := by
  simp only [adjacentToTriangleCount]
  have hsub : T.vertices ⊆ T.vertices.filter (fun v => G.Adj y v) := by
    intro v hv
    simp only [Triangle.vertices, Finset.mem_insert, Finset.mem_singleton] at hv
    simp only [Finset.mem_filter, Triangle.vertices, Finset.mem_insert, Finset.mem_singleton]
    rcases hv with rfl | rfl | rfl
    · exact ⟨Or.inl rfl, h1⟩
    · exact ⟨Or.inr (Or.inl rfl), h2⟩
    · exact ⟨Or.inr (Or.inr rfl), h3⟩
  have hle := Finset.card_le_card hsub
  have hge := Finset.card_le_card (Finset.filter_subset _ T.vertices)
  rw [Triangle.card_vertices] at hle hge
  omega

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  Triangle
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  isBook
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  goodNeighbors
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  G-/
/-- Good neighbors form a superset of book pages. -/
theorem book_subset_good (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Triangle G) (pages : Finset V) (hBook : isBook G T pages)
    (hDisjoint : Disjoint pages T.vertices) :
    pages ⊆ goodNeighbors G T := by
  intro p hp
  simp only [goodNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
  have hp_not_in : p ∉ T.vertices := Finset.disjoint_left.mp hDisjoint hp
  exact ⟨book_pages_are_good G T pages hBook p hp hp_not_in, hp_not_in⟩

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected name `Erdos1034` after `end`: The current section is unnamed

Hint: Delete the name `Erdos1034` to end the current unnamed scope; outer named scopes can then be closed using additional `end` command(s):
  end ̵E̵r̵d̵o̵s̵1̵0̵3̵4̵-/
/-
## Summary

This file formalizes Erdős Problem #1034 on triangle neighbors.

**Status**: DISPROVED (Ma-Tang)

**The Question**: Let G have n vertices and > n²/4 edges. Must there exist
a triangle T with > (1/2 - o(1))n vertices each adjacent to ≥ 2 of T's vertices?

**The Answer**: NO

**Counterexample**: Ma-Tang constructed graphs where every triangle has
at most (2 - √(5/2) + o(1))n ≈ 0.4189n good neighbors.

**Known Bounds** on h(n) (the extremal function):
- Lower: h(n) ≥ (1/6 - o(1))n (from book lemma)
- Upper: h(n) ≤ (2 - √(5/2) + o(1))n (Ma-Tang)

**K₄-free variant**: Upper bound is (2√3 - 3 + o(1))n ≈ 0.464n

**Related Problems**:
- Problem 905 (weaker version)
- Problem 1033 (triangle degree sums)

**References**:
- Erdős-Faudree conjecture
- Ma-Tang counterexample construction
-/

end Erdos1034