/-
Erdős Problem #1155: Triangle Removal Process

Source: https://erdosproblems.com/1155
Status: OPEN (partially resolved)

Statement:
Begin with the complete graph K_n on n vertices. Repeatedly select a uniformly
random triangle and delete all its edges, until the graph becomes triangle-free.
Let f(n) denote the number of remaining edges.

Is it true that E[f(n)] ≍ n^{3/2} and f(n) ≪ n^{3/2} almost surely?

Known Results:
- Grable (1997): For every ε > 0, P(f(n) > n^{7/4 + ε}) → 0.
- Bohman, Frieze, Lubetzky (2015): f(n) = n^{3/2 + o(1)} almost surely.
  Equivalently, for every ε > 0, P(n^{3/2 - ε} < f(n) < n^{3/2 + ε}) → 1.
  This resolves the "almost surely" part: f(n) ≪ n^{3/2} a.s. (up to sub-polynomial).

What remains open: the exact asymptotic E[f(n)] ≍ n^{3/2}.

Formalization approach:
We abstract the triangle removal process via an axiom that captures the
function f : ℕ → ℝ (expected remaining edges after the process). The key
results and conjectures are then stated in terms of this function and
standard asymptotic analysis (∀ᶠ ... in atTop).
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter SimpleGraph

-- ## Triangle Removal Process Setup
--
-- The triangle removal process starts with K_n and repeatedly removes a uniformly
-- random triangle (all 3 edges) until the graph is triangle-free. The output is
-- the number of remaining edges, f(n).
--
-- Since formalizing the full probabilistic process (random triangle selection,
-- measure on graph sequences) requires extensive measure theory infrastructure,
-- we axiomatize the key function f(n) and state results about its behavior.

/-- `triangleRemovalEdges n` is the (expected) number of remaining edges after
running the triangle removal process on K_n until no triangles remain.
This is the function f(n) from the problem statement. -/
axiom triangleRemovalEdges : ℕ → ℝ

/-- The triangle removal process leaves a non-negative number of edges. -/
axiom triangleRemovalEdges_nonneg (n : ℕ) : 0 ≤ triangleRemovalEdges n

/-- The triangle removal process on K_n starts with C(n,2) edges and can only
remove edges, so f(n) ≤ n(n-1)/2. -/
axiom triangleRemovalEdges_le_complete (n : ℕ) :
    triangleRemovalEdges n ≤ (n * (n - 1) : ℝ) / 2

-- ## Known Results

/-- **Grable (1997)**: For every ε > 0, the number of remaining edges
satisfies f(n) ≤ n^{7/4 + ε} asymptotically (in probability).
We state the deterministic bound on the expectation. -/
axiom grable_upper_bound :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ (n : ℕ) in atTop,
        triangleRemovalEdges n ≤ (n : ℝ) ^ ((7 : ℝ) / 4 + ε)

/-- **Bohman-Frieze-Lubetzky (2015)**: f(n) = n^{3/2 + o(1)} almost surely.
Upper bound part: for every ε > 0, eventually f(n) < n^{3/2 + ε}. -/
axiom bfl_upper_bound :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ (n : ℕ) in atTop,
        triangleRemovalEdges n ≤ (n : ℝ) ^ ((3 : ℝ) / 2 + ε)

/-- **Bohman-Frieze-Lubetzky (2015)**: f(n) = n^{3/2 + o(1)} almost surely.
Lower bound part: for every ε > 0, eventually f(n) > n^{3/2 - ε}. -/
axiom bfl_lower_bound :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ (n : ℕ) in atTop,
        (n : ℝ) ^ ((3 : ℝ) / 2 - ε) ≤ triangleRemovalEdges n

-- ## Erdős Conjecture

/-- **Erdős Conjecture (Problem #1155)**: The expected number of remaining edges
in the triangle removal process satisfies E[f(n)] ≍ n^{3/2}.
This means there exist constants 0 < c₁ ≤ c₂ such that
c₁ · n^{3/2} ≤ f(n) ≤ c₂ · n^{3/2} for all large n.

The BFL result shows this up to sub-polynomial factors. The full conjecture
asks for a polynomial (constant-factor) bound. -/
def erdos_1155_conjecture : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
    ∀ᶠ (n : ℕ) in atTop,
      c₁ * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ triangleRemovalEdges n ∧
      triangleRemovalEdges n ≤ c₂ * (n : ℝ) ^ ((3 : ℝ) / 2)

-- ## Derived Results

/-- The BFL result implies the Grable bound (since 3/2 + ε' < 7/4 + ε
for appropriate choice of parameters). -/
theorem bfl_implies_grable :
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ (n : ℕ) in atTop,
        triangleRemovalEdges n ≤ (n : ℝ) ^ ((3 : ℝ) / 2 + ε)) →
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ (n : ℕ) in atTop,
        triangleRemovalEdges n ≤ (n : ℝ) ^ ((7 : ℝ) / 4 + ε)) := by
  intro h ε hε
  -- Use BFL with ε' = 1/4 + ε, since 3/2 + (1/4 + ε) = 7/4 + ε
  have hε' : (0 : ℝ) < 1/4 + ε := by linarith
  have h1 := h (1/4 + ε) hε'
  apply h1.mono
  intro n hn
  have : (3 : ℝ) / 2 + (1 / 4 + ε) = 7 / 4 + ε := by ring
  rw [this] at hn
  exact hn

/-- If the full conjecture holds, f(n) is Θ(n^{3/2}). -/
theorem conjecture_gives_theta :
    erdos_1155_conjecture →
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ᶠ (n : ℕ) in atTop,
        c₁ * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ triangleRemovalEdges n ∧
        triangleRemovalEdges n ≤ c₂ * (n : ℝ) ^ ((3 : ℝ) / 2) := by
  intro ⟨c₁, c₂, hc₁, hc₁c₂, h⟩
  exact ⟨c₁, c₂, hc₁, lt_of_lt_of_le hc₁ hc₁c₂, h⟩

/-- The BFL result shows f(n) = n^{3/2 + o(1)}, which we express as:
for every ε > 0, eventually n^{3/2 - ε} ≤ f(n) ≤ n^{3/2 + ε}. -/
theorem bfl_exponent_characterization :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ (n : ℕ) in atTop,
        (n : ℝ) ^ ((3 : ℝ) / 2 - ε) ≤ triangleRemovalEdges n ∧
        triangleRemovalEdges n ≤ (n : ℝ) ^ ((3 : ℝ) / 2 + ε) := by
  intro ε hε
  have hup := bfl_upper_bound ε hε
  have hlo := bfl_lower_bound ε hε
  exact hup.and hlo |>.mono (fun n ⟨hn_up, hn_lo⟩ => ⟨hn_lo, hn_up⟩)

-- ## Graph Theory Basics

/-- A triangle in a graph on vertex set V is a 3-clique. -/
def IsTriangle {V : Type*} (G : SimpleGraph V) (a b c : V) : Prop :=
  a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj a c

/-- A graph is triangle-free if it contains no triangles. -/
def IsTriangleFree' {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c : V, ¬IsTriangle G a b c

/-- Triangle-free is equivalent to CliqueFree 3 for simple graphs. -/
theorem triangleFree_iff_cliqueFree3 {V : Type*} [Fintype V] (G : SimpleGraph V) :
    IsTriangleFree' G ↔ G.CliqueFree 3 := by
  sorry

/-- The complete graph on n ≥ 3 vertices contains triangles. -/
theorem complete_has_triangles {n : ℕ} (hn : 3 ≤ n) :
    ¬IsTriangleFree' (⊤ : SimpleGraph (Fin n)) := by
  sorry

-- ## Mantel's Theorem (Triangle-Free Bound)
--
-- The triangle removal process terminates with a triangle-free graph.
-- By Mantel's theorem (Turán for r=3), a triangle-free graph on n vertices
-- has at most ⌊n²/4⌋ edges. This gives a trivial upper bound on f(n).

/-- **Mantel's theorem**: A triangle-free graph on n vertices has at most
⌊n²/4⌋ edges. -/
axiom mantel_theorem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    G.CliqueFree 3 →
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2)).card
      ≤ n ^ 2 / 4

/-- The Mantel bound gives a trivial upper bound: f(n) ≤ n²/4. -/
theorem trivial_upper_bound :
    ∀ᶠ (n : ℕ) in atTop,
      triangleRemovalEdges n ≤ (n : ℝ) ^ 2 / 4 := by
  -- The triangle removal process ends with a triangle-free graph,
  -- which by Mantel's theorem has at most n²/4 edges.
  sorry
