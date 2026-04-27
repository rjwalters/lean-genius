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

/-- **Mantel bound for triangle removal**: The triangle removal process ends
with a triangle-free graph. By Mantel's theorem, any triangle-free graph on
n vertices has at most ⌊n²/4⌋ edges. Therefore f(n) ≤ n²/4 for all n. -/
axiom triangleRemoval_mantel_bound (n : ℕ) :
    triangleRemovalEdges n ≤ (n : ℝ) ^ 2 / 4

/-- The triangle removal process on K_n starts with C(n,2) edges and can only
remove edges, so f(n) ≤ n(n-1)/2 ≤ n²/2. Now derived from the tighter
Mantel bound (n²/4 ≤ n²/2). Originally axiomatized; now a theorem. -/
theorem triangleRemovalEdges_le_complete (n : ℕ) :
    triangleRemovalEdges n ≤ (n : ℝ) ^ 2 / 2 := by
  have h_mantel := triangleRemoval_mantel_bound n
  have h_sq : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
  linarith

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

/-- **Grable (1997)**: For every ε > 0, the number of remaining edges
satisfies f(n) ≤ n^{7/4 + ε} asymptotically (in probability).
This follows directly from the stronger BFL bound (3/2 + ε' implies 7/4 + ε
with ε' = 1/4 + ε). Originally axiomatized; now proved from BFL. -/
theorem grable_upper_bound :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ (n : ℕ) in atTop,
        triangleRemovalEdges n ≤ (n : ℝ) ^ ((7 : ℝ) / 4 + ε) := by
  intro ε hε
  have hε' : (0 : ℝ) < 1/4 + ε := by linarith
  have h1 := bfl_upper_bound (1/4 + ε) hε'
  apply h1.mono
  intro n hn
  have : (3 : ℝ) / 2 + (1 / 4 + ε) = 7 / 4 + ε := by ring
  rw [this] at hn
  exact hn

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
theorem triangleFree_iff_cliqueFree3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : IsTriangleFree' G ↔ G.CliqueFree 3 := by
  constructor
  · -- IsTriangleFree' → CliqueFree 3
    intro htf s hs
    obtain ⟨hclique, hcard⟩ := hs
    rw [Finset.card_eq_three] at hcard
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := hcard
    have mem_a : a ∈ (↑({a, b, c} : Finset V) : Set V) := by simp
    have mem_b : b ∈ (↑({a, b, c} : Finset V) : Set V) := by simp
    have mem_c : c ∈ (↑({a, b, c} : Finset V) : Set V) := by simp
    exact htf a b c ⟨hab, hbc, hac,
      hclique mem_a mem_b hab,
      hclique mem_b mem_c hbc,
      hclique mem_a mem_c hac⟩
  · -- CliqueFree 3 → IsTriangleFree'
    intro hcf a b c ⟨hab, hbc, hac, hadj_ab, hadj_bc, hadj_ac⟩
    apply hcf {a, b, c}
    refine ⟨?_, by rw [Finset.card_eq_three]; exact ⟨a, b, c, hab, hac, hbc, rfl⟩⟩
    intro x hx y hy hxy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
               Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact absurd rfl hxy | exact hadj_ab | exact hadj_ac |
              exact hadj_bc | exact G.symm hadj_ab | exact G.symm hadj_ac |
              exact G.symm hadj_bc

/-- The complete graph on n ≥ 3 vertices contains triangles. -/
theorem complete_has_triangles {n : ℕ} (hn : 3 ≤ n) :
    ¬IsTriangleFree' (⊤ : SimpleGraph (Fin n)) := by
  intro h
  let v0 : Fin n := ⟨0, by omega⟩
  let v1 : Fin n := ⟨1, by omega⟩
  let v2 : Fin n := ⟨2, by omega⟩
  have h01 : v0 ≠ v1 := by intro heq; simp [v0, v1] at heq
  have h12 : v1 ≠ v2 := by intro heq; simp [v1, v2] at heq
  have h02 : v0 ≠ v2 := by intro heq; simp [v0, v2] at heq
  have adj01 : (⊤ : SimpleGraph (Fin n)).Adj v0 v1 := by
    simp only [SimpleGraph.top_adj]; exact h01
  have adj12 : (⊤ : SimpleGraph (Fin n)).Adj v1 v2 := by
    simp only [SimpleGraph.top_adj]; exact h12
  have adj02 : (⊤ : SimpleGraph (Fin n)).Adj v0 v2 := by
    simp only [SimpleGraph.top_adj]; exact h02
  exact h v0 v1 v2 ⟨h01, h12, h02, adj01, adj12, adj02⟩

-- ## Mantel's Theorem (Triangle-Free Bound)
--
-- The triangle removal process terminates with a triangle-free graph.
-- By Mantel's theorem (Turán for r=3), a triangle-free graph on n vertices
-- has at most ⌊n²/4⌋ edges. This gives a universal upper bound on f(n).
-- The Mantel bound axiom is now declared at the top of the file alongside
-- other process axioms; the weaker n²/2 bound is derived from it.

/-- The Mantel bound as an eventually-true statement (for comparison with BFL). -/
theorem trivial_upper_bound :
    ∀ᶠ (n : ℕ) in atTop,
      triangleRemovalEdges n ≤ (n : ℝ) ^ 2 / 4 :=
  Filter.eventually_atTop.mpr ⟨0, fun n _ => triangleRemoval_mantel_bound n⟩
