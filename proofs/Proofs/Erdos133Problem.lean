/-
Erdős Problem #133: Maximum Degree in Triangle-Free Diameter-2 Graphs

Source: https://erdosproblems.com/133
Status: SOLVED (DISPROVED - f(n)/√n does not tend to ∞)

Statement:
Let f(n) be minimal such that every triangle-free graph G with n vertices
and diameter 2 contains a vertex with degree ≥ f(n).

What is the order of growth of f(n)? Does f(n)/√n → ∞?

Answer: NO - f(n) ~ √n (Alon conjectures f(n) ~ √n exactly)

Known Results:
- Lower bound: f(n) ≥ (1-o(1))√n (from d² + 1 vertex bound)
- Upper bounds:
  * Simonovits: f(n) ≤ n^0.7182...
  * Alon: f(n) ≪ √(n log n)
  * Hanson-Seyffarth (1984): f(n) ≤ (√2 + o(1))√n
  * Füredi-Seress (1994): f(n) ≤ (2/√3 + o(1))√n

References:
- [Er97b] Erdős
- [HaSe84] Hanson-Seyffarth
- [FuSe94] Füredi-Seress

Tags: graph-theory, extremal-combinatorics, diameter, triangle-free
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

namespace Erdos133

open SimpleGraph

/- ## Part 1: Basic Definitions -/

/-- Triangle-free graph: no three mutually adjacent vertices -/
def TriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c : V, G.Adj a b → G.Adj b c → G.Adj c a → False

/-- Graph has diameter exactly 2: any two vertices are at distance ≤ 2 -/
def HasDiameter2 {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  G.Connected ∧
  ∀ u v : V, u ≠ v → G.Adj u v ∨ ∃ w : V, G.Adj u w ∧ G.Adj w v

/-- Maximum degree of a graph -/
noncomputable def maxDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.sup Finset.univ (fun v => G.degree v)

/- ## Part 2: The Function f(n) -/

/-- f(n) = minimum k such that every triangle-free diameter-2 graph on n vertices
    has a vertex of degree ≥ k -/
noncomputable def f (n : ℕ) : ℕ :=
  Nat.find (⟨1, by trivial⟩ : ∃ k : ℕ, ∀ V : Type*, ∀ _ : Fintype V,
    Fintype.card V = n → ∀ G : SimpleGraph V, [DecidableEq V] → [DecidableRel G.Adj] →
    TriangleFree G → HasDiameter2 G → ∃ v : V, G.degree v ≥ k)

/- ## Part 3: The Moore Bound (Lower Bound) -/

/-- The asymptotic lower bound: f(n) ≥ (1 - o(1))√n -/
axiom lower_bound_asymptotic :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀, (f n : ℝ) ≥ (1 - ε) * Real.sqrt n

/- ## Part 4: Upper Bound Constructions -/

/-- Füredi-Seress (1994), the current best upper bound:
    f(n) ≤ (2/√3 + o(1))√n ≈ 1.1547√n -/
axiom furedi_seress_1994 :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (f n : ℝ) ≤ (2 / Real.sqrt 3 + ε) * Real.sqrt n

/- ## Part 5: The Main Question (DISPROVED) -/

/-- The original question: Does f(n)/√n → ∞? -/
def OriginalQuestion : Prop :=
  Filter.Tendsto (fun n => (f n : ℝ) / Real.sqrt n) Filter.atTop Filter.atTop

/-- Answer: NO - disproved by the Füredi-Seress upper bound showing f(n)/√n is bounded -/
axiom original_question_false : ¬OriginalQuestion

/- ## Part 6: Alon's Conjecture -/

/-- Alon's conjecture: f(n)/√n → 1, i.e., f(n) ~ √n exactly -/
def AlonConjecture : Prop :=
  Filter.Tendsto (fun n => (f n : ℝ) / Real.sqrt n) Filter.atTop (nhds 1)

/- ## Part 7: Polarity Graph Constructions -/

/- ## Part 8: Complete Resolution -/

/-- Erdős Problem #133: Complete resolution combining all bounds.
    1. The original question f(n)/√n → ∞ is DISPROVED
    2. Lower bound: f(n) ≥ (1-o(1))√n (from Moore bound)
    3. Upper bound: f(n) ≤ (2/√3+o(1))√n (Füredi-Seress 1994)
    Therefore f(n) = Θ(√n). -/
theorem erdos_133 :
    ¬OriginalQuestion ∧
    (∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀, (f n : ℝ) ≥ (1 - ε) * Real.sqrt n) ∧
    (∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀, (f n : ℝ) ≤ (2 / Real.sqrt 3 + ε) * Real.sqrt n) := by
  refine ⟨original_question_false, lower_bound_asymptotic, furedi_seress_1994⟩

end Erdos133
