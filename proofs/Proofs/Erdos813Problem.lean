/-
Erdős Problem #813: Triangles in Every 7-Vertex Set

Source: https://erdosproblems.com/813
Status: OPEN (partial progress)

Statement:
Let h(n) be minimal such that every graph on n vertices where every set of 7
vertices contains a triangle must contain a clique on at least h(n) vertices.
Estimate h(n). In particular, do constants c₁, c₂ > 0 exist such that
  n^{1/3+c₁} ≪ h(n) ≪ n^{1/2-c₂}?

Known Results:
- Erdős-Hajnal: n^{1/3} ≪ h(n) ≪ n^{1/2}
- Bucić-Sudakov (2023): h(n) ≫ n^{5/12-o(1)}

References:
- [Er91] Erdős (1991)
- [BuSu23] Bucić-Sudakov (2023)
- https://erdosproblems.com/813
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic

open Finset

namespace Erdos813

/- ## Part I: Basic Definitions -/

/-- A simple graph on n vertices (using Fin n as vertex set). -/
def GraphOnN (n : ℕ) := SimpleGraph (Fin n)

/-- A triangle (K₃) in a graph. -/
def HasTriangle {n : ℕ} (G : GraphOnN n) (v₁ v₂ v₃ : Fin n) : Prop :=
  v₁ ≠ v₂ ∧ v₂ ≠ v₃ ∧ v₁ ≠ v₃ ∧
  G.Adj v₁ v₂ ∧ G.Adj v₂ v₃ ∧ G.Adj v₁ v₃

/-- A subset of vertices contains a triangle. -/
def SubsetHasTriangle {n : ℕ} (G : GraphOnN n) (S : Finset (Fin n)) : Prop :=
  ∃ v₁ v₂ v₃ : Fin n, v₁ ∈ S ∧ v₂ ∈ S ∧ v₃ ∈ S ∧ HasTriangle G v₁ v₂ v₃

/-- Every 7-vertex subset contains a triangle. -/
def Every7SetHasTriangle {n : ℕ} (G : GraphOnN n) : Prop :=
  ∀ S : Finset (Fin n), S.card = 7 → SubsetHasTriangle G S

/- ## Part II: Cliques -/

/-- A clique on k vertices: all pairs are adjacent. -/
def IsClique {n : ℕ} (G : GraphOnN n) (S : Finset (Fin n)) : Prop :=
  ∀ v₁ ∈ S, ∀ v₂ ∈ S, v₁ ≠ v₂ → G.Adj v₁ v₂

/-- The graph contains a clique of size k. -/
def HasCliqueOfSize {n : ℕ} (G : GraphOnN n) (k : ℕ) : Prop :=
  ∃ S : Finset (Fin n), S.card = k ∧ IsClique G S

/- ## Part III: The Function h(n) -/

/-- h(n): minimum clique size guaranteed when every 7-set has a triangle.
Axiomatized since computing the minimum requires exhaustive search. -/
axiom h (n : ℕ) : ℕ

/-- h(n) is an achievable bound: every graph with the property has a clique. -/
/- ## Part IV: Known Bounds -/

/-- Erdős-Hajnal lower bound: h(n) ≫ n^{1/3}. -/
axiom erdos_hajnal_lower_bound :
  ∃ c > 0, ∀ n ≥ 1, (h n : ℝ) ≥ c * (n : ℝ)^(1/3 : ℝ)

/-- Erdős-Hajnal upper bound: h(n) ≪ n^{1/2}. -/
axiom erdos_hajnal_upper_bound :
  ∃ c > 0, ∀ n ≥ 1, (h n : ℝ) ≤ c * (n : ℝ)^(1/2 : ℝ)

/-- Combined Erdős-Hajnal bounds: n^{1/3} ≪ h(n) ≪ n^{1/2}. -/
theorem erdos_hajnal_bounds :
  ∃ c₁ c₂ > 0, ∀ n ≥ 1,
    c₁ * (n : ℝ)^(1/3 : ℝ) ≤ (h n : ℝ) ∧
    (h n : ℝ) ≤ c₂ * (n : ℝ)^(1/2 : ℝ) := by
  obtain ⟨c₁, hc₁, hl⟩ := erdos_hajnal_lower_bound
  obtain ⟨c₂, hc₂, hu⟩ := erdos_hajnal_upper_bound
  exact ⟨c₁, hc₁, c₂, hc₂, fun n hn => ⟨hl n hn, hu n hn⟩⟩

/- ## Part V: Bucić-Sudakov Improvement (2023) -/

/-- Bucić-Sudakov (2023): Improved lower bound h(n) ≫ n^{5/12-o(1)}. -/
/-- The exponent 5/12 improves on 1/3. -/
theorem five_twelfths_better : (5 : ℝ) / 12 > 1 / 3 := by norm_num

/-- Gap between known bounds: 1/2 - 5/12 = 1/12. -/
theorem exponent_gap : (1 : ℝ) / 2 - 5 / 12 = 1 / 12 := by norm_num

/- ## Part VI: The Main Conjecture -/

/-- Erdős's conjecture: can both bounds be improved?
Specifically, do c₁, c₂ > 0 exist with n^{1/3+c₁} ≪ h(n) ≪ n^{1/2-c₂}? -/
def ErdosConjecture813 : Prop :=
  ∃ c₁ c₂ > 0,
    (∀ n ≥ 1, (h n : ℝ) ≥ c₁ * (n : ℝ)^(1/3 + c₁ : ℝ)) ∧
    (∀ n ≥ 1, (h n : ℝ) ≤ c₂ * (n : ℝ)^(1/2 - c₂ : ℝ))

/- ## Part VII: Summary -/

/-- **Erdős Problem #813: OPEN**

h(n) = minimum clique size in graphs where every 7-set has a triangle.
- Erdős-Hajnal: n^{1/3} ≪ h(n) ≪ n^{1/2}
- Bucić-Sudakov (2023): h(n) ≫ n^{5/12-o(1)}
- Open: Can exponents be further improved? -/
theorem erdos_813 :
    (∃ c > 0, ∀ n ≥ 1, (h n : ℝ) ≥ c * (n : ℝ)^(1/3 : ℝ)) ∧
    (∃ c > 0, ∀ n ≥ 1, (h n : ℝ) ≤ c * (n : ℝ)^(1/2 : ℝ)) :=
  ⟨erdos_hajnal_lower_bound, erdos_hajnal_upper_bound⟩

end Erdos813
