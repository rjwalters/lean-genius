/-
Erdős Problem #1104: Maximum Chromatic Number of Triangle-Free Graphs

**Statement**: Let f(n) be the maximum possible chromatic number of a
triangle-free graph on n vertices. Estimate f(n).

**Answer**: f(n) ≍ (n/log n)^(1/2)

**Known Bounds**:
  (1 - o(1)) · (n/log n)^(1/2) ≤ f(n) ≤ (2 + o(1)) · (n/log n)^(1/2)

- Upper bound: Davies-Illingworth (2022)
- Lower bound: Follows from Hefty-Horn-King-Pfender (2025) via R(3,k) connection

**Connection to R(3,k)**:
The asymptotic behavior of f(n) is determined by R(3,k) ~ k²/log k.
A triangle-free graph with chromatic number χ must have independence number < n/χ,
connecting chromatic numbers to Ramsey theory.

**Variant**: g(m) = max chromatic number with m edges
- Upper: g(m) ≤ (3^(5/3) + o(1)) · (m/(log m)²)^(1/3)  [Davies-Illingworth]
- Lower: g(m) ≫ (m/(log m)²)^(1/3)  [Kim 1995]

Reference: https://erdosproblems.com/1104
Related: Problem #165 (R(3,k) asymptotics)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

namespace Erdos1104

/-
## Part I: Basic Definitions
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph is triangle-free if it contains no K₃ subgraph. -/
def TriangleFree (G : SimpleGraph V) : Prop :=
  ∀ a b c : V, ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj a c)

/-- Alternative: No 3-cliques exist. -/
def TriangleFree' (G : SimpleGraph V) : Prop :=
  ¬G.CliqueFree 3 → False

/-- Triangle-free is equivalent to clique-free 3. -/
theorem triangleFree_iff_cliqueFree (G : SimpleGraph V) :
    TriangleFree G ↔ G.CliqueFree 3 := by
  sorry

/-- The chromatic number of a graph: minimum colors needed for proper vertex coloring.
    Axiomatized as full definition requires decidability machinery. -/
axiom chromaticNumber (G : SimpleGraph V) : ℕ

/-- A proper k-coloring assigns colors 0..k-1 such that adjacent vertices get different colors. -/
def HasProperColoring (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, ∀ v w : V, G.Adj v w → c v ≠ c w

/-- Chromatic number is the minimum k with a proper k-coloring. -/
axiom chromatic_is_minimum (G : SimpleGraph V) (k : ℕ) :
    chromaticNumber G = k ↔ HasProperColoring G k ∧ ∀ j < k, ¬HasProperColoring G j

/-- An independent set has no edges between its vertices. -/
def IsIndependent (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ x y : V, x ∈ S → y ∈ S → x ≠ y → ¬G.Adj x y

/-- The independence number α(G) is the size of the largest independent set. -/
noncomputable def independenceNumber (G : SimpleGraph V) : ℕ :=
  sSup {S.ncard | S : Set V, IsIndependent G S}

/-- Key observation: χ(G) ≥ |V|/α(G). -/
axiom chromatic_ge_vertex_over_alpha (G : SimpleGraph V) (n : ℕ) (hn : Fintype.card V = n) :
    chromaticNumber G * independenceNumber G ≥ n

/-
## Part II: The Function f(n)
-/

/-- f(n) = max chromatic number over all triangle-free graphs on n vertices. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {chromaticNumber G | G : SimpleGraph (Fin n), TriangleFree G}

/-- f is monotone: larger graphs can have larger chromatic numbers. -/
theorem f_monotone (m n : ℕ) (h : m ≤ n) : f m ≤ f n := by
  sorry

/-- Basic bound: f(n) ≤ n (trivial upper bound). -/
theorem f_le_n (n : ℕ) : f n ≤ n := by
  sorry

/-- f(n) ≥ 1 for n ≥ 1 (empty graph has χ = 1). -/
theorem f_ge_one (n : ℕ) (hn : n ≥ 1) : f n ≥ 1 := by
  sorry

/-
## Part III: Connection to Ramsey Numbers

The key insight: R(3,k) determines the behavior of f(n).
-/

/-- The Ramsey number R(3,k) from Erdős 165. -/
axiom R3 (k : ℕ) : ℕ

/-- R(3,k) definition: min N such that every triangle-free graph on N vertices
    has independence number at least k. -/
axiom R3_characterization (k : ℕ) (hk : k ≥ 1) :
    (∀ G : SimpleGraph (Fin (R3 k)), TriangleFree G → independenceNumber G ≥ k) ∧
    (∃ G : SimpleGraph (Fin (R3 k - 1)), TriangleFree G ∧ independenceNumber G < k)

/-- From Erdős #165: R(3,k) ≍ k²/log k. -/
axiom R3_asymptotic : ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
    (∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
      (c₁ - ε) * k^2 / log k ≤ R3 k ∧ (R3 k : ℝ) ≤ (c₂ + ε) * k^2 / log k)

/-- Current best constants: 1/2 ≤ c ≤ 1 (from Hefty et al. and Shearer). -/
axiom R3_best_constants :
    (∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ → (R3 k : ℝ) ≥ (1/2 - ε) * k^2 / log k) ∧
    (∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ → (R3 k : ℝ) ≤ (1 + ε) * k^2 / log k)

/-- Key lemma: If G is triangle-free on n vertices with χ(G) = χ, then α(G) ≥ n/χ.
    Therefore n < R(3, n/χ + 1), giving bounds on χ. -/
theorem chromatic_to_independence (G : SimpleGraph (Fin n)) (hG : TriangleFree G)
    (χ : ℕ) (hχ : chromaticNumber G = χ) (hpos : χ > 0) :
    independenceNumber G ≥ n / χ := by
  sorry

/-- Connection: f(n) can be characterized via R(3,k).
    f(n) = max{χ : n < R(3, ⌈n/χ⌉ + 1)} approximately. -/
theorem f_via_R3 (n : ℕ) (hn : n ≥ 2) :
    ∀ χ : ℕ, (χ : ℝ) ≤ Real.sqrt (n / log n) → f n ≥ χ := by
  sorry

/-
## Part IV: Upper Bounds
-/

/--
**Davies-Illingworth Theorem (2022)**:
f(n) ≤ (2 + o(1)) · √(n / log n)

This improves upon earlier bounds and uses sophisticated probabilistic arguments.
-/
axiom davies_illingworth_upper :
    ∀ ε > 0, ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      (f n : ℝ) ≤ (2 + ε) * Real.sqrt (n / log n)

/-- The upper bound follows from independence number lower bounds in triangle-free graphs. -/
axiom independence_lower_bound_triangleFree :
    ∀ ε > 0, ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ G : SimpleGraph (Fin n),
      TriangleFree G →
      (independenceNumber G : ℝ) ≥ ((1/2) - ε) * Real.sqrt (n * log n)

/-
## Part V: Lower Bounds
-/

/--
**Lower bound via R(3,k)**:
f(n) ≥ (1 - o(1)) · √(n / log n)

This follows from the Ramsey lower bound R(3,k) ≥ (1/2 - o(1)) · k²/log k.
-/
axiom hhkp_lower_via_R3 :
    ∀ ε > 0, ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      (f n : ℝ) ≥ (1 - ε) * Real.sqrt (n / log n)

/--
Construction sketch:
Take a Ramsey graph G on N = R(3,k) - 1 vertices that is triangle-free
with independence number < k. Its chromatic number satisfies χ(G) ≥ N/k.
With N ≈ k²/log k, we get χ ≥ k/log k.
Setting k ≈ √(n log n) gives χ ≈ √(n/log n).
-/
axiom construction_via_ramsey (n : ℕ) (hn : n ≥ 3) :
    ∃ G : SimpleGraph (Fin n), TriangleFree G ∧
      (chromaticNumber G : ℝ) ≥ (1/2) * Real.sqrt (n / log n)

/-
## Part VI: The Main Asymptotic Result
-/

/--
**Erdős Problem #1104: SOLVED (asymptotic order)**
f(n) ≍ √(n / log n)

Best bounds: (1 - o(1))·√(n/log n) ≤ f(n) ≤ (2 + o(1))·√(n/log n)
The exact constant (between 1 and 2) remains open.
-/
theorem erdos_1104_main :
    (∀ ε > 0, ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → (f n : ℝ) ≥ (1 - ε) * sqrt (n / log n)) ∧
    (∀ ε > 0, ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → (f n : ℝ) ≤ (2 + ε) * sqrt (n / log n)) := by
  exact ⟨hhkp_lower_via_R3, davies_illingworth_upper⟩

/-- The asymptotic order is determined. -/
theorem f_asymptotic_order :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ n : ℕ, n ≥ 3 → c₁ * sqrt (n / log n) ≤ f n ∧ (f n : ℝ) ≤ c₂ * sqrt (n / log n) := by
  use 1/2, 3
  constructor; norm_num
  constructor; norm_num
  intro n _
  constructor
  · sorry  -- From construction_via_ramsey
  · sorry  -- From trivial bound + Davies-Illingworth

/-
## Part VII: The Edge-Count Variant
-/

/-- g(m) = max chromatic number of triangle-free graph with m edges. -/
noncomputable def g (m : ℕ) : ℕ :=
  sSup {chromaticNumber G | G : SimpleGraph V, TriangleFree G ∧
        (G.edgeFinset).card = m}

/--
**Davies-Illingworth (2022)**: Upper bound for g(m).
g(m) ≤ (3^(5/3) + o(1)) · (m / (log m)²)^(1/3)
-/
axiom davies_illingworth_edge_upper :
    ∀ ε > 0, ∃ m₀ : ℕ, ∀ m : ℕ, m ≥ m₀ →
      (g m : ℝ) ≤ ((3 : ℝ)^(5/3 : ℝ) + ε) * (m / (log m)^2)^(1/3 : ℝ)

/--
**Kim (1995)**: Lower bound for g(m).
g(m) ≫ (m / (log m)²)^(1/3)
-/
axiom kim_edge_lower :
    ∃ c > 0, ∀ m : ℕ, m ≥ 3 → (g m : ℝ) ≥ c * (m / (log m)^2)^(1/3 : ℝ)

/-- The edge-count variant has asymptotic order (m / (log m)²)^(1/3). -/
theorem g_asymptotic_order :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ m : ℕ, m ≥ 3 → c₁ * (m / (log m)^2)^(1/3 : ℝ) ≤ g m ∧
                        (g m : ℝ) ≤ c₂ * (m / (log m)^2)^(1/3 : ℝ) := by
  sorry

/-
## Part VIII: Open Questions
-/

/-- Open: What is the exact constant c such that f(n) ~ c · √(n/log n)? -/
def exact_constant_conjecture : Prop :=
    ∃ c : ℝ, c > 0 ∧ ∀ ε > 0, ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      (c - ε) * sqrt (n / log n) ≤ f n ∧ (f n : ℝ) ≤ (c + ε) * sqrt (n / log n)

/-- The gap between upper (2) and lower (1) constants is the main open question.
    This is related to determining the exact constant in R(3,k). -/
axiom gap_relates_to_R3 :
    exact_constant_conjecture ↔
      ∃ c : ℝ, c > 0 ∧ ∀ ε > 0, ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
        (c - ε) * k^2 / log k ≤ R3 k ∧ (R3 k : ℝ) ≤ (c + ε) * k^2 / log k

/-
## Summary

**Erdős Problem #1104**: SOLVED (asymptotic order)

- f(n) ≍ √(n / log n)
- Best bounds: (1 - o(1))·√(n/log n) ≤ f(n) ≤ (2 + o(1))·√(n/log n)
- Upper bound: Davies-Illingworth (2022)
- Lower bound: Hefty-Horn-King-Pfender (2025) via R(3,k)

**Open**: Determine the exact constant (currently known to be between 1 and 2).
-/

end Erdos1104
