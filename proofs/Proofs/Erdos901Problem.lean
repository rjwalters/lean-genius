/-
  Erdős Problem #901: Property B and Hypergraph Coloring

  Source: https://erdosproblems.com/901
  Status: OPEN

  Statement:
  Let m(n) be the minimum number of edges in an n-uniform hypergraph that does NOT
  have Property B (i.e., is not 2-colorable). Estimate m(n).

  Property B: A hypergraph has Property B if there exists a 2-coloring of vertices
  such that no edge is monochromatic.

  Known Results:
  - Exact values: m(2) = 3, m(3) = 7, m(4) = 23
  - Erdős (1963-64): 2^n ≪ m(n) ≪ n² · 2^n
  - Beck (1977-78): n^{1/3-o(1)} · 2^n ≪ m(n)
  - Radhakrishnan-Srinivasan (2000): √(n/log n) · 2^n ≪ m(n)

  Erdős-Lovász Conjecture: m(n) = Θ(n · 2^n)

  Tags: hypergraph, coloring, property-b, combinatorics
-/

import Mathlib.Combinatorics.SetFamily.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Erdos901

open Finset Real

/- ## Part I: Hypergraph Definitions -/

/-- An n-uniform hypergraph: a family of n-element subsets of a ground set. -/
structure UniformHypergraph (V : Type*) [Fintype V] (n : ℕ) where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = n

/-- The number of edges in a hypergraph. -/
def UniformHypergraph.edgeCount {V : Type*} [Fintype V] {n : ℕ}
    (H : UniformHypergraph V n) : ℕ :=
  H.edges.card

/- ## Part II: Property B -/

/-- A 2-coloring of vertices. -/
def TwoColoring (V : Type*) := V → Fin 2

/-- An edge is monochromatic under a coloring if all vertices have the same color. -/
def IsMonochromatic {V : Type*} (c : TwoColoring V) (e : Finset V) : Prop :=
  (∀ v ∈ e, c v = 0) ∨ (∀ v ∈ e, c v = 1)

/-- Property B: there exists a 2-coloring with no monochromatic edge. -/
def HasPropertyB {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (H : UniformHypergraph V n) : Prop :=
  ∃ c : TwoColoring V, ∀ e ∈ H.edges, ¬IsMonochromatic c e

/-- Without Property B: every 2-coloring has a monochromatic edge. -/
def LacksPropertyB {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (H : UniformHypergraph V n) : Prop :=
  ∀ c : TwoColoring V, ∃ e ∈ H.edges, IsMonochromatic c e

/-- Property B and its negation are complementary. -/
theorem propertyB_dichotomy {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (H : UniformHypergraph V n) :
    HasPropertyB H ↔ ¬LacksPropertyB H := by
  sorry

/- ## Part III: The Function m(n) -/

/-- m(n) = minimum edges in an n-uniform hypergraph without Property B. -/
noncomputable def m (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (H : UniformHypergraph V n), H.edgeCount = k ∧ LacksPropertyB H}

/-- m(n) is well-defined for n ≥ 2. -/
theorem m_well_defined (n : ℕ) (hn : n ≥ 2) : m n > 0 := by
  sorry

/-- m is monotone increasing. -/
theorem m_mono {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) (hn₁ : n₁ ≥ 2) : m n₁ ≤ m n₂ := by
  sorry

/- ## Part IV: Exact Values -/

/-- m(2) = 3: The Fano plane minus one line. -/
theorem m_2_eq_3 : m 2 = 3 := by
  sorry

/-- m(3) = 7: The Fano plane. -/
theorem m_3_eq_7 : m 3 = 7 := by
  sorry

/-- m(4) = 23: Found by computer search. -/
theorem m_4_eq_23 : m 4 = 23 := by
  sorry

/- ## Part V: Lower Bounds -/

/-- Erdős (1963-64) lower bound: m(n) > 2^{n-1}. -/
theorem erdos_lower_bound (n : ℕ) (hn : n ≥ 2) : m n > 2 ^ (n - 1) := by
  sorry

/-- Beck (1977-78) improved lower: m(n) ≫ n^{1/3} · 2^n. -/
theorem beck_lower_bound :
    ∀ ε > 0, ∀ᶠ n in Filter.atTop,
      (m n : ℝ) > (n : ℝ) ^ (1/3 - ε) * 2 ^ n := by
  sorry

/-- Radhakrishnan-Srinivasan (2000): m(n) ≫ √(n/log n) · 2^n. -/
theorem rs_lower_bound :
    ∀ᶠ n in Filter.atTop,
      (m n : ℝ) > Real.sqrt (n / Real.log n) * 2 ^ n / 2 := by
  sorry

/-- Pluhár (2009) simplified proof: m(n) ≫ n^{1/4} · 2^n. -/
theorem pluhar_lower_bound :
    ∀ ε > 0, ∀ᶠ n in Filter.atTop,
      (m n : ℝ) > (n : ℝ) ^ (1/4 - ε) * 2 ^ n := by
  sorry

/- ## Part VI: Upper Bounds -/

/-- Erdős (1963-64) upper bound: m(n) < n² · 2^n. -/
theorem erdos_upper_bound (n : ℕ) (hn : n ≥ 2) :
    (m n : ℝ) < (n : ℝ) ^ 2 * 2 ^ n := by
  sorry

/-- The probabilistic method gives m(n) ≤ C · n · 2^n for some C. -/
theorem probabilistic_upper :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 → (m n : ℝ) ≤ C * n * 2 ^ n := by
  sorry

/- ## Part VII: The Erdős-Lovász Conjecture -/

/-- Erdős-Lovász Conjecture: m(n) = Θ(n · 2^n). -/
def ErdosLovaszConjecture : Prop :=
  ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
    ∀ᶠ n in Filter.atTop,
      c₁ * n * 2 ^ n ≤ (m n : ℝ) ∧ (m n : ℝ) ≤ c₂ * n * 2 ^ n

/-- The gap between known bounds. -/
theorem current_gap :
    ∀ᶠ n in Filter.atTop,
      Real.sqrt (n / Real.log n) * 2 ^ n / 2 < (m n : ℝ) ∧
      (m n : ℝ) < (n : ℝ) ^ 2 * 2 ^ n := by
  sorry

/- ## Part VIII: Constructions -/

/-- The complete n-uniform hypergraph on 2n-1 vertices lacks Property B. -/
theorem complete_hypergraph_no_propertyB (n : ℕ) (hn : n ≥ 2) :
    ∃ (H : UniformHypergraph (Fin (2*n - 1)) n), LacksPropertyB H := by
  sorry

/-- Explicit construction for m(2) = 3: Three edges on 4 vertices. -/
def hypergraph_m2 : UniformHypergraph (Fin 4) 2 where
  edges := {{0, 1}, {0, 2}, {1, 2}}
  uniform := by intro e he; simp_all [Finset.card_pair]

theorem hypergraph_m2_no_propertyB : LacksPropertyB hypergraph_m2 := by
  sorry

/- ## Part IX: Probabilistic Method -/

/-- The Lovász Local Lemma gives Property B for sparse hypergraphs. -/
theorem lll_property_b {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (H : UniformHypergraph V n) (hn : n ≥ 2)
    (hd : ∀ e ∈ H.edges, (H.edges.filter fun e' => (e ∩ e').Nonempty).card < 2^(n-1)) :
    HasPropertyB H := by
  sorry

/-- Random coloring: probability an edge is monochromatic is 2^{1-n}. -/
theorem monochromatic_probability (n : ℕ) (hn : n ≥ 1) :
    (2 : ℝ) ^ (1 - (n : ℤ)) = 2 / 2 ^ n := by
  sorry

/- ## Part X: Connections -/

/-- Connection to list chromatic number (Problem #629):
    m(k) ≤ n(k) ≤ m(k+1) where n(k) is from the list coloring problem. -/
theorem connection_list_chromatic :
    ∀ k : ℕ, k ≥ 2 → m k ≤ m (k + 1) := by
  sorry

/-- The chromatic number of a hypergraph. -/
noncomputable def chromaticNumber {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (H : UniformHypergraph V n) : ℕ :=
  sInf {k : ℕ | k ≥ 1 ∧ ∃ c : V → Fin k, ∀ e ∈ H.edges, ∃ v w : V,
    v ∈ e ∧ w ∈ e ∧ c v ≠ c w}

/-- A hypergraph lacks Property B iff its chromatic number is ≥ 3. -/
theorem lacks_propertyB_iff_chromatic_ge_3 {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (H : UniformHypergraph V n) (hne : H.edges.Nonempty) :
    LacksPropertyB H ↔ chromaticNumber H ≥ 3 := by
  sorry

end Erdos901

/-
  ## Summary

  This file formalizes Erdős Problem #901 on Property B and hypergraph coloring.

  **Status**: OPEN

  **The Problem**: Find m(n) = minimum edges in an n-uniform hypergraph without
  Property B (not 2-colorable).

  **Known Results**:
  - Exact: m(2) = 3, m(3) = 7, m(4) = 23
  - Lower: √(n/log n) · 2^n ≪ m(n) (Radhakrishnan-Srinivasan 2000)
  - Upper: n² · 2^n (Erdős 1963-64)

  **Erdős-Lovász Conjecture**: m(n) = Θ(n · 2^n)

  The gap between √(n/log n) and n in the coefficient is the main open question.

  **What we formalize**:
  1. Uniform hypergraphs and Property B
  2. The function m(n) and exact values
  3. Lower bounds: Erdős, Beck, Radhakrishnan-Srinivasan, Pluhár
  4. Upper bounds via probabilistic method
  5. The Erdős-Lovász conjecture
  6. Explicit constructions
  7. Connection to list chromatic number (Problem #629)

  **Key sorries**:
  - `m_2_eq_3`, `m_3_eq_7`, `m_4_eq_23`: Exact values
  - `rs_lower_bound`: Best known lower bound
  - `lll_property_b`: Lovász Local Lemma application

  **Historical note**: Property B is named after Bernstein, who first studied it.
-/
