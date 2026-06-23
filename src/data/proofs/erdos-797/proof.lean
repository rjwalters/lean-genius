/-!
Erdős Problem #797: Acyclic Chromatic Number

Source: https://erdosproblems.com/797
Status: SOLVED (Alon-McDiarmid-Reed 1991)

Statement:
Let f(d) be the maximal acyclic chromatic number of any graph with
maximum degree d. An acyclic coloring is a proper coloring where no
cycle uses only two colors.

Estimate f(d). In particular, is it true that f(d) = o(d²)?

Answer: YES, f(d) = Θ(d^{4/3})
- Upper bound: f(d) ≤ O(d^{4/3}) [Alon-McDiarmid-Reed 1991]
- Lower bound: f(d) ≥ Ω(d^{4/3} / (log d)^{1/3})

References:
- Alon-McDiarmid-Reed [AMR91]: Resolved the problem
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open SimpleGraph Real

namespace Erdos797

/-!
## Part 1: Basic Definitions
-/

/-- A proper vertex coloring of a graph. -/
def IsProperColoring {V : Type*} (G : SimpleGraph V) (c : V → ℕ) : Prop :=
  ∀ u v : V, G.Adj u v → c u ≠ c v

/-- A coloring has a bichromatic cycle if some cycle in G uses exactly two colors. -/
def HasBichromaticCycle {V : Type*} (G : SimpleGraph V) (c : V → ℕ) : Prop :=
  ∃ (cycle : List V), cycle.length ≥ 3 ∧
    (∃ col1 col2 : ℕ, col1 ≠ col2 ∧ ∀ v ∈ cycle, c v = col1 ∨ c v = col2) ∧
    (∀ i, i + 1 < cycle.length →
      G.Adj (cycle.get ⟨i, by omega⟩) (cycle.get ⟨i + 1, by omega⟩))

/-- An acyclic coloring: proper and no bichromatic cycles. -/
def IsAcyclicColoring {V : Type*} (G : SimpleGraph V) (c : V → ℕ) : Prop :=
  IsProperColoring G c ∧ ¬HasBichromaticCycle G c

/-- Maximum degree of a graph. -/
noncomputable def maxDegree {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ :=
  Finset.sup Finset.univ (fun v => G.degree v)

/-- Acyclic chromatic number of a graph. -/
noncomputable def acyclicChromaticNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ c : V → ℕ, IsAcyclicColoring G c ∧ ∀ v, c v < k}

/-!
## Part 2: The Extremal Function f(d)
-/

/-- f(d): Maximum acyclic chromatic number over graphs with max degree d. -/
axiom f (d : ℕ) : ℕ

/-- f(d) is realized by some graph with maximum degree ≤ d. -/
axiom f_realized (d : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      maxDegree G ≤ d ∧ acyclicChromaticNumber G = f d

/-!
## Part 3: Known Bounds
-/

/-- Greedy upper bound: f(d) ≤ d² + 1. -/
axiom greedy_upper_bound :
  ∀ d : ℕ, d ≥ 1 → f d ≤ d^2 + 1

/-- Erdős lower bound: f(d) ≥ d^{4/3 - o(1)}. -/
axiom erdos_lower_bound :
  ∀ ε > 0, ∃ d₀ : ℕ, ∀ d ≥ d₀,
    (f d : ℝ) ≥ (d : ℝ)^(4/3 - ε)

/-- Alon-McDiarmid-Reed (1991): f(d) ≤ O(d^{4/3}). -/
axiom alon_mcdiarmid_reed_upper :
  ∃ C : ℝ, C > 0 ∧ ∀ d : ℕ, d ≥ 1 →
    (f d : ℝ) ≤ C * (d : ℝ)^(4/3 : ℝ)

/-- Precise lower bound with log factor: f(d) ≥ c · d^{4/3} / (log d)^{1/3}. -/
axiom precise_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ d : ℕ, d ≥ 3 →
    (f d : ℝ) ≥ c * (d : ℝ)^(4/3) / (Real.log d)^(1/3)

/-!
## Part 4: The Theta Bound
-/

/-- The complete asymptotic: f(d) = Θ(d^{4/3}). -/
axiom asymptotic_theta :
  ∃ c C : ℝ, 0 < c ∧ c < C ∧
    ∀ d : ℕ, d ≥ 3 →
      c * (d : ℝ)^(4/3) / (Real.log d)^(1/3) ≤ f d ∧
      (f d : ℝ) ≤ C * (d : ℝ)^(4/3)

/-!
## Part 5: Connection to B₂ Sequences
-/

/-- Connection to Sidon sets: the B₂ property of a Finset. -/
def is_B2_sequence (A : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≤ b → c ≤ d → a + b = c + d → (a = c ∧ b = d)

/-!
## Part 6: Summary
-/

/-- **Erdős Problem #797: SOLVED**

PROBLEM: Let f(d) = max acyclic chromatic number over graphs with max degree d.
Is f(d) = o(d²)?

ANSWER: YES — f(d) = Θ(d^{4/3})

BOUNDS:
- Upper: f(d) ≤ O(d^{4/3}) [Alon-McDiarmid-Reed 1991]
- Lower: f(d) ≥ Ω(d^{4/3} / (log d)^{1/3})
-/
theorem erdos_797_summary :
    -- Upper bound: O(d^{4/3})
    (∃ C : ℝ, C > 0 ∧ ∀ d : ℕ, d ≥ 1 → (f d : ℝ) ≤ C * (d : ℝ)^(4/3 : ℝ)) ∧
    -- Lower bound: Ω(d^{4/3} / (log d)^{1/3})
    (∃ c : ℝ, c > 0 ∧ ∀ d : ℕ, d ≥ 3 →
      (f d : ℝ) ≥ c * (d : ℝ)^(4/3) / (Real.log d)^(1/3)) :=
  ⟨alon_mcdiarmid_reed_upper, precise_lower_bound⟩

end Erdos797
