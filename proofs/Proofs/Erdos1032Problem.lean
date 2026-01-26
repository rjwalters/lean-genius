/-!
# Erdős Problem #1032 — 4-Chromatic Critical Graphs with High Minimum Degree

Do there exist 4-chromatic critical graphs on n vertices with minimum
degree ≫ n (i.e., linear in n)?

A graph G is k-chromatic critical if χ(G) = k and removing any edge
reduces the chromatic number to k − 1.

## Known constructions

- Dirac: 6-chromatic critical graphs with δ > n/2
- Simonovits and Toft: 4-chromatic critical graphs with δ ≫ n^{1/3}

## Related conjecture (Toft)

Every 4-chromatic critical graph on n vertices has ≥ (5/3 + o(1))n edges.

Reference: https://erdosproblems.com/1032
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

/-! ## Graph properties (axiomatised) -/

/-- The number of vertices of a graph. -/
axiom vertexCount : Type → ℕ

/-- The minimum degree of a graph. -/
axiom minDegree : Type → ℕ

/-- The chromatic number of a graph. -/
axiom chromaticNumber : Type → ℕ

/-- The number of edges of a graph. -/
axiom edgeCount : Type → ℕ

/-- A graph is k-chromatic critical if χ(G) = k and removing any edge
    reduces the chromatic number. -/
def IsKChromaticCritical (G : Type) (k : ℕ) : Prop :=
    chromaticNumber G = k ∧
    ∀ e : ℕ, e < edgeCount G →
      chromaticNumber G - 1 ≤ k - 1

/-! ## Known constructions -/

/-- Dirac: there exist 6-chromatic critical graphs with δ > n/2. -/
axiom dirac_6_critical :
    ∀ N : ℕ, ∃ (G : Type),
      vertexCount G = N ∧ IsKChromaticCritical G 6 ∧
      N / 2 < minDegree G

/-- Simonovits–Toft: there exist 4-chromatic critical graphs with
    δ ≫ n^{1/3}. -/
axiom simonovits_toft_4_critical :
    ∃ c : ℚ, 0 < c ∧ ∀ N : ℕ, ∃ (G : Type),
      vertexCount G = N ∧ IsKChromaticCritical G 4 ∧
      c * (N : ℚ) ^ ((1 : ℚ) / 3) ≤ (minDegree G : ℚ)

/-! ## Toft's conjecture -/

/-- Toft: every 4-chromatic critical graph on n vertices has
    ≥ (5/3 + o(1))n edges. -/
def ToftConjecture : Prop :=
    ∀ ε : ℚ, 0 < ε → ∃ n₀ : ℕ, ∀ (G : Type),
      n₀ ≤ vertexCount G → IsKChromaticCritical G 4 →
        (5 / 3 - ε) * (vertexCount G : ℚ) ≤ (edgeCount G : ℚ)

/-! ## Main conjecture -/

/-- Erdős Problem 1032: there exist 4-chromatic critical graphs on
    n vertices with minimum degree linear in n.
    Formally: ∃ c > 0 such that for all N, there exists a 4-chromatic
    critical graph on N vertices with δ ≥ c·N. -/
def ErdosProblem1032 : Prop :=
    ∃ c : ℚ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N → ∃ (G : Type),
      vertexCount G = N ∧ IsKChromaticCritical G 4 ∧
      c * (N : ℚ) ≤ (minDegree G : ℚ)

/-- Extended question for 5-chromatic critical graphs. -/
def ErdosProblem1032_k5 : Prop :=
    ∃ c : ℚ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N → ∃ (G : Type),
      vertexCount G = N ∧ IsKChromaticCritical G 5 ∧
      c * (N : ℚ) ≤ (minDegree G : ℚ)
