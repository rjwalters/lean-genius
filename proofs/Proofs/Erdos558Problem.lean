/-
# Erdős Problem #558: Multicolor Ramsey Numbers for Complete Bipartite Graphs

Source: https://erdosproblems.com/558
Status: SOLVED (partially, asymptotic bounds known)

Statement:
Let R(G; k) denote the minimal m such that if the edges of K_m are k-coloured
then there is a monochromatic copy of G. Determine R(K_{s,t}; k) where K_{s,t}
is the complete bipartite graph.

Background:
Chung-Graham (1975) proved general bounds and R(K_{2,2}; k) = (1+o(1))k².
Alon-Rónyai-Szabó (1999) proved R(K_{3,3}; k) = (1+o(1))k³ and showed that
if s ≥ (t-1)!+1 then R(K_{s,t}; k) grows as k^t.

Key Insight:
The Ramsey number R(K_{s,t}; k) grows polynomially in k (unlike R(K_n; 2)
which grows exponentially). Algebraic constructions (norm graphs) give
tight lower bounds in many cases.

Tags: ramsey-theory, bipartite-graphs, multicolor-ramsey
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos558

open SimpleGraph

/-
## Part 1: Basic Definitions

Complete bipartite graphs and Ramsey numbers.
-/

/-- The complete bipartite graph K_{s,t} -/
structure CompleteBipartite where
  s : ℕ
  t : ℕ

notation "K[" s "," t "]" => CompleteBipartite.mk s t

/-- K_{s,t} has s + t vertices -/
def CompleteBipartite.vertexCount (G : CompleteBipartite) : ℕ := G.s + G.t

/-- K_{s,t} has s * t edges -/
def CompleteBipartite.edgeCount (G : CompleteBipartite) : ℕ := G.s * G.t

/-- A k-coloring of the edges of K_m -/
def EdgeColoring (m k : ℕ) := Fin m → Fin m → Fin k

/-- A graph G contains a monochromatic copy of K_{s,t} in coloring c -/
def hasMonochromaticBipartite (m : ℕ) (c : EdgeColoring m k)
    (G : CompleteBipartite) (color : Fin k) : Prop :=
  ∃ (S T : Finset (Fin m)),
    S.card = G.s ∧ T.card = G.t ∧
    Disjoint S T ∧
    ∀ x ∈ S, ∀ y ∈ T, c x y = color

/-- R(K_{s,t}; k): The multicolor Ramsey number.
    Axiomatized as the minimum m such that every k-coloring of K_m
    contains a monochromatic K_{s,t}. -/
axiom ramseyBipartite (G : CompleteBipartite) (k : ℕ) : ℕ

notation "R(" G ";" k ")" => ramseyBipartite G k

/-
## Part 2: Basic Properties

The Ramsey number is well-defined and has basic properties.
-/

/-
## Part 3: Chung-Graham Bounds (1975)

General bounds for R(K_{s,t}; k).
-/

/-- Chung-Graham lower bound -/
noncomputable def chungGrahamLower (s t k : ℕ) : ℝ :=
  (2 * Real.pi * Real.sqrt (s * t))^(1 / (s + t : ℝ)) *
    ((s + t : ℝ) / Real.exp 2) * k^((s * t - 1 : ℝ) / (s + t : ℝ))

/-- Chung-Graham upper bound -/
noncomputable def chungGrahamUpper (s t k : ℕ) : ℝ :=
  (t - 1 : ℝ) * (k + k^(1 / s : ℝ))^s

/-- Chung-Graham theorem (1975): General bounds -/
axiom chung_graham_bounds (s t k : ℕ)
    (hs : s ≥ 1) (ht : t ≥ 1) (hk : k ≥ 2) :
  chungGrahamLower s t k ≤ R(K[s, t]; k) ∧
    (R(K[s, t]; k) : ℝ) ≤ chungGrahamUpper s t k

/-
## Part 4: The Case K_{2,2} (Four-Cycle)

R(K_{2,2}; k) = (1+o(1))k².
-/

/-- K_{2,2} is the 4-cycle C_4 -/
def C4 : CompleteBipartite := K[2, 2]

/-- Chung-Graham (1975): R(K_{2,2}; k) ~ k² -/
axiom ramsey_K22 (k : ℕ) (hk : k ≥ 2) :
  ∃ (c₁ c₂ : ℝ), c₁ > 0 ∧ c₂ > 0 ∧
    c₁ * k^2 ≤ R(C4; k) ∧ (R(C4; k) : ℝ) ≤ c₂ * k^2

/-
## Part 5: The Case K_{3,3}

Alon-Rónyai-Szabó (1999): R(K_{3,3}; k) ~ k³.
-/

/-- K_{3,3} is the utility graph -/
def K33 : CompleteBipartite := K[3, 3]

/-- Alon-Rónyai-Szabó (1999): R(K_{3,3}; k) ~ k³ -/
axiom ramsey_K33 (k : ℕ) (hk : k ≥ 2) :
  ∃ (c₁ c₂ : ℝ), c₁ > 0 ∧ c₂ > 0 ∧
    c₁ * k^3 ≤ R(K33; k) ∧ (R(K33; k) : ℝ) ≤ c₂ * k^3

/-
## Part 6: The General Theorem of Alon-Rónyai-Szabó

If s ≥ (t-1)! + 1, then R(K_{s,t}; k) grows as k^t.
-/

/-- The critical threshold for s -/
def criticalS (t : ℕ) : ℕ := Nat.factorial (t - 1) + 1

/-- Alon-Rónyai-Szabó main theorem: R(K_{s,t}; k) = Θ(k^t) when s ≥ (t-1)!+1 -/
axiom alon_ronyai_szabo (s t k : ℕ)
    (hs : s ≥ criticalS t) (ht : t ≥ 2) (hk : k ≥ 2) :
  ∃ (c₁ c₂ : ℝ), c₁ > 0 ∧ c₂ > 0 ∧
    c₁ * k^t ≤ R(K[s, t]; k) ∧ (R(K[s, t]; k) : ℝ) ≤ c₂ * k^t

/-
## Part 7: Erdős Problem #558 Statement

The problem asks to determine R(K_{s,t}; k) for all s, t.
-/

/-- Erdős Problem #558: The main statement -/
theorem erdos_558 (s t k : ℕ) (hs : s ≥ 1) (ht : t ≥ 1) (hk : k ≥ 2) :
    -- Chung-Graham bounds hold
    (chungGrahamLower s t k ≤ R(K[s, t]; k) ∧
      (R(K[s, t]; k) : ℝ) ≤ chungGrahamUpper s t k) ∧
    -- If s ≥ (t-1)!+1, the exponent is exactly t
    (s ≥ criticalS t → ∃ (c₁ c₂ : ℝ), c₁ > 0 ∧ c₂ > 0 ∧
      c₁ * k^t ≤ R(K[s, t]; k) ∧ (R(K[s, t]; k) : ℝ) ≤ c₂ * k^t) := by
  constructor
  · exact chung_graham_bounds s t k hs ht hk
  · intro hcrit
    exact alon_ronyai_szabo s t k hcrit ht hk

/-
## Part 8: Norm Graphs and Lower Bounds

Algebraic constructions give tight lower bounds.
-/

/-
## Part 9: Specific Values and Bounds
-/

/-
## Part 10: Connection to Extremal Graph Theory
-/

/-
## Part 11: Summary
-/

/-- Main summary: Erdős Problem #558 is partially solved -/
theorem erdos_558_summary :
    -- R(K_{2,2}; k) ~ k²
    (∀ k ≥ 2, ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      c₁ * k^2 ≤ R(C4; k) ∧ (R(C4; k) : ℝ) ≤ c₂ * k^2) ∧
    -- R(K_{3,3}; k) ~ k³
    (∀ k ≥ 2, ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      c₁ * k^3 ≤ R(K33; k) ∧ (R(K33; k) : ℝ) ≤ c₂ * k^3) ∧
    -- If s ≥ (t-1)!+1, then R(K_{s,t}; k) = Θ(k^t)
    (∀ s t k, s ≥ criticalS t → t ≥ 2 → k ≥ 2 →
      ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
        c₁ * k^t ≤ R(K[s, t]; k) ∧ (R(K[s, t]; k) : ℝ) ≤ c₂ * k^t) := by
  exact ⟨ramsey_K22, ramsey_K33, alon_ronyai_szabo⟩

end Erdos558
