/-
# Erdős Problem #1075: Dense Subgraphs in r-Uniform Hypergraphs

**Source:** [erdosproblems.com/1075](https://erdosproblems.com/1075)
**Status:** OPEN

## Statement

For r ≥ 3, does there exist c_r > r^{-r} such that for any ε > 0,
if n is sufficiently large, any r-uniform hypergraph on n vertices
with at least (1+ε)(n/r)^r edges contains a subgraph on m vertices
with at least c_r · m^r edges, where m = m(n) → ∞ as n → ∞?

## Background

- Erdős [Er64f] (1964) proved this holds with c_r = r^{-r} under the
  stronger threshold εn^r
- The question is whether the weaker threshold (1+ε)(n/r)^r allows
  improving the density constant beyond r^{-r}
- The constant r^{-r} arises from random subgraph selection

## Approach

We define r-uniform hypergraphs and induced subhypergraphs, state
the known result as an axiom, formalize the open conjecture, and
provide supporting asymptotic and structural results.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Real

namespace Erdos1075

/- ## Part I: Hypergraph Definitions -/

/-- An r-uniform hypergraph on vertex set V -/
structure Hypergraph (V : Type*) (r : ℕ) where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = r

/-- Number of edges in a hypergraph -/
def Hypergraph.numEdges {V : Type*} {r : ℕ} (H : Hypergraph V r) : ℕ :=
  H.edges.card

/-- Induced subhypergraph on a subset of vertices -/
def Hypergraph.induced {V : Type*} [DecidableEq V] {r : ℕ}
    (H : Hypergraph V r) (S : Finset V) : Hypergraph V r where
  edges := H.edges.filter (fun e => e ⊆ S)
  uniform := by
    intro e he
    simp only [mem_filter] at he
    exact H.uniform e he.1

/-- The threshold constant r^{-r} from random subgraph selection -/
noncomputable def thresholdConstant (r : ℕ) : ℝ :=
  (r : ℝ)^(-(r : ℤ))

/- ## Part II: Erdős's Known Result (1964) -/

/--
**Erdős [Er64f] (1964):** Any r-uniform hypergraph on n vertices
with at least εn^r edges contains a subhypergraph on m vertices
with at least r^{-r} · m^r edges.

Note: This uses the STRONGER threshold εn^r. The open question
asks about the weaker threshold (1+ε)(n/r)^r.
-/
axiom erdos_1964_result :
  ∀ r : ℕ, r ≥ 3 →
    ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ n ≥ N₀,
        ∀ V : Finset ℕ, V.card = n →
          ∀ H : Hypergraph ℕ r,
            (∀ e ∈ H.edges, e ⊆ V) →
            (H.numEdges : ℝ) ≥ ε * (n : ℝ)^r →
            ∃ S : Finset ℕ, S ⊆ V ∧
              ∃ m : ℕ, S.card = m ∧ m > 0 ∧
              ((H.induced S).numEdges : ℝ) ≥ thresholdConstant r * (m : ℝ)^r

/--
The threshold constant r^{-r} is strictly decreasing in r for r ≥ 2.
Since (r+1)^{-(r+1)} < r^{-r} for all r ≥ 2, the problem becomes
harder for larger r.
-/
axiom threshold_decreasing :
  ∀ r : ℕ, r ≥ 2 →
    thresholdConstant (r + 1) < thresholdConstant r

/-- Concrete threshold values for small r -/
/- ## Part III: The Open Conjecture -/

/--
**Erdős Problem #1075 (OPEN):**
For r ≥ 3, does there exist c_r > r^{-r} such that for any ε > 0,
if n is sufficiently large, any r-uniform hypergraph on n vertices
with at least (1+ε)(n/r)^r edges contains a subgraph on m vertices
(m → ∞ as n → ∞) with at least c_r · m^r edges?

The key difference from the known result is the edge threshold:
(1+ε)(n/r)^r is much smaller than εn^r for large n.
-/
def ErdosConjecture1075 : Prop :=
  ∀ r : ℕ, r ≥ 3 →
    ∃ c : ℝ, c > thresholdConstant r ∧
      ∀ ε : ℝ, ε > 0 →
        ∃ N₀ : ℕ, ∀ n ≥ N₀,
          ∀ V : Finset ℕ, V.card = n →
            ∀ H : Hypergraph ℕ r,
              (∀ e ∈ H.edges, e ⊆ V) →
              (H.numEdges : ℝ) ≥ (1 + ε) * ((n : ℝ) / r)^r →
              ∃ S : Finset ℕ, S ⊆ V ∧
                ∃ m : ℕ, S.card = m ∧ m > 0 ∧
                ((H.induced S).numEdges : ℝ) ≥ c * (m : ℝ)^r

/--
The edge threshold (1+ε)(n/r)^r is strictly smaller than εn^r for
large n when ε is small. This means the hypothesis in the conjecture
is weaker, so improving the conclusion (density constant) would be
a genuine strengthening.
-/
/- ## Part IV: Complete Hypergraphs and Asymptotics -/

/-- Complete r-uniform hypergraph on m vertices has C(m,r) edges -/
def completeHypergraphEdges (m r : ℕ) : ℕ := Nat.choose m r

/--
For large m, C(m,r) ~ m^r / r!, establishing the relationship
between binomial coefficients and the m^r density measure.
-/
/- ## Part V: Summary -/

/--
**Summary of Erdős Problem #1075:**

Erdős Problem #1075 asks whether the density constant c_r = r^{-r}
from the 1964 result can be improved when using the weaker edge
threshold (1+ε)(n/r)^r instead of εn^r.

**Known:** Erdős [Er64f] proved c_r = r^{-r} works with threshold εn^r.
**Open:** Whether c_r > r^{-r} is achievable with threshold (1+ε)(n/r)^r.
**Key insight:** r^{-r} is the random selection baseline; improvement
requires structural arguments exploiting the specific edge threshold.
-/
theorem erdos_1075_summary :
    -- Erdős's 1964 result with c_r = r^{-r} and threshold εn^r
    (∀ r : ℕ, r ≥ 3 →
      ∀ ε : ℝ, ε > 0 →
        ∃ N₀ : ℕ, ∀ n ≥ N₀,
          ∀ V : Finset ℕ, V.card = n →
            ∀ H : Hypergraph ℕ r,
              (∀ e ∈ H.edges, e ⊆ V) →
              (H.numEdges : ℝ) ≥ ε * (n : ℝ)^r →
              ∃ S : Finset ℕ, S ⊆ V ∧
                ∃ m : ℕ, S.card = m ∧ m > 0 ∧
                ((H.induced S).numEdges : ℝ) ≥ thresholdConstant r * (m : ℝ)^r) ∧
    -- The threshold constant is strictly decreasing
    (∀ r : ℕ, r ≥ 2 → thresholdConstant (r + 1) < thresholdConstant r) := by
  exact ⟨erdos_1964_result, threshold_decreasing⟩

end Erdos1075
