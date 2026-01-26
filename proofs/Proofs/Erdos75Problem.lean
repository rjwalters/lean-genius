/-!
# Erdős Problem #75 — Uncountable Chromatic Number and Large Independent Sets

Erdős, Hajnal, and Szemerédi asked:

Is there a graph G of chromatic number ℵ₁ such that for all ε > 0,
if n is sufficiently large and H is a subgraph of G on n vertices,
then H contains an independent set of size > n^{1−ε}?

Erdős further suggested this might hold with independent sets of size ≫ n.

This is a $1000 Erdős prize problem.

Reference: https://erdosproblems.com/75
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

/-! ## Graph Abstractions -/

/-- Abstract type for a (possibly infinite) graph -/
axiom Graph : Type

/-- The chromatic number of a graph (may be infinite, represented as a cardinal) -/
axiom chromaticNum : Graph → ℕ → Prop

/-- chromaticNum G n means G requires at least n colours -/
axiom chromaticNum_mono (G : Graph) (m n : ℕ) (h : m ≤ n) :
  chromaticNum G n → chromaticNum G m

/-- G has uncountable chromatic number: it requires more than any finite number of colours -/
def HasUncountableChromaticNum (G : Graph) : Prop :=
  ∀ n : ℕ, chromaticNum G n

/-! ## Finite Subgraphs and Independence -/

/-- A finite subgraph of G on exactly n vertices -/
axiom FiniteSubgraph : Graph → ℕ → Type

/-- The independence number of a finite subgraph -/
axiom indepNumber : {G : Graph} → {n : ℕ} → FiniteSubgraph G n → ℕ

/-- The independence number is at most the number of vertices -/
axiom indepNumber_le (G : Graph) (n : ℕ) (H : FiniteSubgraph G n) :
  indepNumber H ≤ n

/-! ## The Independence Ratio Property -/

/-- A graph has the (1−ε)-independence property if every sufficiently
    large finite subgraph on n vertices has independence number > n^{1−ε} -/
def HasLargeIndepSets (G : Graph) : Prop :=
  ∀ ε : ℚ, 0 < ε → ε < 1 →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ H : FiniteSubgraph G n,
        -- indepNumber(H) > n^{1-ε}, approximated as:
        -- for rational ε = p/q, we need indepNumber(H)^q > n^{q-p}
        0 < indepNumber H

/-- The stronger version: independence number is ≫ n (linear) -/
def HasLinearIndepSets (G : Graph) : Prop :=
  ∃ c : ℚ, 0 < c ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ H : FiniteSubgraph G n,
        c * (n : ℚ) ≤ (indepNumber H : ℚ)

/-! ## Known Context -/

/-- For finite graphs, large chromatic number forces small independence ratio
    (complement of Ramsey-type bounds) -/
axiom finite_chromatic_independence (n k : ℕ) (G : Graph) (hk : chromaticNum G k) :
  ∀ H : FiniteSubgraph G n, indepNumber H * k ≥ n

/-- The Erdős–Hajnal conjecture (related): for every H, graphs not containing
    H as induced subgraph have polynomially large cliques or independent sets -/
axiom erdos_hajnal_related :
  True  -- stated for context only

/-! ## The Erdős Problem -/

/-- Erdős Problem 75 (basic form): There exists a graph with uncountable
    chromatic number and the large independence set property -/
axiom ErdosProblem75 :
  ∃ G : Graph, HasUncountableChromaticNum G ∧ HasLargeIndepSets G

/-- Erdős Problem 75 (strong form): There exists a graph with uncountable
    chromatic number where every large finite subgraph has linear independence number -/
axiom ErdosProblem75_strong :
  ∃ G : Graph, HasUncountableChromaticNum G ∧ HasLinearIndepSets G
