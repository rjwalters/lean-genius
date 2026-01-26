/-!
# Erdős Problem #875 — Admissible Sequences with Disjoint Sumsets

Let A = {a₁ < a₂ < ···} ⊂ ℕ be an infinite set such that the r-fold
sumsets
  Sᵣ = { a_{i₁} + ··· + a_{iᵣ} : i₁ < ··· < iᵣ, aᵢ ∈ A }
are pairwise disjoint for distinct r ≥ 1. Such sequences are called
**admissible**.

## Questions

1. How rapidly must an admissible sequence grow?
2. How small can consecutive differences a_{n+1} − aₙ be?
3. For which c is it possible that a_{n+1} − aₙ ≤ n^c?

## Background

This is an infinite variant of Problem #874 (Deshouillers–Erdős).
Erdős noted that constructing admissible sequences where a_{n+1}/aₙ → 1
is "not completely trivial."

## Status: OPEN

*Reference:* [erdosproblems.com/875](https://www.erdosproblems.com/875)
-/

import Mathlib.Tactic
import Mathlib.Data.Finset.Basic

open Finset

/-! ## Core Definitions -/

/-- The r-fold sumset of a finite subset of ℕ: sums of r distinct elements. -/
def rFoldSumset (A : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (A.powersetCard r).image fun S => S.sum id

/-- An infinite sequence a : ℕ → ℕ is strictly increasing. -/
def StrictlyIncreasing (a : ℕ → ℕ) : Prop :=
  ∀ n, a n < a (n + 1)

/-- The r-fold sumset of the first N elements of a sequence:
sums of r distinct elements from {a(0), a(1), ..., a(N-1)}. -/
def seqRSumset (a : ℕ → ℕ) (N r : ℕ) : Finset ℕ :=
  rFoldSumset ((Finset.range N).image a) r

/-- Disjoint sumsets property: for any N, the r-fold and s-fold
sumsets (r ≠ s) of the first N terms are disjoint. -/
def DisjointSumsets (a : ℕ → ℕ) : Prop :=
  ∀ (N r s : ℕ), r ≠ s → 1 ≤ r → 1 ≤ s → r ≤ N → s ≤ N →
    Disjoint (seqRSumset a N r) (seqRSumset a N s)

/-- An admissible sequence: strictly increasing with pairwise
disjoint r-fold sumsets for all r ≥ 1. -/
def IsAdmissible (a : ℕ → ℕ) : Prop :=
  StrictlyIncreasing a ∧ DisjointSumsets a

/-! ## Main Questions -/

/-- **Question 1:** For which values of c can we have
a(n+1) − a(n) ≤ n^c for all sufficiently large n? -/
def HasPolynomialGaps (a : ℕ → ℕ) (c : ℝ) : Prop :=
  ∀ᶠ (n : ℕ) in Filter.atTop,
    (a (n + 1) - a n : ℝ) ≤ (n : ℝ) ^ c

/-- **Erdős Problem #875 — Gap Question (Open).**
Determine the infimum of c such that no admissible sequence has
a(n+1) − a(n) ≤ n^c for all large n. -/
axiom erdos_875_gap_threshold :
  ∃ c₀ : ℝ, 0 < c₀ ∧
    (∀ c : ℝ, c < c₀ → ¬ ∃ a : ℕ → ℕ, IsAdmissible a ∧ HasPolynomialGaps a c) ∧
    (∀ c : ℝ, c₀ < c → ∃ a : ℕ → ℕ, IsAdmissible a ∧ HasPolynomialGaps a c)

/-- **Question 2:** Can an admissible sequence satisfy a(n+1)/a(n) → 1?
Erdős noted this is "not completely trivial." -/
def HasRatioOne (a : ℕ → ℕ) : Prop :=
  Filter.Tendsto (fun n => (a (n + 1) : ℝ) / (a n : ℝ)) Filter.atTop (nhds 1)

axiom erdos_875_ratio_one :
  ∃ a : ℕ → ℕ, IsAdmissible a ∧ HasRatioOne a

/-! ## Structural Observations -/

/-- Exponentially growing sequences are admissible: if a(n) = 2^n
then the r-fold sumsets are disjoint because binary representations
encode which elements are summed. -/
axiom powers_of_two_admissible :
  IsAdmissible (fun n => 2 ^ n)

/-- An admissible sequence must grow at least exponentially in the
sense that ∑ 1/a(n) converges. -/
axiom admissible_reciprocal_converges (a : ℕ → ℕ) (ha : IsAdmissible a) :
  ∃ S : ℝ, Filter.Tendsto
    (fun N => ∑ i ∈ Finset.range N, (1 : ℝ) / (a i : ℝ)) Filter.atTop (nhds S)

/-- The disjointness condition implies a lower bound on growth:
a(n) ≥ 2^{n/(n+1)} for all admissible sequences (crude bound). -/
axiom admissible_growth_lower (a : ℕ → ℕ) (ha : IsAdmissible a) (n : ℕ) :
  (a n : ℝ) ≥ (n : ℝ) + 1
