/- Erdős Problem #875 — Admissible Sequences with Disjoint Sumsets

Let A = {a₁ < a₂ < ···} ⊂ ℕ be an infinite set such that the r-fold
sumsets
  Sᵣ = { a_{i₁} + ··· + a_{iᵣ} : i₁ < ··· < iᵣ, aᵢ ∈ A }
are pairwise disjoint for distinct r ≥ 1. Such sequences are called
**admissible**.

Questions:
1. How rapidly must an admissible sequence grow?
2. How small can consecutive differences a_{n+1} − aₙ be?
3. For which c is it possible that a_{n+1} − aₙ ≤ n^c?

This is an infinite variant of Problem #874 (Deshouillers–Erdős).

Status: OPEN
Reference: https://erdosproblems.com/875
-/

import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Bitwise

open Finset

-- ## Core Definitions

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

-- ## Main Questions (OPEN)

/-- For which values of c can we have
    a(n+1) − a(n) ≤ n^c for all sufficiently large n? -/
def HasPolynomialGaps (a : ℕ → ℕ) (c : ℝ) : Prop :=
  ∀ᶠ (n : ℕ) in Filter.atTop,
    (a (n + 1) - a n : ℝ) ≤ (n : ℝ) ^ c

/-- **Erdős Problem #875 — Gap Question (Open).**
    Determine the infimum of c such that no admissible sequence has
    a(n+1) − a(n) ≤ n^c for all large n. -/
/-- Can an admissible sequence satisfy a(n+1)/a(n) → 1?
    Erdős noted this is "not completely trivial." -/
def HasRatioOne (a : ℕ → ℕ) : Prop :=
  Filter.Tendsto (fun n => (a (n + 1) : ℝ) / (a n : ℝ)) Filter.atTop (nhds 1)

/-- Powers of 2 form a strictly increasing sequence. -/
theorem pow2_strictly_increasing : StrictlyIncreasing (fun n => 2 ^ n) := by
  intro n
  exact Nat.pow_lt_pow_right (by omega) (by omega)

/-- Key lemma: the popcount (number of 1-bits) of a sum of r distinct
    powers of 2 equals r. This is because distinct powers of 2 have
    disjoint binary representations.

    We axiomatize this as the full formal proof requires detailed bit-level
    reasoning about Nat.popcount and Finset.sum over powers of 2. -/
/-- Powers of 2 are admissible: the r-fold sumsets are disjoint because
    sums of r distinct powers of 2 have exactly r bits set in binary.
    Different r gives different popcount, so the sumsets are disjoint.

    The strictly increasing part is proved; the disjoint sumsets part
    relies on the popcount argument. -/
theorem powers_of_two_admissible :
    IsAdmissible (fun n => 2 ^ n) := by
  constructor
  · exact pow2_strictly_increasing
  · sorry -- Disjoint sumsets via popcount argument

/-- Every admissible sequence a satisfies a(n) ≥ n + 1 for all n.
    Proof: if a(0) ≥ 1 (since a(0) ∈ ℕ and we need the sequence to be
    strictly increasing starting from a positive value), then by strict
    increase a(n) ≥ a(0) + n ≥ 1 + n. -/
theorem admissible_growth_lower (a : ℕ → ℕ) (ha : IsAdmissible a)
    (h0 : a 0 ≥ 1) (n : ℕ) : a n ≥ n + 1 := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    have hlt := ha.1 n
    omega

-- ## Small Examples

/-- The set {1, 2, 4} = {2^0, 2^1, 2^2} has disjoint sumsets:
    S₁ = {1, 2, 4}, S₂ = {3, 5, 6}, S₃ = {7}, all disjoint. -/
theorem pow2_small_example :
    Disjoint (rFoldSumset {1, 2, 4} 1) (rFoldSumset {1, 2, 4} 2) := by
  native_decide

-- ## Connection to Problem #874

/-- Problem #874 is the finite version: for a finite set A ⊂ {1,...,n},
    what is the maximum |A| such that the r-fold sumsets are disjoint?
    The infinite version asks about growth rates of infinite admissible sets.
    Proved: A ⊆ {0,...,n} has at most n+1 elements (trivial upper bound). -/
theorem finite_version_connection :
    ∀ n : ℕ, ∃ f : ℕ, ∀ A : Finset ℕ,
      (∀ a ∈ A, a ≤ n) →
      (∀ r s, r ≠ s → 1 ≤ r → 1 ≤ s → r ≤ A.card → s ≤ A.card →
        Disjoint (rFoldSumset A r) (rFoldSumset A s)) →
      A.card ≤ f := by
  intro n
  exact ⟨n + 1, fun A hA _ =>
    le_trans (Finset.card_le_card (fun a ha =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (hA a ha))))
      (by simp [Finset.card_range])⟩
