/-
# Erdős Problem #341: Dickson's Sum-Free Extension

Given a finite set A = {a₁ < ⋯ < aₖ} of positive integers, extend to an
infinite sequence where each a_{n+1} is the smallest integer > aₙ not
expressible as aᵢ + aⱼ with i, j ≤ n. Is the sequence of differences
a_{m+1} − aₘ eventually periodic?

## Key Context

- An old problem of Dickson, popularized by Erdős–Graham (1980)
- Even {1, 4, 9, 16, 25} requires thousands of terms before periodicity
- Featured as Problem 7 on Ben Green's open problems list
- The sequence avoids being a sumset of its own initial segments

## References

- [ErGr80] Erdős–Graham (1980), p. 53
- Ben Green, open problems list, Problem 7
- <https://erdosproblems.com/341>
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic

/- ## Core Definitions -/

/-- The set of pairwise sums from a finite set of naturals:
    {aᵢ + aⱼ : aᵢ, aⱼ ∈ S, i ≤ j}. -/
def pairwiseSums (S : Finset ℕ) : Finset ℕ :=
  (S.product S).image (fun p => p.1 + p.2)

/-- Whether a number is representable as a sum of two elements from S. -/
def IsSumRepresentable (S : Finset ℕ) (n : ℕ) : Prop :=
  n ∈ pairwiseSums S

/- ## Key Lemma: Existence of Valid Extensions -/

/-- For any finite set S and bound, there exists a number above the bound
    that is not a pairwise sum of elements of S. This is because
    pairwiseSums S is finite, so it cannot contain all naturals above
    any given bound. -/
private lemma dickson_next_exists (S : Finset ℕ) (bound : ℕ) :
    ∃ m, m > bound ∧ m ∉ pairwiseSums S := by
  refine ⟨bound + (pairwiseSums S).sup id + 1, by omega, ?_⟩
  intro hmem
  have h_le : id (bound + (pairwiseSums S).sup id + 1) ≤ (pairwiseSums S).sup id :=
    Finset.le_sup hmem
  simp at h_le
  omega

/- ## Dickson Sequence Definition -/

/-- Internal step function: returns (current value, accumulated element set).
    At step 0: the initial value is max(A₀) and the accumulated set is {max(A₀)}.
    At step n+1: find the smallest number above the previous value that is
    not a pairwise sum of the accumulated set. -/
noncomputable def dicksonStep (A₀ : Finset ℕ) : ℕ → ℕ × Finset ℕ
  | 0 =>
    let val := if h : A₀.Nonempty then A₀.max' h else 0
    (val, {val})
  | (n + 1) =>
    let nextVal := Nat.find (dickson_next_exists (dicksonStep A₀ n).2 (dicksonStep A₀ n).1)
    (nextVal, (dicksonStep A₀ n).2 ∪ {nextVal})

/-- The Dickson extension sequence: given initial set A₀, extend by always
    choosing the smallest integer > current value that is not a sum
    of two previous elements. Returns the n-th element. -/
noncomputable def dicksonSeq (A₀ : Finset ℕ) (n : ℕ) : ℕ :=
  (dicksonStep A₀ n).1

/-- The difference sequence: d(n) = a_{n+1} − aₙ. -/
noncomputable def dicksonDiff (A₀ : Finset ℕ) (n : ℕ) : ℕ :=
  dicksonSeq A₀ (n + 1) - dicksonSeq A₀ n

/-- A sequence is eventually periodic with period p starting from index N. -/
def IsEventuallyPeriodic (f : ℕ → ℕ) (p N : ℕ) : Prop :=
  p ≥ 1 ∧ ∀ n : ℕ, n ≥ N → f (n + p) = f n

/- ## Main Conjecture -/

/-- **Erdős–Dickson Conjecture (OPEN)**: For every finite starting set A₀,
    the difference sequence d(n) = a_{n+1} − aₙ is eventually periodic. -/
def erdos_341_conjecture : Prop :=
  ∀ A₀ : Finset ℕ, A₀.Nonempty →
    ∃ p N : ℕ, IsEventuallyPeriodic (dicksonDiff A₀) p N

/- ## Structural Properties (proved from definition) -/

/-- The sequence is strictly increasing: a_{n+1} > aₙ.
    Follows from Nat.find_spec: the found value satisfies m > bound. -/
theorem dickson_strictly_increasing :
  ∀ (A₀ : Finset ℕ) (n : ℕ), A₀.Nonempty →
    dicksonSeq A₀ (n + 1) > dicksonSeq A₀ n := by
  intro A₀ n _
  show (dicksonStep A₀ (n + 1)).1 > (dicksonStep A₀ n).1
  simp only [dicksonStep]
  exact (Nat.find_spec (dickson_next_exists (dicksonStep A₀ n).2 (dicksonStep A₀ n).1)).1

/-- Differences are positive: d(n) ≥ 1. Follows from strict increase. -/
theorem dickson_diff_pos :
    ∀ (A₀ : Finset ℕ) (n : ℕ), A₀.Nonempty →
      dicksonDiff A₀ n ≥ 1 := by
  intro A₀ n hne
  unfold dicksonDiff
  have := dickson_strictly_increasing A₀ n hne
  omega

/-- The sequence avoids self-sums: a_{n+1} is not a sum of two
    elements from the accumulated set at step n.
    Follows from Nat.find_spec: the found value avoids pairwiseSums. -/
theorem dickson_avoids_sums :
  ∀ (A₀ : Finset ℕ) (n : ℕ), A₀.Nonempty →
    ¬IsSumRepresentable (dicksonStep A₀ n).2
      (dicksonSeq A₀ (n + 1)) := by
  intro A₀ n _
  show ¬IsSumRepresentable (dicksonStep A₀ n).2 (dicksonStep A₀ (n + 1)).1
  simp only [dicksonStep]
  exact (Nat.find_spec (dickson_next_exists (dicksonStep A₀ n).2 (dicksonStep A₀ n).1)).2

/-- Minimality: a_{n+1} is the smallest valid extension.
    Every integer between aₙ + 1 and a_{n+1} − 1 is a sum of two earlier terms.
    Follows from Nat.find_min: values below the found minimum don't satisfy
    the predicate, so they must be sums. -/
theorem dickson_minimal :
  ∀ (A₀ : Finset ℕ) (n : ℕ) (m : ℕ), A₀.Nonempty →
    dicksonSeq A₀ n < m → m < dicksonSeq A₀ (n + 1) →
    IsSumRepresentable (dicksonStep A₀ n).2 m := by
  intro A₀ n m _ h_lb h_ub
  -- m < dicksonSeq A₀ (n+1) = Nat.find (...)
  -- By Nat.find_min: ¬(m > dicksonSeq A₀ n ∧ m ∉ pairwiseSums ...)
  -- Since m > dicksonSeq A₀ n, we must have m ∈ pairwiseSums ...
  have h_not : ¬(m > (dicksonStep A₀ n).1 ∧ m ∉ pairwiseSums (dicksonStep A₀ n).2) := by
    have : m < (dicksonStep A₀ (n + 1)).1 := h_ub
    simp only [dicksonStep] at this
    exact Nat.find_min (dickson_next_exists (dicksonStep A₀ n).2 (dicksonStep A₀ n).1) this
  push_neg at h_not
  unfold IsSumRepresentable
  exact h_not (by exact h_lb)

/- ## Derived Properties -/

/-- Growth rate: the sequence grows at least linearly.
    Since a_{n+1} > aₙ (strict increase of naturals), we get aₙ ≥ n by induction. -/
theorem dickson_linear_growth :
  ∀ (A₀ : Finset ℕ), A₀.Nonempty →
    ∃ c : ℕ, c ≥ 1 ∧ ∀ n : ℕ, dicksonSeq A₀ n ≥ c * n := by
  intro A₀ hne
  refine ⟨1, le_refl _, ?_⟩
  intro n
  simp only [one_mul]
  induction n with
  | zero => omega
  | succ n ih =>
    have := dickson_strictly_increasing A₀ n hne
    omega
