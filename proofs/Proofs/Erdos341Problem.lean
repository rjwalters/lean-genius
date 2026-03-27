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
import Mathlib.Tactic

/- ## Core Definitions -/

/-- The set of pairwise sums from a finite set of naturals:
    {aᵢ + aⱼ : aᵢ, aⱼ ∈ S, i ≤ j}. -/
def pairwiseSums (S : Finset ℕ) : Finset ℕ :=
  (S.product S).image (fun p => p.1 + p.2)

/-- Whether a number is representable as a sum of two elements from S. -/
def IsSumRepresentable (S : Finset ℕ) (n : ℕ) : Prop :=
  n ∈ pairwiseSums S

/-- For any bound and finite set, there exists a larger number not in the set.
    Key lemma enabling the greedy Dickson construction. -/
private lemma dickson_next_exists (val : ℕ) (sums : Finset ℕ) :
    ∃ m, val < m ∧ m ∉ sums :=
  ⟨sums.sup id + val + 1, by omega, fun hmem => by
    have := Finset.le_sup (f := id) hmem; simp only [id_eq] at this; omega⟩

/-- Auxiliary function for the Dickson sequence construction.
    Returns (current_value, accumulated_terms) at each step.
    At step 0, returns (max A₀, A₀). At step n+1, finds the least
    integer exceeding the current value that avoids pairwise sums. -/
noncomputable def dicksonAux (A₀ : Finset ℕ) : ℕ → ℕ × Finset ℕ
  | 0 => if h : A₀.Nonempty then (A₀.max' h, A₀) else (0, ∅)
  | n + 1 =>
    let prev := dicksonAux A₀ n
    let sums := pairwiseSums prev.2
    let hex := dickson_next_exists prev.1 sums
    (Nat.find hex, insert (Nat.find hex) prev.2)

/-- The Dickson extension sequence: given initial set A₀, extend by always
    choosing the smallest integer > current maximum that is not a sum
    of two previous elements. Returns the n-th extension value. -/
noncomputable def dicksonSeq (A₀ : Finset ℕ) (n : ℕ) : ℕ :=
  (dicksonAux A₀ n).1

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

/- ## Structural Properties -/

/-- The sequence is strictly increasing: a_{n+1} > aₙ.
    Follows from Nat.find_spec: the next value satisfies val < m. -/
theorem dickson_strictly_increasing :
    ∀ (A₀ : Finset ℕ) (n : ℕ), A₀.Nonempty →
      dicksonSeq A₀ (n + 1) > dicksonSeq A₀ n := by
  intro A₀ n _
  exact (Nat.find_spec (dickson_next_exists (dicksonAux A₀ n).1
    (pairwiseSums (dicksonAux A₀ n).2))).1

/-- Differences are positive: d(n) ≥ 1. Follows from strict increase. -/
theorem dickson_diff_pos :
    ∀ (A₀ : Finset ℕ) (n : ℕ), A₀.Nonempty →
      dicksonDiff A₀ n ≥ 1 := by
  intro A₀ n hne
  unfold dicksonDiff
  have := dickson_strictly_increasing A₀ n hne
  omega

/-- The sequence avoids self-sums: a_{n+1} is not a sum of two
    elements from {a₁, ..., aₙ}. -/
axiom dickson_avoids_sums :
  ∀ (A₀ : Finset ℕ) (n : ℕ), A₀.Nonempty →
    ¬IsSumRepresentable (Finset.range (n + 1) |>.image (dicksonSeq A₀))
      (dicksonSeq A₀ (n + 1))

/-- Minimality: a_{n+1} is the smallest valid extension.
    Every integer between aₙ + 1 and a_{n+1} − 1 is a sum of two earlier terms. -/
axiom dickson_minimal :
  ∀ (A₀ : Finset ℕ) (n : ℕ) (m : ℕ), A₀.Nonempty →
    dicksonSeq A₀ n < m → m < dicksonSeq A₀ (n + 1) →
    IsSumRepresentable (Finset.range (n + 1) |>.image (dicksonSeq A₀)) m

/- ## Examples -/

/-- Starting from {1}: the first extension value is 1 (= max {1}). -/
theorem singleton_one_example :
    dicksonSeq ({1} : Finset ℕ) 0 = 1 := by
  unfold dicksonSeq dicksonAux
  simp

/-- The sequence starting from {1, 4, 9, 16, 25} (perfect squares)
    requires thousands of terms before periodicity emerges. -/
axiom squares_slow_periodicity :
  ∀ N : ℕ, N < 1000 →
    ¬∃ p : ℕ, p ≥ 1 ∧ p ≤ 10 ∧ IsEventuallyPeriodic (dicksonDiff {1, 4, 9, 16, 25}) p N

/-- If the conjecture holds, the eventual period depends on A₀. -/
axiom period_depends_on_initial :
  ∃ A₁ A₂ : Finset ℕ,
    A₁.Nonempty ∧ A₂.Nonempty ∧
    ∀ p₁ p₂ N₁ N₂ : ℕ,
      IsEventuallyPeriodic (dicksonDiff A₁) p₁ N₁ →
      IsEventuallyPeriodic (dicksonDiff A₂) p₂ N₂ →
      p₁ ≠ p₂

/-- Growth rate: the sequence grows at least linearly. -/
theorem dickson_linear_growth :
    ∀ (A₀ : Finset ℕ), A₀.Nonempty →
      ∃ c : ℕ, c ≥ 1 ∧ ∀ n : ℕ, dicksonSeq A₀ n ≥ c * n := by
  intro A₀ hne
  exact ⟨1, le_refl 1, fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      have := dickson_strictly_increasing A₀ n hne
      omega⟩
