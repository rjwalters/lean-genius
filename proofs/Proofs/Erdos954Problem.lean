/-!
# Erdős Problem #954 — Rosen's Greedy Additive Sequence

Let 0 = a₀ < a₁ < a₂ < ⋯ be defined by a₀ = 0, a₁ = 1, and a_{k+1} is
the smallest integer n such that the number of representations
a_i + a_j ≤ n (0 ≤ i ≤ j ≤ k, j ≥ 1) is less than n.

**Conjecture**: The representation count R(x) = |{(i,j) : a_i + a_j ≤ x, i ≤ j, j ≥ 1}|
satisfies R(x) = x + O(x^{1/4+o(1)}).

**Status: OPEN.** Erdős and Rosen could not even prove R(x) ≤ (1+o(1))x.

The sequence begins: 0, 1, 3, 5, 9, 13, 17, 24, 31, 38, 45, ...
OEIS: A390642

Reference: https://erdosproblems.com/954
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- The representation count: number of pairs (i,j) with
    i ≤ j, j ≥ 1, and a(i) + a(j) ≤ n for a given sequence a. -/
def repCount (a : ℕ → ℕ) (k : ℕ) (n : ℕ) : ℕ :=
  (Finset.Icc 1 k).sum fun j =>
    (Finset.Icc 0 j).filter (fun i => a i + a j ≤ n) |>.card

/-- The greedy condition: a(k+1) is the smallest n such that
    repCount a k n < n. This ensures the sequence grows as slowly
    as possible while keeping R(n) < n at each new element. -/
def IsGreedyNext (a : ℕ → ℕ) (k : ℕ) : Prop :=
  repCount a k (a (k + 1)) < a (k + 1) ∧
  ∀ m, a k < m → m < a (k + 1) → repCount a k m ≥ m

/-- Rosen's greedy sequence satisfies the greedy condition at every step. -/
def IsRosenSequence (a : ℕ → ℕ) : Prop :=
  a 0 = 0 ∧ a 1 = 1 ∧ StrictMono a ∧ ∀ k ≥ 1, IsGreedyNext a k

/-! ## Known Initial Values -/

/-- The first few values of the Rosen sequence (OEIS A390642). -/
axiom rosen_initial_values :
    ∃ a : ℕ → ℕ, IsRosenSequence a ∧
      a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 5 ∧ a 4 = 9 ∧
      a 5 = 13 ∧ a 6 = 17 ∧ a 7 = 24 ∧ a 8 = 31 ∧ a 9 = 38 ∧ a 10 = 45

/-! ## Basic Properties -/

/-- By construction, R(n) < n at each new element of the sequence. -/
axiom repcount_below_at_elements (a : ℕ → ℕ) (h : IsRosenSequence a) (k : ℕ) (hk : 1 ≤ k) :
    repCount a k (a (k + 1)) < a (k + 1)

/-- By construction, R(x) ≥ x for all x between consecutive elements. -/
axiom repcount_above_between (a : ℕ → ℕ) (h : IsRosenSequence a) (k : ℕ) (hk : 1 ≤ k)
    (m : ℕ) (hm1 : a k < m) (hm2 : m < a (k + 1)) :
    repCount a k m ≥ m

/-! ## The Main Conjecture -/

/-- The full representation count over the infinite sequence. -/
def fullRepCount (a : ℕ → ℕ) (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).sum fun j =>
    if j = 0 then 0 else
    (Finset.Icc 0 j).filter (fun i => a i + a j ≤ x) |>.card

/-- Weak conjecture: R(x) = (1 + o(1))x. Erdős and Rosen
    could not even prove this. -/
axiom erdos_954_weak_conjecture (a : ℕ → ℕ) (h : IsRosenSequence a) :
    ∀ ε > 0, ∃ N, ∀ x ≥ N,
      (fullRepCount a x : ℤ) ≤ ((1 + ε) * x : ℤ)

/-- Strong conjecture: R(x) = x + O(x^{1/4 + o(1)}).
    The error term x^{1/4} is the natural guess from Sidon set theory. -/
axiom erdos_954_strong_conjecture (a : ℕ → ℕ) (h : IsRosenSequence a) :
    ∃ C : ℝ, ∀ x : ℕ, 1 ≤ x →
      |(fullRepCount a x : ℤ) - (x : ℤ)| ≤ C * (x : ℝ) ^ (1/4 : ℝ) * Real.log x

/-! ## Connection to Sidon Sets and B₂ Sequences -/

/-- A B₂ sequence (Sidon set): all pairwise sums are distinct. -/
def IsB2Sequence (a : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ i₁ j₁ i₂ j₂, i₁ ≤ j₁ → j₁ ≤ k → i₂ ≤ j₂ → j₂ ≤ k →
    a i₁ + a j₁ = a i₂ + a j₂ → (i₁ = i₂ ∧ j₁ = j₂)

/-- The Rosen sequence is a relaxation of B₂: instead of requiring
    all sums distinct, it ensures the representation count grows
    roughly linearly. A B₂ sequence has R(x) ~ √x, while
    Rosen's has R(x) ~ x. -/
axiom rosen_not_b2 (a : ℕ → ℕ) (h : IsRosenSequence a) :
    ∃ k, ¬IsB2Sequence a k

/-- Erdős–Turán conjecture (Problem #28): every B₂ sequence has
    unbounded representation function. Rosen's construction is
    related but distinct — it controls the cumulative count rather
    than individual representations. -/
axiom erdos_turan_context :
    ∀ a : ℕ → ℕ, (∀ k, IsB2Sequence a k) →
    ∀ B, ∃ n, fullRepCount a n > B
