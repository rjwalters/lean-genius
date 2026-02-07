/-
Erdős Problem #852 — Maximal Runs of Distinct Consecutive Prime Gaps

Let dₙ = pₙ₊₁ − pₙ be the n-th prime gap. Define h(x) as the maximal
length such that for some n with pₙ < x, the gaps dₙ, dₙ₊₁, ..., dₙ₊ₕ₍ₓ₎₋₁
are all distinct.

Erdős asked:
(1) Is h(x) > (log x)^c for some constant c > 0?
(2) Is h(x) = o(log x)?

Brun's sieve implies h(x) → ∞ as x → ∞.

**Status:** OPEN

**Reference:** erdosproblems.com/852, Er85c
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-
## Prime Sequence and Gaps (Axiomatized)
-/

/-- The n-th prime (0-indexed: nthPrime 0 = 2, nthPrime 1 = 3, ...) -/
axiom nthPrime : ℕ → ℕ
axiom nthPrime_prime (n : ℕ) : Nat.Prime (nthPrime n)
axiom nthPrime_strictMono : StrictMono nthPrime
axiom nthPrime_initial : nthPrime 0 = 2 ∧ nthPrime 1 = 3

/-- The n-th prime gap: dₙ = pₙ₊₁ − pₙ -/
def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- Prime gaps are positive (since nthPrime is strictly monotone). -/
theorem primeGap_pos (n : ℕ) : 0 < primeGap n := by
  unfold primeGap
  have := nthPrime_strictMono (Nat.lt_succ_of_le (le_refl n))
  omega

/-- nthPrime is monotone (follows from strict monotonicity). -/
theorem nthPrime_mono : Monotone nthPrime :=
  nthPrime_strictMono.monotone

/-- nthPrime n ≥ 2 for all n (all primes are ≥ 2). -/
theorem nthPrime_ge_two (n : ℕ) : nthPrime n ≥ 2 :=
  (nthPrime_prime n).two_le

/-- The first prime gap d₀ = p₁ - p₀ = 3 - 2 = 1. -/
theorem primeGap_zero : primeGap 0 = 1 := by
  unfold primeGap
  have := nthPrime_initial
  rw [this.1, this.2]

/-
## Distinct Gap Runs
-/

/-- A run of gaps starting at index n has all distinct values up to length k. -/
def IsDistinctRun (n k : ℕ) : Prop :=
  ∀ i j : ℕ, i < k → j < k → i ≠ j → primeGap (n + i) ≠ primeGap (n + j)

/-- An empty run is trivially distinct. -/
theorem isDistinctRun_zero (n : ℕ) : IsDistinctRun n 0 := by
  intro i j hi; omega

/-- A single-element run is always distinct. -/
theorem isDistinctRun_one (n : ℕ) : IsDistinctRun n 1 := by
  intro i j hi hj hne
  omega

/-- If a run of length k is distinct, then any prefix is distinct. -/
theorem isDistinctRun_prefix (n k₁ k₂ : ℕ) (h : k₁ ≤ k₂)
    (hk : IsDistinctRun n k₂) : IsDistinctRun n k₁ := by
  intro i j hi hj hne
  exact hk i j (lt_of_lt_of_le hi h) (lt_of_lt_of_le hj h) hne

/-- If a run of length k is distinct, dropping the first element
    gives a distinct run of length k-1. -/
theorem isDistinctRun_tail (n k : ℕ) (hk : 1 ≤ k)
    (h : IsDistinctRun n k) : IsDistinctRun (n + 1) (k - 1) := by
  intro i j hi hj hne
  have := h (i + 1) (j + 1) (by omega) (by omega) (by omega)
  simp only [Nat.add_assoc] at this
  exact this

/-- Combining: IsDistinctRun is downward-closed in k. -/
theorem isDistinctRun_le {n k₁ k₂ : ℕ} (hle : k₁ ≤ k₂)
    (h : IsDistinctRun n k₂) : IsDistinctRun n k₁ :=
  isDistinctRun_prefix n k₁ k₂ hle h

/-
## h(x): Maximal Distinct Run Length (Axiomatized)
-/

/-- h(x): maximal length of a run of distinct consecutive gaps
    among primes pₙ < x. -/
axiom maxDistinctRun : ℕ → ℕ

/-- h(x) is achieved by some starting index with pₙ < x. -/
axiom maxDistinctRun_witness (x : ℕ) (hx : 2 ≤ x) :
  ∃ n : ℕ, nthPrime n < x ∧ IsDistinctRun n (maxDistinctRun x)

/-- h(x) is indeed maximal. -/
axiom maxDistinctRun_optimal (x : ℕ) (n k : ℕ)
    (hn : nthPrime n < x) (hk : IsDistinctRun n k) :
  k ≤ maxDistinctRun x

/-
## Properties of h(x)
-/

/-- h(x) ≥ 1 for x ≥ 3 (there always exists at least a single gap). -/
theorem maxDistinctRun_ge_one (x : ℕ) (hx : 3 ≤ x) :
    1 ≤ maxDistinctRun x := by
  have h2 : nthPrime 0 < x := by
    have := nthPrime_initial.1; omega
  exact maxDistinctRun_optimal x 0 1 h2 (isDistinctRun_one 0)

/-- h(x) is non-decreasing: if x ≤ y, then h(x) ≤ h(y). -/
theorem maxDistinctRun_mono (x y : ℕ) (hx : 2 ≤ x) (hxy : x ≤ y) :
    maxDistinctRun x ≤ maxDistinctRun y := by
  obtain ⟨n, hn, hdist⟩ := maxDistinctRun_witness x hx
  exact maxDistinctRun_optimal y n (maxDistinctRun x)
    (lt_of_lt_of_le hn hxy) hdist

/-
## Brun's Sieve Result
-/

/-- Brun's sieve: h(x) → ∞ as x → ∞. -/
axiom brun_sieve_divergence :
  ∀ C : ℕ, ∃ X : ℕ, ∀ x : ℕ, X ≤ x → C ≤ maxDistinctRun x

/-
## Erdős Conjectures (OPEN)
-/

/-- Erdős Problem 852, Part 1: h(x) > (log x)^c for some constant c > 0. -/
axiom ErdosProblem852_lower :
  ∃ c : ℝ, 0 < c ∧ ∃ X : ℕ, ∀ x ≥ X,
    (Real.log x) ^ c < (maxDistinctRun x : ℝ)

/-- Erdős Problem 852, Part 2: h(x) = o(log x). -/
axiom ErdosProblem852_upper :
  ∀ ε : ℝ, 0 < ε → ∃ X : ℕ, ∀ x ≥ X,
    (maxDistinctRun x : ℝ) < ε * Real.log x

/-
## Pigeonhole Upper Bound
-/

/-- Among primes p ≤ x, the gaps dₙ satisfy dₙ ≤ x. So a distinct
    run can have at most x different values. This gives h(x) ≤ x. -/
axiom maxDistinctRun_le_x (x : ℕ) (hx : 2 ≤ x) :
  maxDistinctRun x ≤ x

/-- If all gaps in a distinct run of length k are ≤ M, then k ≤ M
    (by pigeonhole: k distinct positive values in {1, ..., M} implies k ≤ M). -/
axiom distinct_run_bounded_by_max_gap (n k M : ℕ)
    (hk : IsDistinctRun n k)
    (hbound : ∀ i, i < k → primeGap (n + i) ≤ M)
    (hpos : ∀ i, i < k → 0 < primeGap (n + i)) :
    k ≤ M

/-
## Problem Status
-/

def erdos_852_status : String := "OPEN"
