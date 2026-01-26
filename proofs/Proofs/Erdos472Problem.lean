/-!
# Erdős Problem 472: Ulam Prime Sequences

Given an initial finite sequence of primes `q₁ < ⋯ < qₘ`, extend it so
that `q_{n+1}` is the smallest prime of the form `qₙ + qᵢ − 1` for some
`i ≤ n`. Does there exist an initial sequence such that the resulting
sequence is infinite?

A problem due to Ulam. Starting with `3, 5`, the sequence continues
`3, 5, 7, 11, 13, 17, …` and may be infinite.

*Reference:* [erdosproblems.com/472](https://www.erdosproblems.com/472),
Erdős–Graham (1980).
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-! ## Ulam prime extension -/

/-- Given a list of primes and its last element, a candidate next prime is
`last + qᵢ - 1` for some `qᵢ` in the list, and must be prime. -/
def IsCandidateNext (seq : List ℕ) (last : ℕ) (p : ℕ) : Prop :=
    p.Prime ∧ ∃ q ∈ seq, p = last + q - 1

/-- An Ulam prime sequence starting from a seed: an infinite function
`ℕ → ℕ` where the first `m` values match the seed, each value is prime,
the sequence is strictly increasing, and each `f(n+1)` is the smallest
prime of the form `f(n) + f(i) - 1` for some `i ≤ n`. -/
def IsUlamPrimeSeq (seed : List ℕ) (f : ℕ → ℕ) : Prop :=
    -- seed values match
    (∀ i : Fin seed.length, f i.val = seed.get i) ∧
    -- all values are prime
    (∀ n : ℕ, (f n).Prime) ∧
    -- strictly increasing
    (∀ n : ℕ, f n < f (n + 1)) ∧
    -- extension rule: f(n+1) is the smallest prime of the form f(n) + f(i) - 1
    (∀ n : ℕ, seed.length - 1 ≤ n →
      IsCandidateNext (List.ofFn (fun i : Fin (n + 1) => f i)) (f n) (f (n + 1)) ∧
      ∀ p : ℕ, p < f (n + 1) →
        IsCandidateNext (List.ofFn (fun i : Fin (n + 1) => f i)) (f n) p → False)

/-! ## Main conjecture -/

/-- Erdős Problem 472 (Ulam): There exists a finite seed of primes such
that the Ulam prime extension produces an infinite sequence. -/
def ErdosProblem472 : Prop :=
    ∃ (seed : List ℕ),
      (∀ p ∈ seed, p.Prime) ∧
      seed.length ≥ 2 ∧
      seed.Chain' (· < ·) ∧
      ∃ f : ℕ → ℕ, IsUlamPrimeSeq seed f

/-! ## Known example -/

/-- Starting with `[3, 5]`, the sequence `3, 5, 7, 11, 13, 17, …` is
conjectured to be an infinite Ulam prime sequence. -/
def ulamSeed35 : List ℕ := [3, 5]

/-- The seed `[3, 5]` consists of primes. -/
axiom ulamSeed35_prime : ∀ p ∈ ulamSeed35, p.Prime

/-! ## Basic properties -/

/-- In any Ulam prime sequence, consecutive differences are at least 2
(since all terms are prime and increasing). -/
axiom ulam_seq_gap (seed : List ℕ) (f : ℕ → ℕ) (hf : IsUlamPrimeSeq seed f)
    (n : ℕ) : f n + 2 ≤ f (n + 1) ∨ (f n = 2 ∧ f (n + 1) = 3)

/-- The candidate `f(n) + f(n) - 1 = 2f(n) - 1` is always odd for `f(n) ≥ 2`. -/
axiom candidate_self_odd (p : ℕ) (hp : 2 ≤ p) : ¬Even (p + p - 1)
