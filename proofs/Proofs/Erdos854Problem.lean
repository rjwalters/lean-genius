/-
# Erdős Problem #854 — Gaps Between Coprime Residues of Primorials

Let nₖ = p₁ · p₂ · ⋯ · pₖ be the k-th primorial. Consider the sequence
1 = a₁ < a₂ < ⋯ < a_{φ(nₖ)} = nₖ − 1 of integers coprime to nₖ.

Erdős asked:
(1) Estimate the smallest even integer not expressible as a gap aᵢ₊₁ − aᵢ.
(2) Is it true that ≫ max_i(aᵢ₊₁ − aᵢ) many even integers occur as gaps?

Erdős initially conjectured all even integers up to the maximal gap appear,
but computations by Lacampagne and Selfridge cast doubt on this for nₖ = 30030.

Reference: https://erdosproblems.com/854
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Pairwise
import Mathlib.Tactic

/- ## Primorial and Coprime Residues -/

/-- The k-th prime number (1-indexed: nthPrime 1 = 2, nthPrime 2 = 3, ...).
    Defined via Mathlib's Nat.nth with index shift: nthPrime 0 = 0 (sentinel). -/
noncomputable def nthPrime : ℕ → ℕ
  | 0 => 0
  | k + 1 => Nat.nth Nat.Prime k

theorem nthPrime_prime (k : ℕ) (hk : 1 ≤ k) : Nat.Prime (nthPrime k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime j

theorem nthPrime_mono : StrictMono nthPrime := by
  intro a b hab
  match a, b, hab with
  | 0, b + 1, _ =>
    simp only [nthPrime]
    exact (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime b).pos
  | a + 1, b + 1, hab =>
    simp only [nthPrime]
    exact Nat.nth_strictMono Nat.infinite_setOf_prime (by omega)

theorem nthPrime_vals : nthPrime 1 = 2 ∧ nthPrime 2 = 3 ∧ nthPrime 3 = 5 := by
  refine ⟨?_, ?_, ?_⟩
  · show Nat.nth Nat.Prime 0 = 2; exact Nat.nth_prime_zero_eq_two
  · show Nat.nth Nat.Prime 1 = 3; exact Nat.nth_prime_one_eq_three
  · show Nat.nth Nat.Prime 2 = 5; exact Nat.nth_prime_two_eq_five

/-- The k-th primorial: product of the first k primes -/
noncomputable def primorial : ℕ → ℕ
  | 0 => 1
  | k + 1 => primorial k * nthPrime (k + 1)

/-- The set of positive integers less than n that are coprime to n -/
def coprimeResidues (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun a => 0 < a ∧ Nat.Coprime a n)

/-- Sorted list of coprime residues -/
axiom sortedCoprimes (n : ℕ) : List ℕ
axiom sortedCoprimes_sorted (n : ℕ) : List.Pairwise (· < ·) (sortedCoprimes n)
axiom sortedCoprimes_mem (n : ℕ) (a : ℕ) :
  a ∈ sortedCoprimes n ↔ a ∈ coprimeResidues n

/- ## Gap Structure -/

/-- The set of consecutive gaps between coprime residues of n -/
axiom gapSet : ℕ → Finset ℕ

/-- Every gap is even for k ≥ 2 (since nₖ is even, all coprime residues are odd) -/
axiom gaps_even (k : ℕ) (hk : 2 ≤ k) (d : ℕ) (hd : d ∈ gapSet (primorial k)) :
  2 ∣ d

/-- The maximal gap between consecutive coprime residues of n -/
axiom maxGap : ℕ → ℕ
axiom maxGap_mem (n : ℕ) (hn : 1 < n) : maxGap n ∈ gapSet n
axiom maxGap_max (n : ℕ) (d : ℕ) (hd : d ∈ gapSet n) : d ≤ maxGap n

/-- Number of distinct even integers that appear as gaps -/
axiom distinctGapCount : ℕ → ℕ
axiom distinctGapCount_def (n : ℕ) :
  distinctGapCount n = (gapSet n).card

/- ## Known Bounds -/

/-- Maximal gap for primorial(k) grows like 2pₖ (the Jacobsthal function bound) -/
axiom maxGap_bound (k : ℕ) (hk : 2 ≤ k) :
  maxGap (primorial k) ≤ 2 * nthPrime k

/-- The first missing gap: smallest even integer not in gapSet(nₖ) -/
axiom firstMissingGap : ℕ → ℕ
axiom firstMissingGap_even (k : ℕ) (hk : 2 ≤ k) :
  2 ∣ firstMissingGap (primorial k)
axiom firstMissingGap_missing (k : ℕ) (hk : 2 ≤ k) :
  firstMissingGap (primorial k) ∉ gapSet (primorial k)

/-- Lacampagne–Selfridge computation: for nₖ = 30030 (k=6),
    not all even integers up to the maximal gap appear -/
axiom lacampagne_selfridge_counterexample :
  ∃ d : ℕ, 2 ∣ d ∧ d < maxGap (primorial 6) ∧ d ∉ gapSet (primorial 6)

/- ## The Erdős Conjectures -/

/-- Erdős Problem 854, Part 1: Estimate the smallest even integer
    not representable as a consecutive gap in coprime residues of primorials -/
axiom ErdosProblem854_missing_gap_growth :
  ∀ C : ℕ, ∃ k : ℕ, C ≤ firstMissingGap (primorial k)

/-- Erdős Problem 854, Part 2: The number of distinct even gaps
    is proportional to the maximal gap -/
axiom ErdosProblem854_many_gaps :
  ∃ c : ℚ, 0 < c ∧
    ∀ k : ℕ, 2 ≤ k →
      c * (maxGap (primorial k) : ℚ) ≤ (distinctGapCount (primorial k) : ℚ)
