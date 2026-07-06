/-
Proof: Prime Gaps Are Unbounded (Arbitrarily Long Runs of Consecutive Composites)
Date: 2026-06-26
Research: infinitude-primes-oq-02
Method: Elementary factorial construction
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-
# Prime Gaps Are Unbounded

## What This Proves

The open question `infinitude-primes-oq-02` asks: *how large can gaps between
consecutive primes grow?*  The answer is: **without bound**.  We prove this in
two complementary forms, both via the classical elementary factorial
construction (no analytic number theory needed):

1. `exists_consecutive_composites` — for every `G` there is a block of `G`
   consecutive composite numbers, namely `(G+1)! + 2, …, (G+1)! + (G+1)`.

2. `exists_large_prime_gap` — for every `G` there are two *consecutive* primes
   `p < q` (no prime strictly between them) with `q - p ≥ G`.

## Why This Matters For the Gallery

The gallery already contains an extensive `bounded-prime-gaps` development
(admissible tuples, Maynard–Tao, bounded gaps `H`), which concerns the *small*
side of the gap spectrum.  The *large* side — that gaps are unbounded — has so
far appeared only as an unproved `axiom` (`large_prime_gaps_exist` in
`Erdos454Problem.lean`).  This file discharges that statement with a fully
machine-checked elementary proof.

## The Construction

For `2 ≤ j ≤ G+1`, the number `(G+1)! + j` is divisible by `j`: indeed
`j ∣ (G+1)!` because `j ≤ G+1`, and `j ∣ j`.  Since `1 < j < (G+1)! + j`, this
exhibits a nontrivial divisor, so `(G+1)! + j` is composite.  Letting `j` range
over `2, …, G+1` gives `G` consecutive composites.  For the consecutive-prime
form, we sandwich this composite block between the greatest prime below it and
the least prime above it.
-/

namespace PrimeGapsUnbounded

/-- For `2 ≤ j ≤ G + 1`, the number `(G+1)! + j` is composite.
    Witness divisor: `j` divides `(G+1)!` (since `j ≤ G+1`) and divides itself,
    hence divides the sum, with `1 < j < (G+1)! + j`. -/
theorem not_prime_factorial_add {G j : ℕ} (hj2 : 2 ≤ j) (hjG : j ≤ G + 1) :
    ¬ (Nat.factorial (G + 1) + j).Prime := by
  rw [Nat.not_prime_iff_exists_dvd_ne (show 2 ≤ Nat.factorial (G + 1) + j by omega)]
  refine ⟨j, ?_, ?_, ?_⟩
  · exact dvd_add (Nat.dvd_factorial (show 0 < j by omega) hjG) (dvd_refl j)
  · omega
  · have hfac : 0 < Nat.factorial (G + 1) := Nat.factorial_pos _
    omega

/-- **Arbitrarily long runs of consecutive composites.**

    For every `G` there exist `G` consecutive composite numbers, namely
    `(G+1)! + 2, (G+1)! + 3, …, (G+1)! + (G+1)`. -/
theorem exists_consecutive_composites (G : ℕ) :
    ∃ m, 2 ≤ m ∧ ∀ i, i < G → ¬ (m + i).Prime := by
  refine ⟨Nat.factorial (G + 1) + 2, ?_, ?_⟩
  · have := Nat.factorial_pos (G + 1); omega
  · intro i hi
    have hrw : Nat.factorial (G + 1) + 2 + i = Nat.factorial (G + 1) + (i + 2) := by ring
    rw [hrw]
    exact not_prime_factorial_add (by omega) (by omega)

/-- **Prime gaps are unbounded.**

    For every `G` there exist consecutive primes `p < q` — meaning no prime lies
    strictly between them — with gap `q - p ≥ G`.  Equivalently, the gap
    `p + G ≤ q` can be made as large as desired. -/
theorem exists_large_prime_gap (G : ℕ) :
    ∃ p q, p.Prime ∧ q.Prime ∧ p < q ∧ p + G ≤ q ∧
      ∀ k, p < k → k < q → ¬ k.Prime := by
  have hMpos : 0 < Nat.factorial (G + 1) := Nat.factorial_pos _
  -- The block `[M+2, M+G+1]` is prime-free.
  have hrun : ∀ k, Nat.factorial (G + 1) + 2 ≤ k → k ≤ Nat.factorial (G + 1) + G + 1 →
      ¬ k.Prime := by
    intro k hk1 hk2
    obtain ⟨i, rfl⟩ : ∃ i, k = Nat.factorial (G + 1) + 2 + i := ⟨k - (Nat.factorial (G + 1) + 2), by omega⟩
    have hrw : Nat.factorial (G + 1) + 2 + i = Nat.factorial (G + 1) + (i + 2) := by ring
    rw [hrw]
    exact not_prime_factorial_add (by omega) (by omega)
  -- `q` : the least prime `≥ M + 2`.
  have hex : ∃ x, Nat.factorial (G + 1) + 2 ≤ x ∧ x.Prime := by
    obtain ⟨x, hx1, hx2⟩ := Nat.exists_infinite_primes (Nat.factorial (G + 1) + 2)
    exact ⟨x, hx1, hx2⟩
  obtain ⟨q, hq_ge, hq_prime, hq_min⟩ :
      ∃ q, Nat.factorial (G + 1) + 2 ≤ q ∧ q.Prime ∧
        ∀ k, k < q → ¬ (Nat.factorial (G + 1) + 2 ≤ k ∧ k.Prime) := by
    exact ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      fun k hk => Nat.find_min hex hk⟩
  -- Because the block is prime-free, the least prime above it is `≥ M + G + 2`.
  have hq_big : Nat.factorial (G + 1) + G + 2 ≤ q := by
    by_contra h
    push_neg at h
    exact hrun q hq_ge (by omega) hq_prime
  -- `p` : the greatest prime `≤ M + 1`.
  obtain ⟨p, hp_le, hp_prime, hp_greatest⟩ :
      ∃ p, p ≤ Nat.factorial (G + 1) + 1 ∧ p.Prime ∧
        ∀ k, p < k → k ≤ Nat.factorial (G + 1) + 1 → ¬ k.Prime := by
    refine ⟨Nat.findGreatest Nat.Prime (Nat.factorial (G + 1) + 1), Nat.findGreatest_le _, ?_, ?_⟩
    · refine Nat.findGreatest_of_ne_zero rfl ?_
      have h2 : 2 ≤ Nat.findGreatest Nat.Prime (Nat.factorial (G + 1) + 1) :=
        Nat.le_findGreatest (by omega) Nat.prime_two
      omega
    · intro k hk hkb
      exact Nat.findGreatest_is_greatest hk hkb
  -- Assemble: `p` and `q` are consecutive primes with the required gap.
  refine ⟨p, q, hp_prime, hq_prime, by omega, by omega, ?_⟩
  intro k hpk hkq
  by_cases hk : k ≤ Nat.factorial (G + 1) + 1
  · exact hp_greatest k hpk hk
  · push_neg at hk
    intro hkp
    exact hq_min k hkq ⟨by omega, hkp⟩

/-- Demonstration: there are 100 consecutive composite numbers. -/
example : ∃ m, 2 ≤ m ∧ ∀ i, i < 100 → ¬ (m + i).Prime :=
  exists_consecutive_composites 100

/-- Demonstration: some pair of consecutive primes differs by at least 1000. -/
example : ∃ p q, p.Prime ∧ q.Prime ∧ p < q ∧ p + 1000 ≤ q ∧
    ∀ k, p < k → k < q → ¬ k.Prime :=
  exists_large_prime_gap 1000

end PrimeGapsUnbounded
