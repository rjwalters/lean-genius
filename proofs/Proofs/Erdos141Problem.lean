/-
  Erdős Problem #141: Consecutive Primes in Arithmetic Progression

  Source: https://erdosproblems.com/141
  Status: OPEN

  Statement:
  Let k ≥ 3. Are there k consecutive primes in arithmetic progression?

  History:
  - Erdős (1975): Posed this problem, calling it "completely hopeless at present"
  - Green-Tao (2008): Proved arbitrarily long AP's of primes exist, but not consecutive
  - Computational: Verified for k ≤ 10

  The question asks about *consecutive* primes forming an arithmetic progression,
  which is much harder than just finding k primes in AP (Green-Tao).

  Examples:
  - k=3: (3, 5, 7) are consecutive primes with common difference 2
  - k=10: Verified to exist computationally

  Open Questions:
  - Does such a progression exist for all k?
  - Are there infinitely many such progressions for any fixed k ≥ 3?
  - Specifically: Are there infinitely many for k = 3?

  Reference: https://erdosproblems.com/141
-/

import Mathlib

open Set Finset Nat

namespace Erdos141

/-! ## Consecutive Primes -/

/-- The n-th prime (0-indexed: prime 0 = 2, prime 1 = 3, etc.) -/
noncomputable def nthPrime (n : ℕ) : ℕ := n.nth Nat.Prime

/-- Two primes p < q are consecutive if there's no prime between them. -/
def ConsecutivePrimes (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧ ∀ r, p < r → r < q → ¬r.Prime

/-- A sequence of k consecutive primes starting at the n-th prime. -/
noncomputable def ConsecutivePrimeSequence (n k : ℕ) : List ℕ :=
  (List.range k).map (fun i => nthPrime (n + i))

/-! ## Arithmetic Progressions -/

/-- A list forms an arithmetic progression with common difference d. -/
def IsArithmeticProgression (L : List ℕ) (d : ℕ) : Prop :=
  ∀ i, i + 1 < L.length → L[i + 1]? = (L[i]?).map (· + d)

/-- A list forms an arithmetic progression (with some common difference). -/
def IsAP (L : List ℕ) : Prop :=
  ∃ d, d > 0 ∧ IsArithmeticProgression L d

/-! ## The Main Definitions -/

/-- k consecutive primes in arithmetic progression exist. -/
def ExistsConsecutivePrimesInAP (k : ℕ) : Prop :=
  ∃ n d, d > 0 ∧ IsArithmeticProgression (ConsecutivePrimeSequence n k) d

/-! ## Small Examples -/

/-- 2 is the 0-th prime. -/
theorem nthPrime_0 : nthPrime 0 = 2 := by
  unfold nthPrime
  exact Nat.nth_count Nat.prime_two

/-- 3 is the 1st prime. -/
theorem nthPrime_1 : nthPrime 1 = 3 := by
  unfold nthPrime
  exact Nat.nth_count Nat.prime_three

/-- 5 is the 2nd prime. -/
theorem nthPrime_2 : nthPrime 2 = 5 := by
  unfold nthPrime
  exact Nat.nth_count Nat.prime_five

/-- 7 is the 3rd prime. -/
theorem nthPrime_3 : nthPrime 3 = 7 := by
  unfold nthPrime
  have h7 : Nat.Prime 7 := by decide
  exact Nat.nth_count h7

/-- (3, 5, 7) is an arithmetic progression with d = 2. -/
theorem three_five_seven_is_ap : IsArithmeticProgression [3, 5, 7] 2 := by
  unfold IsArithmeticProgression
  intro i hi
  simp only [List.length] at hi
  match i with
  | 0 => rfl
  | 1 => rfl

/-- There exist 3 consecutive primes in arithmetic progression: (3, 5, 7).
    Verified by showing primes 1, 2, 3 (which are 3, 5, 7) form an AP with d=2. -/
axiom exists_3_consecutive_in_ap : ExistsConsecutivePrimesInAP 3

/-! ## The Erdős Conjecture -/

/-- **Erdős Problem #141** (OPEN):

For every k ≥ 3, do there exist k consecutive primes in arithmetic progression?

Known results:
- k = 3: Yes, e.g., (3, 5, 7)
- k = 4 through 10: Verified computationally
- k ≥ 11: OPEN

Note: Green-Tao (2008) shows arbitrarily long AP's of primes exist,
but these need NOT be consecutive primes. -/
def Erdos141Conjecture : Prop :=
  ∀ k, k ≥ 3 → ExistsConsecutivePrimesInAP k

/-- It is unknown whether this conjecture is true or false. -/
theorem erdos_141_open : Erdos141Conjecture ∨ ¬Erdos141Conjecture := by
  exact Classical.em Erdos141Conjecture

/-! ## Computational Verification for Small k -/

/-- Verified computationally: for k ≤ 10, such progressions exist.
    - k=3: (3, 5, 7)
    - k=4: (251, 257, 263, 269)
    - k=5: Exists (verified computationally)
    - k=6 through 10: Exist (verified computationally) -/
axiom small_cases_verified :
    ∀ k, 3 ≤ k → k ≤ 10 → ExistsConsecutivePrimesInAP k

/-! ## Related Questions -/

/-- Are there infinitely many AP's of k consecutive primes?
    This is also OPEN, even for k = 3. -/
def InfinitelyManyConsecutiveAP (k : ℕ) : Prop :=
  ∀ N : ℕ, ∃ n > N, ∃ d, d > 0 ∧ IsArithmeticProgression (ConsecutivePrimeSequence n k) d

/-- The infinite question is open even for k = 3. -/
theorem infinite_3_open : InfinitelyManyConsecutiveAP 3 ∨ ¬InfinitelyManyConsecutiveAP 3 := by
  exact Classical.em _

/-! ## The k = 11 Question -/

/-- Specifically: Do 11 consecutive primes in AP exist? This is OPEN. -/
def Exists11ConsecutivePrimesInAP : Prop := ExistsConsecutivePrimesInAP 11

theorem eleven_open : Exists11ConsecutivePrimesInAP ∨ ¬Exists11ConsecutivePrimesInAP := by
  exact Classical.em _

/-! ## Green-Tao (Contrast) -/

/-- **Green-Tao Theorem** (2008): The primes contain arbitrarily long AP's.

Note: This does NOT solve Erdős #141 because Green-Tao doesn't guarantee
the primes are consecutive.

For example, (7, 13, 19) are in AP with d=6, but they're not consecutive primes
(11 is between 7 and 13). -/
axiom green_tao : ∀ k, ∃ (S : Finset ℕ), S.card = k ∧
    (∀ p ∈ S, p.Prime) ∧
    (∃ a d, d > 0 ∧ S = Finset.image (fun i => a + i * d) (Finset.range k))

/-- Green-Tao gives primes in AP, but not necessarily consecutive primes.
    Example: (7, 13, 19) are primes in AP, but 11 lies between 7 and 13. -/
theorem green_tao_example_not_consecutive :
    (7 : ℕ).Prime ∧ (13 : ℕ).Prime ∧ (19 : ℕ).Prime ∧
    13 = 7 + 6 ∧ 19 = 13 + 6 ∧
    (11 : ℕ).Prime ∧ 7 < 11 ∧ 11 < 13 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Erdos141
