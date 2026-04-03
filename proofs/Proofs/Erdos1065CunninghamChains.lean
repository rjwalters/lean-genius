import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-
Cunningham Chains and Form A Primes: Long Chain Existence
Open question from Erdős Problem #1065 (oq-06)

A **Cunningham chain of the first kind** is a sequence
  p₁, p₂ = 2p₁+1, p₃ = 2p₂+1, ..., pₙ = 2pₙ₋₁+1
where every term is prime. The smallest examples are:
  - Length 2: [2, 5], [3, 7], [5, 11], [11, 23], ...
  - Length 4: [2, 5, 11, 23]
  - Length 5: [2, 5, 11, 23, 47]
  - Length 6: [89, 179, 359, 719, 1439, 2879]

**Connection to Erdős #1065**: every element after the first in a Cunningham chain
is a *safe prime* (Form A with k = 1): p = 2q + 1 with both p and q prime.

**Open conjecture**: for every n, there exists a Cunningham chain of the first kind
of length n. If true, this would imply there are infinitely many safe primes,
confirming Conjecture A of Erdős #1065.

Reference: https://erdosproblems.com/1065
-/

namespace Erdos1065CunninghamChains

-- ## Definitions

/-- A safe prime: p = 2q + 1 with both p and q prime.
    Safe primes are exactly the k=1 Form A primes in Erdős #1065. -/
def IsSafePrime (p : ℕ) : Prop :=
  p.Prime ∧ ∃ q : ℕ, q.Prime ∧ p = 2 * q + 1

/-- A Sophie Germain prime: p is prime and 2p + 1 is also prime.
    These are precisely the non-last elements of a Cunningham chain. -/
def IsSophieGermain (p : ℕ) : Prop :=
  p.Prime ∧ (2 * p + 1).Prime

/-- A Cunningham chain of the first kind: a list of primes where
    each consecutive element is of the form 2p + 1.
    - Empty list and singleton are trivially chains.
    - For [p, q, ...]: p must be prime, q = 2p + 1, and (q :: ...) is a chain. -/
def IsCunninghamChain : List ℕ → Prop
  | [] => True
  | [p] => p.Prime
  | p :: q :: rest => p.Prime ∧ q = 2 * p + 1 ∧ IsCunninghamChain (q :: rest)

-- ## Verified Examples

/-- [2, 5] is a Cunningham chain of the first kind. -/
theorem chain_2_5 : IsCunninghamChain [2, 5] := by
  simp only [IsCunninghamChain]; norm_num

/-- [3, 7] is a Cunningham chain of the first kind. -/
theorem chain_3_7 : IsCunninghamChain [3, 7] := by
  simp only [IsCunninghamChain]; norm_num

/-- [5, 11] is a Cunningham chain of the first kind. -/
theorem chain_5_11 : IsCunninghamChain [5, 11] := by
  simp only [IsCunninghamChain]; norm_num

/-- [2, 5, 11] is a Cunningham chain of length 3. -/
theorem chain_2_5_11 : IsCunninghamChain [2, 5, 11] := by
  simp only [IsCunninghamChain]; norm_num

/-- [2, 5, 11, 23] is a Cunningham chain of length 4. -/
theorem chain_2_5_11_23 : IsCunninghamChain [2, 5, 11, 23] := by
  simp only [IsCunninghamChain]; norm_num

/-- [2, 5, 11, 23, 47] is a Cunningham chain of the first kind of length 5.
    Each link: 5 = 2·2+1, 11 = 2·5+1, 23 = 2·11+1, 47 = 2·23+1. All are prime. -/
theorem chain_2_5_11_23_47 : IsCunninghamChain [2, 5, 11, 23, 47] := by
  simp only [IsCunninghamChain]; norm_num

/-- [89, 179, 359, 719, 1439, 2879] is a Cunningham chain of length 6.
    Each link: 179=2·89+1, 359=2·179+1, 719=2·359+1, 1439=2·719+1, 2879=2·1439+1.
    All six are prime. -/
theorem chain_89_length6 : IsCunninghamChain [89, 179, 359, 719, 1439, 2879] := by
  simp only [IsCunninghamChain]; norm_num

-- ## Structural Theorems

/-- The head of any nonempty Cunningham chain is prime. -/
theorem chain_head_prime (p : ℕ) (rest : List ℕ)
    (hchain : IsCunninghamChain (p :: rest)) : p.Prime := by
  cases rest with
  | nil => exact hchain
  | cons q tail =>
    simp only [IsCunninghamChain] at hchain
    exact hchain.1

/-- All elements of a Cunningham chain are prime. -/
theorem chain_elements_prime : ∀ (chain : List ℕ),
    IsCunninghamChain chain → ∀ p ∈ chain, p.Prime := by
  intro chain
  induction chain with
  | nil => simp
  | cons hd tl ih =>
    intro hchain q hq
    simp only [List.mem_cons] at hq
    cases hq with
    | inl h => exact h ▸ chain_head_prime hd tl hchain
    | inr h =>
      cases tl with
      | nil => simp at h
      | cons r tail =>
        simp only [IsCunninghamChain] at hchain
        obtain ⟨_, _, htail⟩ := hchain
        exact ih htail q h

/-- The second element of a Cunningham chain is a safe prime. -/
theorem chain_second_is_safe (p q : ℕ) (rest : List ℕ)
    (hchain : IsCunninghamChain (p :: q :: rest)) : IsSafePrime q := by
  simp only [IsCunninghamChain] at hchain
  obtain ⟨hp, hq, hrest⟩ := hchain
  refine ⟨chain_head_prime q rest hrest, p, hp, ?_⟩
  omega

/-- The first element of a 2+ chain is a Sophie Germain prime. -/
theorem chain_head_is_sophie_germain (p q : ℕ) (rest : List ℕ)
    (hchain : IsCunninghamChain (p :: q :: rest)) : IsSophieGermain p := by
  simp only [IsCunninghamChain] at hchain
  obtain ⟨hp, hq, hrest⟩ := hchain
  exact ⟨hp, hq ▸ chain_head_prime q rest hrest⟩

/-- A Cunningham chain of length ≥ 2 contains at least one safe prime. -/
theorem chain_produces_safe_prime (chain : List ℕ)
    (hchain : IsCunninghamChain chain) (hlen : 2 ≤ chain.length) :
    ∃ q ∈ chain, IsSafePrime q := by
  cases chain with
  | nil => simp at hlen
  | cons p rest =>
    cases rest with
    | nil => simp at hlen
    | cons q tail =>
      refine ⟨q, ?_, chain_second_is_safe p q tail hchain⟩
      simp [List.mem_cons]

/-- Every safe prime is a Form A prime with k = 1:  p = 2^1 · q + 1. -/
theorem safe_prime_is_form_a (p : ℕ) (h : IsSafePrime p) :
    p.Prime ∧ ∃ q k : ℕ, q.Prime ∧ p = 2 ^ k * q + 1 := by
  obtain ⟨hp, q, hq, heq⟩ := h
  exact ⟨hp, q, 1, hq, by linarith⟩

-- ## The Open Conjecture

/-- **Cunningham chain conjecture of the first kind (open)**: for every n,
    there exists a Cunningham chain of length n.

    Known chains: length ≤ 14 have been found computationally. Arbitrarily
    long chains are expected to exist by probabilistic heuristics (analogous to
    the Hardy-Littlewood Conjecture F for safe primes), but no proof is known. -/
axiom cunningham_chain_conjecture :
    ∀ n : ℕ, ∃ chain : List ℕ, chain.length = n ∧ IsCunninghamChain chain

-- ## Connection to Erdős #1065

/-- If the Cunningham chain conjecture holds, then safe primes exist. -/
theorem cunningham_implies_safe_prime_exists :
    (∀ n : ℕ, ∃ chain : List ℕ, chain.length = n ∧ IsCunninghamChain chain) →
    ∃ p : ℕ, IsSafePrime p := by
  intro h
  obtain ⟨chain, hlen, hchain⟩ := h 2
  cases chain with
  | nil => simp at hlen
  | cons p rest =>
    cases rest with
    | nil => simp at hlen
    | cons q tail =>
      exact ⟨q, chain_second_is_safe p q tail hchain⟩

/-- If the Cunningham chain conjecture holds, then safe primes are infinite,
    confirming Conjecture A of Erdős #1065 (infinitely many Form A primes with k=1).

    **Proof sketch**: Suppose only N safe primes exist. Take a Cunningham chain
    of length N+2. The last N+1 elements are all safe primes (each = 2·prev+1 with
    prev prime). Chain elements are strictly increasing (each ≥ 2·prev > prev),
    so these N+1 safe primes are distinct. Contradicts N safe primes total.

    (HARD: full formalization requires additional inductive lemmas about chain
    cardinality and distinctness. Marked for Aristotle or future session.) -/
theorem cunningham_implies_infinite_safe_primes :
    (∀ n : ℕ, ∃ chain : List ℕ, chain.length = n ∧ IsCunninghamChain chain) →
    Set.Infinite {p : ℕ | IsSafePrime p} := by
  sorry

-- ## Known Safe Primes ≤ 100

/-- 5 is a safe prime: 5 = 2·2+1 with both 2 and 5 prime. -/
theorem safe_prime_5 : IsSafePrime 5 := ⟨by norm_num, 2, by norm_num, by norm_num⟩

/-- 7 is a safe prime: 7 = 2·3+1 with both 3 and 7 prime. -/
theorem safe_prime_7 : IsSafePrime 7 := ⟨by norm_num, 3, by norm_num, by norm_num⟩

/-- 11 is a safe prime: 11 = 2·5+1 with both 5 and 11 prime. -/
theorem safe_prime_11 : IsSafePrime 11 := ⟨by norm_num, 5, by norm_num, by norm_num⟩

/-- 23 is a safe prime: 23 = 2·11+1 with both 11 and 23 prime. -/
theorem safe_prime_23 : IsSafePrime 23 := ⟨by norm_num, 11, by norm_num, by norm_num⟩

/-- 47 is a safe prime: 47 = 2·23+1 with both 23 and 47 prime. -/
theorem safe_prime_47 : IsSafePrime 47 := ⟨by norm_num, 23, by norm_num, by norm_num⟩

/-- 59 is a safe prime: 59 = 2·29+1 with both 29 and 59 prime. -/
theorem safe_prime_59 : IsSafePrime 59 := ⟨by norm_num, 29, by norm_num, by norm_num⟩

/-- 83 is a safe prime: 83 = 2·41+1 with both 41 and 83 prime. -/
theorem safe_prime_83 : IsSafePrime 83 := ⟨by norm_num, 41, by norm_num, by norm_num⟩

/-- 2879 is a safe prime: 2879 = 2·1439+1 with both 1439 and 2879 prime.
    This is the last element of the length-6 chain starting at 89. -/
theorem safe_prime_2879 : IsSafePrime 2879 := ⟨by norm_num, 1439, by norm_num, by norm_num⟩

/-- Among primes ≤ 100, the safe primes are: 5, 7, 11, 23, 47, 59, 83. -/
theorem safe_primes_le_100 :
    ∀ p ∈ ([5, 7, 11, 23, 47, 59, 83] : List ℕ), IsSafePrime p := by
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact safe_prime_5
  · exact safe_prime_7
  · exact safe_prime_11
  · exact safe_prime_23
  · exact safe_prime_47
  · exact safe_prime_59
  · exact safe_prime_83

end Erdos1065CunninghamChains
