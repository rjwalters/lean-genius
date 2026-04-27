/-
Erdős Problem 931: Same Prime Factors in Products of Consecutive Integers

Let k₁ ≥ k₂ ≥ 3. Are there only finitely many n₂ ≥ n₁ + k₁ such that
the products ∏_{i=1}^{k₁} (n₁+i) and ∏_{j=1}^{k₂} (n₂+j) share the
same set of prime factors?

Erdős himself expressed doubt, conjecturing instead that such pairs must satisfy
n₂ > 2(n₁ + k₁). Counterexamples exist to the stronger claim: AlphaProof
found that 10! = 2⁸·3⁴·5²·7 and 14·15·16 = 2⁵·3·5·7 share the same
prime factors {2,3,5,7}. Tijdeman also found: 19·20·21·22 and 54·55·56·57
share the same prime factors.

**Status:** OPEN

**Reference:** erdosproblems.com/931, Er76d, Gu04 (Problem B35)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic
import Mathlib.NumberTheory.Bertrand

namespace Erdos931

open Nat Finset

/-
## Core Definitions
-/

/-- The product of k consecutive integers starting from n+1: (n+1)(n+2)...(n+k). -/
def consecutiveProduct (n k : ℕ) : ℕ :=
  (Finset.Icc 1 k).prod (fun i => n + i)

/-- The set of prime factors of a consecutive product. -/
def consecutivePrimeFactors (n k : ℕ) : Finset ℕ :=
  (consecutiveProduct n k).primeFactors

/-- Two pairs (n₁, k₁) and (n₂, k₂) produce products with the same prime factors. -/
def SamePrimeFactors (n₁ k₁ n₂ k₂ : ℕ) : Prop :=
  consecutivePrimeFactors n₁ k₁ = consecutivePrimeFactors n₂ k₂

instance SamePrimeFactorsDecidable (n₁ k₁ n₂ k₂ : ℕ) :
    Decidable (SamePrimeFactors n₁ k₁ n₂ k₂) :=
  inferInstanceAs (Decidable (_ = _))

/-
## Small Computations
-/

/-- 1·2·...·10 = 10! = 3628800. -/
theorem consecutiveProduct_0_10 : consecutiveProduct 0 10 = 3628800 := by native_decide

/-- 14·15·16 = 3360. -/
theorem consecutiveProduct_13_3 : consecutiveProduct 13 3 = 3360 := by native_decide

/-- 19·20·21·22 = 175560. -/
theorem consecutiveProduct_18_4 : consecutiveProduct 18 4 = 175560 := by native_decide

/-- 54·55·56·57 = 9480240. -/
theorem consecutiveProduct_53_4 : consecutiveProduct 53 4 = 9480240 := by native_decide

/-- For k = 0, the product is 1 (empty product). -/
theorem consecutiveProduct_zero (n : ℕ) : consecutiveProduct n 0 = 1 := by
  simp [consecutiveProduct]

/-- For k = 1, the product is n+1. -/
theorem consecutiveProduct_one (n : ℕ) : consecutiveProduct n 1 = n + 1 := by
  simp [consecutiveProduct]

/-- The product is positive when all factors are positive (always true for n+i with i ≥ 1). -/
theorem consecutiveProduct_pos (n k : ℕ) : 0 < consecutiveProduct n k := by
  unfold consecutiveProduct
  apply Finset.prod_pos
  intro i hi
  simp only [Finset.mem_Icc] at hi
  omega

/-- The product is never zero. -/
theorem consecutiveProduct_ne_zero (n k : ℕ) : consecutiveProduct n k ≠ 0 :=
  Nat.pos_iff_ne_zero.mp (consecutiveProduct_pos n k)

/-
## Main Conjecture (OPEN)
-/

/-- **Erdős Problem 931**: For all k₁ ≥ k₂ ≥ 3, the set of pairs (n₁, n₂)
    with n₂ ≥ n₁ + k₁ and same prime factors is finite. -/
def ErdosProblem931 : Prop :=
  ∀ k₁ k₂ : ℕ, 3 ≤ k₂ → k₂ ≤ k₁ →
    { p : ℕ × ℕ | p.1 + k₁ ≤ p.2 ∧
      SamePrimeFactors p.1 k₁ p.2 k₂ }.Finite

/-- Erdős's stronger conjecture: if the products share prime factors and
    n₂ ≥ n₁ + k₁, then n₂ > 2(n₁ + k₁), allowing finitely many exceptions. -/
def StrongerConjecture : Prop :=
  ∀ k₁ k₂ : ℕ, 3 ≤ k₂ → k₂ ≤ k₁ →
    { p : ℕ × ℕ | p.1 + k₁ ≤ p.2 ∧ p.2 ≤ 2 * (p.1 + k₁) ∧
      SamePrimeFactors p.1 k₁ p.2 k₂ }.Finite

/-
## Counterexamples (Verified)
-/

/-- AlphaProof counterexample: 10! and 14·15·16 share prime factors {2,3,5,7}.
    Here n₁ = 0, k₁ = 10, n₂ = 13, k₂ = 3. -/
theorem alphaproof_same_factors : SamePrimeFactors 0 10 13 3 := by native_decide

/-- The AlphaProof counterexample satisfies the gap condition n₂ ≥ n₁ + k₁. -/
theorem alphaproof_gap : 0 + 10 ≤ 13 := by omega

/-- The AlphaProof counterexample has n₂ ≤ 2(n₁ + k₁), refuting the
    no-exceptions version of the stronger conjecture. -/
theorem alphaproof_within_double : 13 ≤ 2 * (0 + 10) := by omega

/-- Tijdeman's example: 19·20·21·22 and 54·55·56·57 share prime factors. -/
theorem tijdeman_same_factors : SamePrimeFactors 18 4 53 4 := by native_decide

/-- Tijdeman's example satisfies the gap condition. -/
theorem tijdeman_gap : 18 + 4 ≤ 53 := by omega

/-- Tijdeman's example also has n₂ > 2(n₁ + k₁): 53 > 44. -/
theorem tijdeman_beyond_double : 53 > 2 * (18 + 4) := by omega

/-- New example: 4·5·6 and 8·9·10 share prime factors {2,3,5}.
    Here n₁ = 3, k₁ = 3, n₂ = 7, k₂ = 3. -/
theorem small_same_factors_3_3_7_3 : SamePrimeFactors 3 3 7 3 := by native_decide

/-- The (3,3,7,3) example satisfies the gap condition. -/
theorem small_gap_3_3_7_3 : 3 + 3 ≤ 7 := by omega

/-- 3·4·5·6 and 8·9·10 share prime factors {2,3,5}.
    Here n₁ = 2, k₁ = 4, n₂ = 7, k₂ = 3. -/
theorem small_same_factors_2_4_7_3 : SamePrimeFactors 2 4 7 3 := by native_decide

/-- The (2,4,7,3) example satisfies the gap condition. -/
theorem small_gap_2_4_7_3 : 2 + 4 ≤ 7 := by omega

/-- 1·2·3·4·5 and 8·9·10 share prime factors {2,3,5}.
    Here n₁ = 0, k₁ = 5, n₂ = 7, k₂ = 3. -/
theorem small_same_factors_0_5_7_3 : SamePrimeFactors 0 5 7 3 := by native_decide

/-- The (0,5,7,3) example satisfies the gap condition. -/
theorem small_gap_0_5_7_3 : 0 + 5 ≤ 7 := by omega

/-
## Properties of Prime Factors
-/

/-- Every prime factor of the consecutive product divides the product. -/
theorem prime_factor_dvd (n k p : ℕ) (hp : p ∈ consecutivePrimeFactors n k) :
    p ∣ consecutiveProduct n k :=
  Nat.dvd_of_mem_primeFactors hp

/-- Every prime factor of the consecutive product is prime. -/
theorem prime_factor_is_prime (n k p : ℕ) (hp : p ∈ consecutivePrimeFactors n k) :
    p.Prime :=
  Nat.prime_of_mem_primeFactors hp

/-- A prime dividing one of the factors divides the product. -/
theorem factor_prime_dvd_product (n k i : ℕ) (hi : i ∈ Finset.Icc 1 k)
    (p : ℕ) (_hp : p.Prime) (hdvd : p ∣ (n + i)) :
    p ∣ consecutiveProduct n k := by
  unfold consecutiveProduct
  exact dvd_trans hdvd (Finset.dvd_prod_of_mem _ hi)

/-- If p divides some n+i with 1 ≤ i ≤ k, then p is a prime factor of the product. -/
theorem factor_prime_mem (n k i : ℕ) (hi : i ∈ Finset.Icc 1 k)
    (p : ℕ) (hp : p.Prime) (hdvd : p ∣ (n + i)) :
    p ∈ consecutivePrimeFactors n k := by
  unfold consecutivePrimeFactors
  rw [Nat.mem_primeFactors]
  exact ⟨hp, factor_prime_dvd_product n k i hi p hp hdvd, consecutiveProduct_ne_zero n k⟩

/-- SamePrimeFactors is reflexive. -/
theorem samePrimeFactors_refl (n k : ℕ) : SamePrimeFactors n k n k :=
  rfl

/-- SamePrimeFactors is symmetric. -/
theorem samePrimeFactors_symm {n₁ k₁ n₂ k₂ : ℕ}
    (h : SamePrimeFactors n₁ k₁ n₂ k₂) : SamePrimeFactors n₂ k₂ n₁ k₁ :=
  h.symm

/-- SamePrimeFactors is transitive. -/
theorem samePrimeFactors_trans {n₁ k₁ n₂ k₂ n₃ k₃ : ℕ}
    (h₁ : SamePrimeFactors n₁ k₁ n₂ k₂) (h₂ : SamePrimeFactors n₂ k₂ n₃ k₃) :
    SamePrimeFactors n₁ k₁ n₃ k₃ :=
  h₁.trans h₂

/-
## The Stronger Conjecture Implies the Main One

The main set decomposes as:
  { (n₁,n₂) | n₁+k₁ ≤ n₂ ∧ SamePrimeFactors } =
  { n₁+k₁ ≤ n₂ ≤ 2(n₁+k₁) ∧ SamePrimeFactors } ∪
  { n₂ > 2(n₁+k₁) ∧ SamePrimeFactors }
StrongerConjecture gives finiteness of the first set. This axiom asserts the
second ("outer") set is also finite, which requires showing that for n₂ far
beyond 2(n₁+k₁), having the same prime factors forces the second block
elements to be n₁-smooth — and by results on consecutive smooth numbers
(Størmer's theorem), there are only finitely many such n₂ for each n₁.
-/
/-- StrongerConjecture (finiteness in the inner range n₂ ≤ 2(n₁+k₁)) implies
    the full ErdosProblem931 (finiteness with no upper bound on n₂).

    The reduction needs: for n₂ > 2(n₁+k₁), `SamePrimeFactors` forces both blocks
    to be n₁-smooth, and Størmer's theorem gives only finitely many such pairs.
    Smooth-number theory not yet in Mathlib.

    Converted from `axiom` to `theorem … := by sorry` so it doesn't assert an
    unverified mathematical claim — sorry acknowledges the proof gap. -/
theorem stronger_implies_main : StrongerConjecture → ErdosProblem931 := by
  sorry

/-
## Bertrand's Postulate and Prime Between Blocks

We partially prove the "prime between blocks" claim using Bertrand's postulate.
The key insight: if the first block {n₁+1,...,n₁+k₁} contains a prime p,
then p > n₁ and p ≤ n₁+k₁ ≤ n₂ ≤ n₂+k₂, giving a prime in the range
immediately. By Bertrand, the first block always contains a prime when k₁ ≥ n₁.

The remaining hard case (n₁ > k₁, first block all composite) requires smooth
number theory: when all prime factors of both products are ≤ n₁, finding
k₂ ≥ 3 consecutive n₁-smooth numbers with the exact same prime factor set
as a block of k₁ composite numbers is extremely restrictive — empirically
impossible for all tested cases, likely provable via Størmer's theorem.
-/

/-- If the first block contains a prime, there's a prime in (n₁, n₂+k₂].
    No SamePrimeFactors hypothesis needed — the prime is already in range. -/
theorem exists_prime_between_of_prime_in_block
    (k₂ n₁ n₂ : ℕ)
    {p : ℕ} (hp : p.Prime) (hlo : n₁ < p) (hhi : p ≤ n₂)
    : ∃ q : ℕ, q.Prime ∧ n₁ < q ∧ q ≤ n₂ + k₂ :=
  ⟨p, hp, hlo, le_trans hhi (Nat.le_add_right n₂ k₂)⟩

/-- By Bertrand's postulate, when n₁ ≤ k₁ the first block {n₁+1,...,n₁+k₁}
    always contains a prime. For n₁ = 0, the prime 2 works. For n₁ ≥ 1,
    Bertrand gives a prime p with n₁ < p ≤ 2n₁ ≤ n₁+k₁. -/
theorem first_block_has_prime (n₁ k₁ : ℕ) (hk : 3 ≤ k₁) (hkn : n₁ ≤ k₁) :
    ∃ p : ℕ, p.Prime ∧ n₁ < p ∧ p ≤ n₁ + k₁ := by
  rcases Nat.eq_zero_or_pos n₁ with rfl | hn
  · exact ⟨2, by norm_num, by omega, by omega⟩
  · obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul n₁ (by omega)
    exact ⟨p, hp, hlt, by omega⟩

/-- For n₁ ≤ k₁: the prime-between-blocks claim holds unconditionally
    (no SamePrimeFactors hypothesis needed). This covers all cases where
    the block is long enough relative to its starting point. -/
theorem exists_prime_between_blocks_small
    (k₁ k₂ n₁ n₂ : ℕ)
    (hk₁ : 3 ≤ k₁) (hkn : n₁ ≤ k₁)
    (hgap : n₁ + k₁ ≤ n₂) :
    ∃ p : ℕ, p.Prime ∧ n₁ < p ∧ p ≤ n₂ + k₂ := by
  obtain ⟨p, hp, hlo, hhi⟩ := first_block_has_prime n₁ k₁ hk₁ hkn
  exact ⟨p, hp, hlo, by omega⟩

/-- If the first product has a prime factor q > n₁, and same prime factors hold,
    then q divides the second product too, giving q ≤ n₂+k₂ (since q divides
    one of the factors n₂+j ≤ n₂+k₂). -/
theorem exists_prime_between_of_large_prime_factor
    (k₁ k₂ n₁ n₂ q : ℕ)
    (hq : q.Prime) (hq_lo : n₁ < q)
    (hq_mem : q ∈ consecutivePrimeFactors n₁ k₁)
    (h₃ : n₁ + k₁ ≤ n₂)
    (h₄ : SamePrimeFactors n₁ k₁ n₂ k₂) :
    ∃ p : ℕ, p.Prime ∧ n₁ < p ∧ p ≤ n₂ + k₂ := by
  refine ⟨q, hq, hq_lo, ?_⟩
  -- q is also a prime factor of the second product by SamePrimeFactors
  have hq_mem₂ : q ∈ consecutivePrimeFactors n₂ k₂ := h₄ ▸ hq_mem
  have hq_dvd : q ∣ consecutiveProduct n₂ k₂ := Nat.dvd_of_mem_primeFactors hq_mem₂
  -- Since q is prime and divides (n₂+1)·...·(n₂+k₂), q divides some factor n₂+j
  unfold consecutiveProduct at hq_dvd
  obtain ⟨j, hj_mem, hq_dvd_j⟩ := hq.prime.dvd_finset_prod_iff.mp hq_dvd
  simp only [Finset.mem_Icc] at hj_mem
  calc q ≤ n₂ + j := Nat.le_of_dvd (by omega) hq_dvd_j
    _ ≤ n₂ + k₂ := by omega

/-
## Prime Between Blocks: Proved from Refined Axiom

We reduce the general prime-between-blocks claim to a precise hard case:
  Case 1: k₁ ≥ n₁ → first block contains a Bertrand prime (proved above)
  Case 2: n₂+k₂ ≥ 2n₁ → Bertrand prime in (n₁, 2n₁] fits in range
  Case 3: first product has a prime factor > n₁ → transfer via SamePrimeFactors
  Case 4 (axiom): n₁ > k₁, n₂+k₂ < 2n₁, all prime factors ≤ n₁
    → both blocks are n₁-smooth, requires Størmer-type smooth number theory

The hard case is extremely constrained: k₁+k₂ < n₁ (so n₁ ≥ 7), the first
block is entirely composite, and the gap between blocks is tight. Under
SamePrimeFactors, the second block must also be n₁-smooth. By Størmer-type
results on consecutive smooth numbers, this case is likely vacuously true
(the hypotheses are mutually inconsistent for large n₁).
-/

/-- The remaining hard case for prime-between-blocks. All three conditions hold:
    - The first block is entirely composite (k₁ < n₁, so no Bertrand prime in block)
    - The gap is tight (n₂+k₂ < 2n₁, so Bertrand's (n₁, 2n₁] overshoots)
    - No large prime factor (all factors ≤ n₁, so SamePrimeFactors transfer fails)
    Under these constraints, SamePrimeFactors forces both blocks to be n₁-smooth.
    Proving this requires smooth number theory not yet in Mathlib.

    Converted from `axiom` to `theorem … := by sorry` so the sorry signals an
    unproved gap rather than asserting an unverified claim. -/
theorem exists_prime_between_blocks_hard (k₁ k₂ n₁ n₂ : ℕ)
    (h₁ : 3 ≤ k₂) (h₂ : k₂ ≤ k₁)
    (h₃ : n₁ + k₁ ≤ n₂)
    (h₄ : SamePrimeFactors n₁ k₁ n₂ k₂)
    (h₅ : k₁ < n₁)
    (h₆ : n₂ + k₂ < 2 * n₁)
    (h₇ : ∀ p ∈ consecutivePrimeFactors n₁ k₁, p ≤ n₁) :
    ∃ p : ℕ, p.Prime ∧ n₁ < p ∧ p ≤ n₂ + k₂ := by
  sorry

/-- **Prime between blocks** (general case): proved by case analysis.
    Reduces the general claim to the hard-case axiom above. -/
theorem exists_prime_between_blocks (k₁ k₂ n₁ n₂ : ℕ)
    (h₁ : 3 ≤ k₂) (h₂ : k₂ ≤ k₁)
    (h₃ : n₁ + k₁ ≤ n₂)
    (h₄ : SamePrimeFactors n₁ k₁ n₂ k₂) :
    ∃ p : ℕ, p.Prime ∧ n₁ < p ∧ p ≤ n₂ + k₂ := by
  -- Case 1: k₁ ≥ n₁ (Bertrand gives a prime in the first block)
  by_cases hkn : n₁ ≤ k₁
  · exact exists_prime_between_blocks_small k₁ k₂ n₁ n₂ (le_trans h₁ h₂) hkn h₃
  push_neg at hkn
  -- Case 2: n₂ + k₂ ≥ 2n₁ (Bertrand prime fits in range)
  by_cases hlarge : 2 * n₁ ≤ n₂ + k₂
  · obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul n₁ (by omega)
    exact ⟨p, hp, hlt, by omega⟩
  push_neg at hlarge
  -- Case 3: first product has a prime factor > n₁
  by_cases hpf : ∃ q ∈ consecutivePrimeFactors n₁ k₁, n₁ < q
  · obtain ⟨q, hq_mem, hq_lo⟩ := hpf
    exact exists_prime_between_of_large_prime_factor k₁ k₂ n₁ n₂ q
      (prime_factor_is_prime n₁ k₁ q hq_mem) hq_lo hq_mem h₃ h₄
  -- Case 4: hard case (all three constraints active)
  push_neg at hpf
  exact exists_prime_between_blocks_hard k₁ k₂ n₁ n₂ h₁ h₂ h₃ h₄ hkn hlarge hpf

/-
## Problem Status
-/

/-
## Structural Lemmas
-/

/-- Among k consecutive integers starting from n+1, at least one is divisible by any d ≤ k.
    This is because the interval [n+1, n+k] has length k, so contains ⌊(n+k)/d⌋ - ⌊n/d⌋
    multiples of d, which is ≥ 1 when d ≤ k. -/
theorem exists_multiple_in_block (d n k : ℕ) (hd : 0 < d) (hdk : d ≤ k) :
    ∃ i, i ∈ Finset.Icc 1 k ∧ d ∣ (n + i) := by
  -- The next multiple of d after n is n + (d - n % d)
  have hmod : n % d < d := Nat.mod_lt n hd
  set r := d - n % d with hr_def
  have hr_pos : 0 < r := by omega
  have hr_le : r ≤ d := by omega
  use r
  refine ⟨Finset.mem_Icc.mpr ⟨hr_pos, le_trans hr_le hdk⟩, ?_⟩
  set q := n / d with hq_def
  have hnd : d * q + n % d = n := Nat.div_add_mod n d
  have h_sum : n % d + r = d := by omega
  exact ⟨q + 1, by nlinarith⟩

/-- Every prime p ≤ k is a prime factor of the consecutive product (n+1)···(n+k). -/
theorem prime_le_k_mem_factors (n k p : ℕ) (hp : p.Prime) (hpk : p ≤ k) :
    p ∈ consecutivePrimeFactors n k := by
  obtain ⟨i, hi, hdvd⟩ := exists_multiple_in_block p n k hp.pos hpk
  exact factor_prime_mem n k i hi p hp hdvd

/-- For k ≥ 2, the product has at least 2 as a prime factor. -/
theorem two_mem_factors (n k : ℕ) (hk : 2 ≤ k) :
    2 ∈ consecutivePrimeFactors n k :=
  prime_le_k_mem_factors n k 2 Nat.prime_two hk

/-
## Hard Case Structure: Both Blocks Are Entirely Composite

In the hard case (k₁ < n₁, n₂+k₂ < 2n₁, all prime factors ≤ n₁), both blocks
must consist entirely of composite numbers. The proof: if n₁+i were prime, it
would be a prime factor of the first product exceeding n₁ (since i ≥ 1),
contradicting hypothesis h₇. Similarly for the second block via SamePrimeFactors.
-/

/-- In the hard case, every element of the first block is composite.
    Proof: if n₁+i is prime and i ≥ 1, then n₁+i > n₁ is a prime factor
    of the first product, contradicting the hypothesis that all prime factors ≤ n₁. -/
theorem hard_case_first_block_composite (n₁ k₁ : ℕ)
    (h₅ : k₁ < n₁)
    (h₇ : ∀ p ∈ consecutivePrimeFactors n₁ k₁, p ≤ n₁)
    (i : ℕ) (hi : i ∈ Finset.Icc 1 k₁) :
    ¬ (n₁ + i).Prime := by
  intro hp
  -- n₁ + i is a prime factor of the product
  have hmem : (n₁ + i) ∈ consecutivePrimeFactors n₁ k₁ :=
    factor_prime_mem n₁ k₁ i hi (n₁ + i) hp (dvd_refl _)
  -- By h₇, n₁ + i ≤ n₁
  have := h₇ _ hmem
  -- But i ≥ 1, so n₁ + i > n₁
  simp only [Finset.mem_Icc] at hi
  omega

/-- In the hard case, every element of the second block is composite.
    Proof: if n₂+j is prime and j ≥ 1, then n₂+j > n₁ (since n₂ ≥ n₁+k₁) is a
    prime factor of the second product. By SamePrimeFactors, it's also a prime factor
    of the first product, and by h₇ it must be ≤ n₁ — contradiction. -/
theorem hard_case_second_block_composite (n₁ k₁ k₂ n₂ : ℕ)
    (h₃ : n₁ + k₁ ≤ n₂)
    (h₄ : SamePrimeFactors n₁ k₁ n₂ k₂)
    (h₇ : ∀ p ∈ consecutivePrimeFactors n₁ k₁, p ≤ n₁)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 k₂) :
    ¬ (n₂ + j).Prime := by
  intro hp
  -- n₂ + j is a prime factor of the second product
  have hmem₂ : (n₂ + j) ∈ consecutivePrimeFactors n₂ k₂ :=
    factor_prime_mem n₂ k₂ j hj (n₂ + j) hp (dvd_refl _)
  -- By SamePrimeFactors, it's also a prime factor of the first product
  have hmem₁ : (n₂ + j) ∈ consecutivePrimeFactors n₁ k₁ := h₄ ▸ hmem₂
  -- By h₇, n₂ + j ≤ n₁
  have hle := h₇ _ hmem₁
  -- But n₂ + j > n₁
  simp only [Finset.mem_Icc] at hj
  omega

/-- In the hard case, every prime factor of the second product is ≤ n₁.
    Follows directly from SamePrimeFactors and the first-product bound. -/
theorem hard_case_second_block_smooth (n₁ k₁ k₂ n₂ : ℕ)
    (h₄ : SamePrimeFactors n₁ k₁ n₂ k₂)
    (h₇ : ∀ p ∈ consecutivePrimeFactors n₁ k₁, p ≤ n₁) :
    ∀ p ∈ consecutivePrimeFactors n₂ k₂, p ≤ n₁ := by
  intro p hp
  exact h₇ p (h₄ ▸ hp)

/-- In the hard case, every element of the second block is n₁-smooth AND greater than n₁.
    This is the core structural constraint: k₂ ≥ 3 consecutive integers, all composite,
    all greater than n₁, all with prime factors ≤ n₁. By results on consecutive smooth
    numbers (Størmer's theorem), this is extremely restrictive and likely impossible
    for all but finitely many n₁. -/
theorem hard_case_summary (k₁ k₂ n₁ n₂ : ℕ)
    (h₁ : 3 ≤ k₂) (h₂ : k₂ ≤ k₁)
    (h₃ : n₁ + k₁ ≤ n₂)
    (h₄ : SamePrimeFactors n₁ k₁ n₂ k₂)
    (h₅ : k₁ < n₁)
    (h₆ : n₂ + k₂ < 2 * n₁)
    (h₇ : ∀ p ∈ consecutivePrimeFactors n₁ k₁, p ≤ n₁) :
    -- All elements of both blocks are composite
    (∀ i ∈ Finset.Icc 1 k₁, ¬ (n₁ + i).Prime) ∧
    (∀ j ∈ Finset.Icc 1 k₂, ¬ (n₂ + j).Prime) ∧
    -- All prime factors of the second product are ≤ n₁
    (∀ p ∈ consecutivePrimeFactors n₂ k₂, p ≤ n₁) ∧
    -- All elements of the second block exceed n₁
    (∀ j ∈ Finset.Icc 1 k₂, n₁ < n₂ + j) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hard_case_first_block_composite n₁ k₁ h₅ h₇
  · exact hard_case_second_block_composite n₁ k₁ k₂ n₂ h₃ h₄ h₇
  · exact hard_case_second_block_smooth n₁ k₁ k₂ n₂ h₄ h₇
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    omega

/-
## Hard Case: Lower Bound on n₁

In the hard case, the constraints k₁ < n₁ and k₁ ≥ k₂ ≥ 3 force n₁ ≥ 4.
Combined with n₂+k₂ < 2n₁ and n₁+k₁ ≤ n₂, we get k₁+k₂ < n₁, so n₁ ≥ 7.
-/

/-- In the hard case, n₁ ≥ k₁ + k₂ + 1 ≥ 7. -/
theorem hard_case_n1_lower_bound (k₁ k₂ n₁ n₂ : ℕ)
    (h₁ : 3 ≤ k₂) (h₂ : k₂ ≤ k₁) (h₃ : n₁ + k₁ ≤ n₂)
    (h₅ : k₁ < n₁) (h₆ : n₂ + k₂ < 2 * n₁) :
    k₁ + k₂ + 1 ≤ n₁ := by omega

/-- In the hard case, the range for n₂ is non-empty: [n₁+k₁, 2n₁-k₂-1]. -/
theorem hard_case_n2_range (k₁ k₂ n₁ n₂ : ℕ)
    (h₃ : n₁ + k₁ ≤ n₂) (h₆ : n₂ + k₂ < 2 * n₁) :
    n₁ + k₁ ≤ n₂ ∧ n₂ ≤ 2 * n₁ - k₂ - 1 := by omega

/-
## Hard Case: No Prime in First Block

The constraint that all prime factors of the first product are ≤ n₁ means
there is NO prime in {n₁+1, ..., n₁+k₁}. Therefore, the next prime after
n₁ is strictly larger than n₁+k₁.
-/

/-- In the hard case, no prime lies in the first block {n₁+1,...,n₁+k₁}. -/
theorem hard_case_no_prime_in_first_block (n₁ k₁ : ℕ)
    (h₅ : k₁ < n₁)
    (h₇ : ∀ p ∈ consecutivePrimeFactors n₁ k₁, p ≤ n₁)
    (p : ℕ) (hp : p.Prime) (hlo : n₁ < p) (hhi : p ≤ n₁ + k₁) :
    False := by
  have hp_in : p ∈ Finset.Icc 1 k₁ := by
    rw [Finset.mem_Icc]; constructor <;> omega
  exact hard_case_first_block_composite n₁ k₁ h₅ h₇ p hp_in hp

/-- Consequently, the next prime after n₁ must exceed n₁+k₁.
    Combined with Bertrand (next prime ≤ 2n₁), the next prime lies in
    (n₁+k₁, 2n₁]. Whether it falls in (n₁+k₁, n₂+k₂] depends on
    the specific gap structure. -/
theorem hard_case_next_prime_beyond_block (n₁ k₁ : ℕ)
    (h₅ : k₁ < n₁)
    (h₇ : ∀ p ∈ consecutivePrimeFactors n₁ k₁, p ≤ n₁) :
    ∀ p : ℕ, p.Prime → n₁ < p → n₁ + k₁ < p := by
  intro p hp hlo
  by_contra h
  push_neg at h
  exact hard_case_no_prime_in_first_block n₁ k₁ h₅ h₇ p hp hlo h

/-
## Hard Case: Computational Verification for Small n₁

For k₁ = k₂ = 3 and small n₁, we verify that the hard case hypotheses are
mutually inconsistent: either h₇ fails (first block has a prime factor > n₁),
or SamePrimeFactors fails for all n₂ in the valid range.

This provides empirical evidence that the hard case is vacuously true
(the hypotheses are never simultaneously satisfiable).
-/

/-- For k₁ = k₂ = 3, no valid hard-case instance exists with n₁ ∈ [7, 30].
    For each n₁ in range, for each n₂ ∈ [n₁+3, 2n₁-4]:
    either the first block has a prime factor > n₁ (h₇ fails),
    or SamePrimeFactors(n₁, 3, n₂, 3) is false. -/
theorem hard_case_vacuous_k3_n30 :
    ∀ n₁ ∈ Finset.Icc 7 30,
    ∀ n₂ ∈ Finset.Icc (n₁ + 3) (2 * n₁ - 4),
      (∀ p ∈ consecutivePrimeFactors n₁ 3, p ≤ n₁) →
      ¬SamePrimeFactors n₁ 3 n₂ 3 := by native_decide

end Erdos931
