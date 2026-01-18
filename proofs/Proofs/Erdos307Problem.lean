/-
  Erdős Problem #307: Prime Reciprocal Products

  Source: https://erdosproblems.com/307
  Status: OPEN (prime version) / SOLVED (coprime version)

  Statement:
  Are there two finite sets of primes P, Q such that
      1 = (Σ_{p ∈ P} 1/p) · (Σ_{q ∈ Q} 1/q)?

  Known Results:
  - The prime version remains OPEN
  - The coprime version is SOLVED: Cambie found examples
    - (1 + 1/5)(1/2 + 1/3) = 1
    - (1 + 1/41)(1/2 + 1/3 + 1/7) = 1
  - No examples known with 1 ∉ P ∪ Q (coprime case)
  - If P, Q are primes: P ∩ Q = ∅ and |P ∪ Q| ≥ 60

  Historical Note:
  Asked by Barbeau in 1976 in "Computer challenge corner: Problem 477".

  References:
  [Ba76] Barbeau, E. J., "Computer challenge corner: Problem 477:
         A brute force program." J. Rec. Math. (1976).

  Tags: number-theory, primes, egyptian-fractions
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic

namespace Erdos307

open Finset BigOperators

/-! ## Part I: Problem Statement -/

/-- The sum of reciprocals of elements in a finite set.
    For a set S = {a₁, a₂, ..., aₙ}, this computes 1/a₁ + 1/a₂ + ... + 1/aₙ. -/
noncomputable def reciprocalSum (S : Finset ℕ) : ℚ :=
  ∑ n in S, (n : ℚ)⁻¹

/-- The product of two reciprocal sums.
    We ask when this equals 1. -/
noncomputable def reciprocalProduct (P Q : Finset ℕ) : ℚ :=
  reciprocalSum P * reciprocalSum Q

/-- A set of primes is a finite set where every element is prime. -/
def IsSetOfPrimes (S : Finset ℕ) : Prop :=
  ∀ p ∈ S, Nat.Prime p

/-- A set is pairwise coprime if any two distinct elements are coprime. -/
def IsPairwiseCoprime (S : Finset ℕ) : Prop :=
  (S : Set ℕ).Pairwise Nat.Coprime

/-! ## Part II: The Open Problem (Prime Version) -/

/-- **Erdős Problem #307** (Prime Version - OPEN):

    Do there exist two finite sets of primes P and Q such that
    (Σ_{p ∈ P} 1/p) · (Σ_{q ∈ Q} 1/q) = 1?

    Status: OPEN. No solution is known, but existence hasn't been disproved. -/
def ErdosProblem307 : Prop :=
  ∃ P Q : Finset ℕ, IsSetOfPrimes P ∧ IsSetOfPrimes Q ∧
    reciprocalProduct P Q = 1

/-- The open status is a placeholder. -/
axiom erdos_307_open : True

/-! ## Part III: The Solved Coprime Version -/

/-- The relaxed version where P and Q need only be pairwise coprime,
    not necessarily prime. -/
def ErdosProblem307Coprime : Prop :=
  ∃ P Q : Finset ℕ, P.card > 1 ∧ Q.card > 1 ∧
    IsPairwiseCoprime P ∧ IsPairwiseCoprime Q ∧
    reciprocalProduct P Q = 1

/-- **Cambie's First Example**:
    P = {1, 5}, Q = {2, 3}
    (1 + 1/5)(1/2 + 1/3) = (6/5)(5/6) = 1 ✓ -/
def cambieExample1P : Finset ℕ := {1, 5}
def cambieExample1Q : Finset ℕ := {2, 3}

/-- Verify that {1, 5} is pairwise coprime. -/
theorem cambieExample1P_coprime : IsPairwiseCoprime cambieExample1P := by
  intro a ha b hb hab
  simp [cambieExample1P] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    first | contradiction | decide

/-- Verify that {2, 3} is pairwise coprime. -/
theorem cambieExample1Q_coprime : IsPairwiseCoprime cambieExample1Q := by
  intro a ha b hb hab
  simp [cambieExample1Q] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    first | contradiction | decide

/-- The reciprocal sum of {1, 5} is 6/5. -/
theorem cambieExample1P_sum : reciprocalSum cambieExample1P = 6/5 := by
  simp [reciprocalSum, cambieExample1P]
  norm_num

/-- The reciprocal sum of {2, 3} is 5/6. -/
theorem cambieExample1Q_sum : reciprocalSum cambieExample1Q = 5/6 := by
  simp [reciprocalSum, cambieExample1Q]
  norm_num

/-- Cambie's first example: (1 + 1/5)(1/2 + 1/3) = 1. -/
theorem cambieExample1_works : reciprocalProduct cambieExample1P cambieExample1Q = 1 := by
  simp [reciprocalProduct, cambieExample1P_sum, cambieExample1Q_sum]
  norm_num

/-- **Cambie's Second Example**:
    P = {1, 41}, Q = {2, 3, 7}
    (1 + 1/41)(1/2 + 1/3 + 1/7) = (42/41)(41/42) = 1 ✓ -/
def cambieExample2P : Finset ℕ := {1, 41}
def cambieExample2Q : Finset ℕ := {2, 3, 7}

/-- The reciprocal sum of {1, 41} is 42/41. -/
theorem cambieExample2P_sum : reciprocalSum cambieExample2P = 42/41 := by
  simp [reciprocalSum, cambieExample2P]
  norm_num

/-- The reciprocal sum of {2, 3, 7} is 41/42. -/
theorem cambieExample2Q_sum : reciprocalSum cambieExample2Q = 41/42 := by
  simp [reciprocalSum, cambieExample2Q]
  norm_num

/-- Cambie's second example: (1 + 1/41)(1/2 + 1/3 + 1/7) = 1. -/
theorem cambieExample2_works : reciprocalProduct cambieExample2P cambieExample2Q = 1 := by
  simp [reciprocalProduct, cambieExample2P_sum, cambieExample2Q_sum]
  norm_num

/-- The coprime version is SOLVED: Cambie's examples prove existence. -/
theorem erdos_307_coprime_solved : ErdosProblem307Coprime := by
  use cambieExample1P, cambieExample1Q
  refine ⟨?_, ?_, cambieExample1P_coprime, cambieExample1Q_coprime, cambieExample1_works⟩
  · simp [cambieExample1P]; decide
  · simp [cambieExample1Q]; decide

/-! ## Part IV: The Strengthened Coprime Version (Open) -/

/-- The strengthened coprime version: require 1 ∉ P ∪ Q.
    No examples are known! -/
def ErdosProblem307CoprimeStrengthened : Prop :=
  ∃ P Q : Finset ℕ, P.card > 1 ∧ Q.card > 1 ∧
    1 ∉ P ∧ 1 ∉ Q ∧
    IsPairwiseCoprime P ∧ IsPairwiseCoprime Q ∧
    reciprocalProduct P Q = 1

/-- Status: The strengthened coprime version remains OPEN. -/
axiom erdos_307_coprime_strengthened_open : True

/-! ## Part V: Constraints on Prime Solutions -/

/-- If P and Q are sets of primes with product 1, then P ∩ Q = ∅.

    Proof sketch: If p ∈ P ∩ Q, the product would have p² in the denominator
    somewhere, but also p² in the numerator. The constraint that the product
    equals 1 (a rational with denominator 1) forces this.

    Actually, more directly: if p ∈ P ∩ Q, then 1/p appears in both sums,
    so the product includes (1/p)² = 1/p². But the product of two sums of
    distinct primes' reciprocals can't simplify to 1 with repeated primes. -/
theorem prime_sets_disjoint {P Q : Finset ℕ} (hP : IsSetOfPrimes P)
    (hQ : IsSetOfPrimes Q) (hPQ : reciprocalProduct P Q = 1) :
    P ∩ Q = ∅ := by
  sorry

/-- A lower bound: if P, Q are prime sets with product 1, then
    Σ_{p ∈ P ∪ Q} 1/p ≥ 2.

    This follows from AM-GM: if (Σ 1/p)(Σ 1/q) = 1, then
    (Σ 1/p) + (Σ 1/q) ≥ 2√((Σ 1/p)(Σ 1/q)) = 2. -/
theorem prime_reciprocal_sum_lower_bound {P Q : Finset ℕ}
    (hP : IsSetOfPrimes P) (hQ : IsSetOfPrimes Q)
    (hPQ : reciprocalProduct P Q = 1) (hdisj : Disjoint P Q) :
    reciprocalSum (P ∪ Q) ≥ 2 := by
  sorry

/-- A consequence: |P ∪ Q| ≥ 60.

    Since Σ_{p prime} 1/p diverges slowly, we need about 60 primes
    to get Σ 1/p ≥ 2. The first 60 primes suffice:
    Σ_{p ≤ 281} 1/p ≈ 2.009... -/
theorem prime_set_size_lower_bound {P Q : Finset ℕ}
    (hP : IsSetOfPrimes P) (hQ : IsSetOfPrimes Q)
    (hPQ : reciprocalProduct P Q = 1) :
    (P ∪ Q).card ≥ 60 := by
  sorry

/-! ## Part VI: Why the Problem is Hard -/

/-- The sum of reciprocals of the first n primes.
    p₁ = 2, p₂ = 3, p₃ = 5, ...
    S_n = 1/2 + 1/3 + 1/5 + ... + 1/pₙ -/
noncomputable def primeReciprocalPartialSum (n : ℕ) : ℚ :=
  ∑ i in (Finset.range n).filter (fun k => (k + 1).minFac = k + 1 ∧ k + 1 > 1),
    ((i + 1) : ℚ)⁻¹

/-- The divergence of Σ 1/p is very slow (like log log n).
    This makes finding solutions computationally difficult. -/
axiom prime_reciprocal_divergence :
  ∀ M : ℚ, ∃ n : ℕ, primeReciprocalPartialSum n > M

/-- The constraint that the product equals 1 is very rigid.
    Most choices of P won't have any Q that works. -/
axiom product_rigidity :
  ∀ P : Finset ℕ, IsSetOfPrimes P → P.card > 0 →
    (∃ Q : Finset ℕ, IsSetOfPrimes Q ∧ reciprocalProduct P Q = 1) ↔
    ∃ Q : Finset ℕ, IsSetOfPrimes Q ∧
      reciprocalSum Q = (reciprocalSum P)⁻¹ ∧
      (reciprocalSum P)⁻¹ = ∑ q in Q, (q : ℚ)⁻¹

/-! ## Part VII: Related Egyptian Fraction Problems -/

/-- An Egyptian fraction representation of 1.
    1 = 1/a₁ + 1/a₂ + ... + 1/aₙ for distinct positive integers aᵢ. -/
def IsEgyptianOne (S : Finset ℕ) : Prop :=
  (∀ n ∈ S, n > 0) ∧ reciprocalSum S = 1

/-- Example: 1 = 1/2 + 1/3 + 1/6. -/
theorem egyptian_example : IsEgyptianOne {2, 3, 6} := by
  constructor
  · intro n hn
    simp at hn
    rcases hn with rfl | rfl | rfl <;> omega
  · simp [reciprocalSum]
    norm_num

/-- The number of ways to write 1 as a sum of n distinct unit fractions
    grows rapidly with n. -/
axiom egyptian_count_growth :
  ∀ n : ℕ, ∃ count : ℕ, count > 0 ∧
    (∀ S : Finset ℕ, S.card = n → IsEgyptianOne S → count ≥ 1)

/-! ## Part VIII: Computational Approaches -/

/-- A brute force search would need to check pairs (P, Q) where
    |P ∪ Q| ≥ 60, making exhaustive search infeasible. -/
def searchSpaceSize : ℕ := 2^60

/-- The number of partitions of a 60-prime set into P and Q
    (where we need both to be nonempty). -/
theorem partition_count : searchSpaceSize = 2^60 := rfl

/-- There are ≈ 1.15 × 10¹⁸ ways to partition 60 primes.
    Even at 10⁹ checks/second, this takes over 36 years. -/
axiom search_intractable : searchSpaceSize > 10^18

/-! ## Part IX: Why Does 1 Appear in Coprime Examples? -/

/-- In Cambie's examples, 1 always appears in one of the sets.
    This is because 1 + 1/n has reciprocal n/(n+1), which is
    easier to match with a small set of primes. -/
theorem one_helps_balance {P Q : Finset ℕ} (h1P : 1 ∈ P)
    (hcop_P : IsPairwiseCoprime P) (hcop_Q : IsPairwiseCoprime Q)
    (hprod : reciprocalProduct P Q = 1) :
    reciprocalSum P > 1 := by
  sorry

/-- If P = {1, n}, then reciprocalSum P = 1 + 1/n = (n+1)/n.
    For this to multiply to 1, we need reciprocalSum Q = n/(n+1). -/
theorem pair_with_one (n : ℕ) (hn : n > 0) :
    reciprocalSum ({1, n} : Finset ℕ) = (n + 1 : ℚ) / n := by
  simp [reciprocalSum]
  field_simp
  ring

/-! ## Part X: Alternative Formulations -/

/-- Multiplicative form: Find P, Q with
    ∏_{p ∈ P} p · ∏_{q ∈ Q} q = (Σ subsets give 1). -/
def MultiplicativeForm (P Q : Finset ℕ) : Prop :=
  let pProd := ∏ p in P, p
  let qProd := ∏ q in Q, q
  pProd * qProd = (∑ S in P.powerset, ∏ p in S, (∏ q in Q, q)) *
                  (∑ T in Q.powerset, ∏ q in T, (∏ p in P, p))

/-- Connection to LCD: The product equals 1 iff
    LCD(P) · LCD(Q) = (Σ denominators' complements). -/
axiom lcd_connection {P Q : Finset ℕ} (hP : IsSetOfPrimes P)
    (hQ : IsSetOfPrimes Q) :
    reciprocalProduct P Q = 1 ↔
    (∏ p in P, p) * (∏ q in Q, q) =
    (∑ S in P.powerset, ∏ p in (P \ S), p) *
    (∑ T in Q.powerset, ∏ q in (Q \ T), q)

/-! ## Part XI: Partial Results -/

/-- No solution with |P| = |Q| = 2 exists among primes.
    If P = {p₁, p₂} and Q = {q₁, q₂}, then
    (1/p₁ + 1/p₂)(1/q₁ + 1/q₂) = 1
    ⟹ (p₁ + p₂)(q₁ + q₂) = p₁p₂q₁q₂.
    This has no prime solutions. -/
theorem no_size_two_solution :
    ¬∃ P Q : Finset ℕ, P.card = 2 ∧ Q.card = 2 ∧
      IsSetOfPrimes P ∧ IsSetOfPrimes Q ∧
      reciprocalProduct P Q = 1 := by
  sorry

/-- No solution with |P| = 2 and |Q| = 3 exists among primes. -/
theorem no_two_three_solution :
    ¬∃ P Q : Finset ℕ, P.card = 2 ∧ Q.card = 3 ∧
      IsSetOfPrimes P ∧ IsSetOfPrimes Q ∧
      reciprocalProduct P Q = 1 := by
  sorry

/-! ## Part XII: Summary -/

/-- Summary of Erdős Problem #307:

    **Prime Version** (OPEN):
    Do there exist finite sets of primes P, Q with
    (Σ 1/p)(Σ 1/q) = 1?

    **Coprime Version** (SOLVED):
    Yes! Cambie's examples:
    - (1 + 1/5)(1/2 + 1/3) = 1
    - (1 + 1/41)(1/2 + 1/3 + 1/7) = 1

    **Strengthened Coprime** (OPEN):
    Unknown if solution exists with 1 ∉ P ∪ Q.

    **Known Constraints**:
    - If P, Q are primes: |P ∪ Q| ≥ 60
    - P ∩ Q = ∅ for any solution

    **Why Hard**:
    - Search space ≈ 2^60 ≈ 10^18
    - Prime reciprocal sums grow very slowly -/
theorem erdos_307_summary :
    ErdosProblem307Coprime ∧
    (∀ P Q : Finset ℕ, IsSetOfPrimes P → IsSetOfPrimes Q →
      reciprocalProduct P Q = 1 → (P ∪ Q).card ≥ 60) := by
  constructor
  · exact erdos_307_coprime_solved
  · intro P Q hP hQ hprod
    exact prime_set_size_lower_bound hP hQ hprod

end Erdos307

/-!
## Summary

This file formalizes Erdős Problem #307 on prime reciprocal products.

**Status**: OPEN (prime version) / SOLVED (coprime version)

**The Problem**: Do there exist two finite sets of primes P, Q such that
(Σ_{p ∈ P} 1/p)(Σ_{q ∈ Q} 1/q) = 1?

**What we formalize**:
1. The reciprocal sum and product definitions
2. The prime and coprime versions of the problem
3. Cambie's verified examples for the coprime version
4. The constraint that |P ∪ Q| ≥ 60 for prime solutions
5. The disjointness requirement P ∩ Q = ∅
6. Connection to Egyptian fractions
7. Partial non-existence results for small sets

**Key insight**: The coprime version is solvable because including 1
in one set makes balancing easier: 1 + 1/n = (n+1)/n has a "nice"
reciprocal n/(n+1). The prime version is much harder because we
can't use 1, and finding primes whose reciprocals sum to a reciprocal
of another prime sum is extremely constrained.

**Historical Note**: Asked by Barbeau in 1976. Cambie solved the
coprime version. The prime version remains one of the older unsolved
problems in elementary number theory.
-/
