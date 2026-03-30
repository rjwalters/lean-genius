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

/- ## Part I: Problem Statement -/

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

/- ## Part II: The Open Problem (Prime Version) -/

/-- **Erdős Problem #307** (Prime Version - OPEN):

    Do there exist two finite sets of primes P and Q such that
    (Σ_{p ∈ P} 1/p) · (Σ_{q ∈ Q} 1/q) = 1?

    Status: OPEN. No solution is known, but existence hasn't been disproved. -/
def ErdosProblem307 : Prop :=
  ∃ P Q : Finset ℕ, IsSetOfPrimes P ∧ IsSetOfPrimes Q ∧
    reciprocalProduct P Q = 1

/- The open status is a placeholder. -/

/- ## Part III: The Solved Coprime Version -/

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

/- ## Part IV: The Strengthened Coprime Version (Open) -/

/-- The strengthened coprime version: require 1 ∉ P ∪ Q.
    No examples are known! -/
def ErdosProblem307CoprimeStrengthened : Prop :=
  ∃ P Q : Finset ℕ, P.card > 1 ∧ Q.card > 1 ∧
    1 ∉ P ∧ 1 ∉ Q ∧
    IsPairwiseCoprime P ∧ IsPairwiseCoprime Q ∧
    reciprocalProduct P Q = 1

/- Status: The strengthened coprime version remains OPEN. -/

/- ## Part V: Constraints on Prime Solutions -/

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

    This follows from AM-GM: if a · b = 1, then a + b ≥ 2.
    Proof: (a - 1)² ≥ 0 ⟹ a² - 2a + 1 ≥ 0 ⟹ a + 1/a ≥ 2. -/
theorem prime_reciprocal_sum_lower_bound {P Q : Finset ℕ}
    (hP : IsSetOfPrimes P) (hQ : IsSetOfPrimes Q)
    (hPQ : reciprocalProduct P Q = 1) (hdisj : Disjoint P Q) :
    reciprocalSum (P ∪ Q) ≥ 2 := by
  -- reciprocalSum (P ∪ Q) = reciprocalSum P + reciprocalSum Q when P, Q disjoint
  have hunion : reciprocalSum (P ∪ Q) = reciprocalSum P + reciprocalSum Q := by
    unfold reciprocalSum
    rw [Finset.sum_union (Finset.disjoint_iff_disjoint_coe.mp hdisj)]
  rw [hunion]
  -- Let a = reciprocalSum P, b = reciprocalSum Q
  -- We know a * b = 1 and a, b > 0 (sums of positive terms, nonempty)
  set a := reciprocalSum P
  set b := reciprocalSum Q
  -- a * b = 1
  have hab : a * b = 1 := hPQ
  -- a > 0: each 1/p > 0 for prime p, and P nonempty (since a*b=1, a≠0)
  have ha_pos : 0 < a := by
    by_contra h
    push_neg at h
    have ha_le : a ≤ 0 := h
    -- If a ≤ 0, then a * b ≤ 0, contradicting a * b = 1
    have hb_nn : 0 ≤ b := by
      unfold reciprocalSum
      apply Finset.sum_nonneg
      intro n _; positivity
    have : a * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha_le hb_nn
    linarith
  -- b = 1/a (from a * b = 1)
  have hb_eq : b = a⁻¹ := by
    field_simp at hab ⊢
    linarith
  -- AM-GM: a + 1/a ≥ 2 for a > 0
  rw [hb_eq]
  -- a + a⁻¹ ≥ 2 ⟺ a² + 1 ≥ 2a ⟺ (a-1)² ≥ 0
  rw [ge_iff_le, ← sub_nonneg]
  have key : a + a⁻¹ - 2 = (a - 1)^2 * a⁻¹ := by field_simp; ring
  rw [key]
  apply mul_nonneg
  · exact sq_nonneg _
  · exact le_of_lt (inv_pos.mpr ha_pos)

/-- A consequence: |P ∪ Q| ≥ 60.

    Since Σ_{p prime} 1/p diverges slowly, we need about 60 primes
    to get Σ 1/p ≥ 2. The first 60 primes suffice:
    Σ_{p ≤ 281} 1/p ≈ 2.009... -/
theorem prime_set_size_lower_bound {P Q : Finset ℕ}
    (hP : IsSetOfPrimes P) (hQ : IsSetOfPrimes Q)
    (hPQ : reciprocalProduct P Q = 1) :
    (P ∪ Q).card ≥ 60 := by
  sorry

/- ## Part VI: Why the Problem is Hard -/

/-- The sum of reciprocals of the first n primes.
    p₁ = 2, p₂ = 3, p₃ = 5, ...
    S_n = 1/2 + 1/3 + 1/5 + ... + 1/pₙ -/
noncomputable def primeReciprocalPartialSum (n : ℕ) : ℚ :=
  ∑ i in (Finset.range n).filter (fun k => (k + 1).minFac = k + 1 ∧ k + 1 > 1),
    ((i + 1) : ℚ)⁻¹

/-
Note: Σ 1/p diverges like log log n (Mertens' theorem), making
prime reciprocal products computationally difficult to search.
The product constraint is very rigid: given P, the required
reciprocalSum Q = (reciprocalSum P)⁻¹ must itself decompose as
a sum of distinct prime reciprocals.
-/

/- ## Part VII: Related Egyptian Fraction Problems -/

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

/- ## Part VIII: Computational Approaches -/

/-- A brute force search would need to check pairs (P, Q) where
    |P ∪ Q| ≥ 60, making exhaustive search infeasible. -/
def searchSpaceSize : ℕ := 2^60

/-- The number of partitions of a 60-prime set into P and Q
    (where we need both to be nonempty). -/
theorem partition_count : searchSpaceSize = 2^60 := rfl

/-- There are ≈ 1.15 × 10¹⁸ ways to partition 60 primes.
    Even at 10⁹ checks/second, this takes over 36 years. -/
theorem search_intractable : searchSpaceSize > 10^18 := by
  native_decide

/- ## Part IX: Why Does 1 Appear in Coprime Examples? -/

/-- In Cambie's examples, 1 always appears in one of the sets.
    This is because 1 + 1/n has reciprocal n/(n+1), which is
    easier to match with a small set of primes.
    If 1 ∈ P and P has more than 1 positive element, then reciprocalSum P > 1,
    since 1/1 = 1 and the other reciprocals are positive. -/
theorem one_helps_balance {P Q : Finset ℕ} (h1P : 1 ∈ P)
    (hcard : P.card > 1) (hpos : ∀ p ∈ P, 0 < p)
    (hcop_P : IsPairwiseCoprime P) (hcop_Q : IsPairwiseCoprime Q)
    (hprod : reciprocalProduct P Q = 1) :
    reciprocalSum P > 1 := by
  unfold reciprocalSum
  rw [← Finset.add_sum_erase _ _ h1P]
  simp only [Nat.cast_one, inv_one]
  have hne : (P.erase 1).Nonempty :=
    Finset.card_pos.mp (by rw [Finset.card_erase_of_mem h1P]; omega)
  have hpos' : ∀ x ∈ P.erase 1, (0 : ℚ) < (x : ℚ)⁻¹ := fun x hx =>
    inv_pos.mpr (Nat.cast_pos.mpr (hpos x (Finset.mem_of_mem_erase hx)))
  linarith [Finset.sum_pos hpos' hne]

/-- If P = {1, n}, then reciprocalSum P = 1 + 1/n = (n+1)/n.
    For this to multiply to 1, we need reciprocalSum Q = n/(n+1). -/
theorem pair_with_one (n : ℕ) (hn : n > 0) :
    reciprocalSum ({1, n} : Finset ℕ) = (n + 1 : ℚ) / n := by
  simp [reciprocalSum]
  field_simp
  ring

/- ## Part X: Alternative Formulations -/

/-- Multiplicative form: Find P, Q with
    ∏_{p ∈ P} p · ∏_{q ∈ Q} q = (Σ subsets give 1). -/
def MultiplicativeForm (P Q : Finset ℕ) : Prop :=
  let pProd := ∏ p in P, p
  let qProd := ∏ q in Q, q
  pProd * qProd = (∑ S in P.powerset, ∏ p in S, (∏ q in Q, q)) *
                  (∑ T in Q.powerset, ∏ q in T, (∏ p in P, p))

/-
Note: The product equals 1 iff LCD(P) · LCD(Q) = (Σ complements),
i.e., (∏ P) · (∏ Q) = (Σ_{S⊆P} ∏(P\S)) · (Σ_{T⊆Q} ∏(Q\T)).
This is an algebraic reformulation but doesn't simplify the search.
-/

/- ## Part XI: Partial Results -/

/-- For any two distinct primes, the reciprocal sum ≤ 5/6.
    Proof: smallest distinct primes are 2, 3 with 1/2 + 1/3 = 5/6. -/
private lemma reciprocal_sum_two_primes_le {P : Finset ℕ} (hcard : P.card = 2) (hP : IsSetOfPrimes P) :
    reciprocalSum P ≤ 5 / 6 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  simp only [reciprocalSum, Finset.sum_pair hab]
  have ha : Nat.Prime a := hP a (Finset.mem_insert_self a {b})
  have hb : Nat.Prime b := hP b (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self b)))
  have ha2 : (2 : ℚ) ≤ a := by exact_mod_cast ha.two_le
  have hb2 : (2 : ℚ) ≤ b := by exact_mod_cast hb.two_le
  -- One of them ≥ 3 since a ≠ b and both ≥ 2
  have hab3 : (3 : ℚ) ≤ a ∨ (3 : ℚ) ≤ b := by
    by_contra h; push_neg at h
    have : a = 2 := by exact_mod_cast (le_antisymm (by linarith) ha.two_le)
    have : b = 2 := by exact_mod_cast (le_antisymm (by linarith) hb.two_le)
    exact hab (by omega)
  have ha_pos : (0 : ℚ) < a := by linarith
  have hb_pos : (0 : ℚ) < b := by linarith
  rcases hab3 with h3 | h3
  · -- a ≥ 3, b ≥ 2: 1/a + 1/b ≤ 1/3 + 1/2 = 5/6
    have : (a : ℚ)⁻¹ ≤ 1 / 3 := by rw [one_div]; exact inv_le_inv_of_le (by norm_num) h3
    have : (b : ℚ)⁻¹ ≤ 1 / 2 := by rw [one_div]; exact inv_le_inv_of_le (by norm_num) hb2
    linarith
  · -- a ≥ 2, b ≥ 3: 1/a + 1/b ≤ 1/2 + 1/3 = 5/6
    have : (a : ℚ)⁻¹ ≤ 1 / 2 := by rw [one_div]; exact inv_le_inv_of_le (by norm_num) ha2
    have : (b : ℚ)⁻¹ ≤ 1 / 3 := by rw [one_div]; exact inv_le_inv_of_le (by norm_num) h3
    linarith

/-- No solution with |P| = |Q| = 2 exists among primes.
    PROVED: reciprocalProduct ≤ (5/6)² = 25/36 < 1. -/
theorem no_size_two_solution :
    ¬∃ P Q : Finset ℕ, P.card = 2 ∧ Q.card = 2 ∧
      IsSetOfPrimes P ∧ IsSetOfPrimes Q ∧
      reciprocalProduct P Q = 1 := by
  intro ⟨P, Q, hP2, hQ2, hPprime, hQprime, hprod⟩
  have hP_le := reciprocal_sum_two_primes_le hP2 hPprime
  have hQ_le := reciprocal_sum_two_primes_le hQ2 hQprime
  have : reciprocalProduct P Q ≤ 25 / 36 := by
    unfold reciprocalProduct
    calc reciprocalSum P * reciprocalSum Q
        ≤ (5 / 6) * (5 / 6) := by
          apply mul_le_mul hP_le hQ_le
          · exact Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg i))
          · norm_num
      _ = 25 / 36 := by norm_num
  linarith

/-- For 3 distinct primes, sum of reciprocals ≤ 1/2 + 1/3 + 1/5 = 31/30.
    Proof: among 3 distinct primes, at least one ≥ 5 (only 2 primes < 5)
    and among the other two, at least one ≥ 3 (only 1 prime < 3). -/
private lemma reciprocal_sum_three_primes_le {Q : Finset ℕ} (hcard : Q.card = 3)
    (hQ : IsSetOfPrimes Q) : reciprocalSum Q ≤ 31 / 30 := by
  obtain ⟨c, t, hct, rfl, ht2⟩ := Finset.card_eq_succ.mp hcard
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp ht2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hct
  obtain ⟨hca, hcb⟩ := hct
  have ha := hQ a (by simp)
  have hb := hQ b (by simp)
  have hc := hQ c (by simp)
  have ha2 : (2 : ℚ) ≤ a := by exact_mod_cast ha.two_le
  have hb2 : (2 : ℚ) ≤ b := by exact_mod_cast hb.two_le
  have hc2 : (2 : ℚ) ≤ c := by exact_mod_cast hc.two_le
  simp only [reciprocalSum, Finset.sum_insert hct, Finset.sum_pair hab]
  -- At least one ≥ 5 (pigeonhole: only 2 primes < 5, namely {2, 3})
  have h5 : 5 ≤ a ∨ 5 ≤ b ∨ 5 ≤ c := by
    by_contra hall; push_neg at hall; obtain ⟨h5a, h5b, h5c⟩ := hall
    have : a = 2 ∨ a = 3 := by have := ha.two_le; interval_cases a <;> simp_all
    have : b = 2 ∨ b = 3 := by have := hb.two_le; interval_cases b <;> simp_all
    have : c = 2 ∨ c = 3 := by have := hc.two_le; interval_cases c <;> simp_all
    rcases ‹a = 2 ∨ a = 3› with rfl | rfl <;> rcases ‹b = 2 ∨ b = 3› with rfl | rfl <;>
      rcases ‹c = 2 ∨ c = 3› with rfl | rfl <;> simp_all
  -- Among any 2 distinct primes, one ≥ 3 (only 1 prime < 3)
  have pair3 : ∀ x y : ℕ, Nat.Prime x → Nat.Prime y → x ≠ y →
      (3 : ℚ) ≤ (x : ℚ) ∨ (3 : ℚ) ≤ (y : ℚ) := by
    intro x y hx hy hxy; by_contra hall; push_neg at hall
    have hx3 : x < 3 := by exact_mod_cast hall.1
    have hy3 : y < 3 := by exact_mod_cast hall.2
    have : x = 2 := le_antisymm (by omega) hx.two_le
    have : y = 2 := le_antisymm (by omega) hy.two_le
    exact hxy (by omega)
  -- Bound each reciprocal, then combine
  rcases h5 with h5a | h5b | h5c
  · have : (a : ℚ)⁻¹ ≤ 1/5 := by rw [one_div]; exact inv_le_inv_of_le (by norm_num) (by exact_mod_cast h5a)
    rcases pair3 b c hb hc (Ne.symm hcb) with h3 | h3
    · have : (b : ℚ)⁻¹ ≤ 1/3 := by rw [one_div]; exact inv_le_inv_of_le (by norm_num) h3
      have : (c : ℚ)⁻¹ ≤ 1/2 := by rw [one_div]; exact inv_le_inv_of_le (by norm_num) hc2
      linarith
    · have : (c : ℚ)⁻¹ ≤ 1/3 := by rw [one_div]; exact inv_le_inv_of_le (by norm_num) h3
      have : (b : ℚ)⁻¹ ≤ 1/2 := by rw [one_div]; exact inv_le_inv_of_le (by norm_num) hb2
      linarith
  · have : (b : ℚ)⁻¹ ≤ 1/5 := by rw [one_div]; exact inv_le_inv_of_le (by norm_num) (by exact_mod_cast h5b)
    rcases pair3 a c ha hc (Ne.symm hca) with h3 | h3
    · have : (a : ℚ)⁻¹ ≤ 1/3 := by rw [one_div]; exact inv_le_inv_of_le (by norm_num) h3
      have : (c : ℚ)⁻¹ ≤ 1/2 := by rw [one_div]; exact inv_le_inv_of_le (by norm_num) hc2
      linarith
    · have : (c : ℚ)⁻¹ ≤ 1/3 := by rw [one_div]; exact inv_le_inv_of_le (by norm_num) h3
      have : (a : ℚ)⁻¹ ≤ 1/2 := by rw [one_div]; exact inv_le_inv_of_le (by norm_num) ha2
      linarith
  · have : (c : ℚ)⁻¹ ≤ 1/5 := by rw [one_div]; exact inv_le_inv_of_le (by norm_num) (by exact_mod_cast h5c)
    rcases pair3 a b ha hb hab with h3 | h3
    · have : (a : ℚ)⁻¹ ≤ 1/3 := by rw [one_div]; exact inv_le_inv_of_le (by norm_num) h3
      have : (b : ℚ)⁻¹ ≤ 1/2 := by rw [one_div]; exact inv_le_inv_of_le (by norm_num) hb2
      linarith
    · have : (b : ℚ)⁻¹ ≤ 1/3 := by rw [one_div]; exact inv_le_inv_of_le (by norm_num) h3
      have : (a : ℚ)⁻¹ ≤ 1/2 := by rw [one_div]; exact inv_le_inv_of_le (by norm_num) ha2
      linarith

/-- No solution with |P| = 2 and |Q| = 3 exists among primes.
    PROVED: product ≤ (5/6)(31/30) = 31/36 < 1. -/
theorem no_two_three_solution :
    ¬∃ P Q : Finset ℕ, P.card = 2 ∧ Q.card = 3 ∧
      IsSetOfPrimes P ∧ IsSetOfPrimes Q ∧
      reciprocalProduct P Q = 1 := by
  intro ⟨P, Q, hP2, hQ3, hPprime, hQprime, hprod⟩
  have hP_le := reciprocal_sum_two_primes_le hP2 hPprime
  have hQ_le := reciprocal_sum_three_primes_le hQ3 hQprime
  have : reciprocalProduct P Q ≤ 31 / 36 := by
    unfold reciprocalProduct
    calc reciprocalSum P * reciprocalSum Q
        ≤ (5 / 6) * (31 / 30) := by
          apply mul_le_mul hP_le hQ_le
          · exact Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg i))
          · norm_num
      _ = 31 / 36 := by norm_num
  linarith

/- ## Part XII: Summary -/

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

/-
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
