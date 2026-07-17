import Mathlib

/-
# Erdős 307 — OQ-02: Sorry Elimination

## Research Problem: erdos-307-oq-02

OQ: Can the sorry theorems (disjointness, AM-GM bound, small case
non-existence) be proved in Lean from Mathlib?

The parent file has 4 sorries. This file eliminates 2 of them:
- no_two_three_solution: proved via tight prime reciprocal bound
- one_helps_balance: proved via reciprocal sum analysis

The remaining sorries (prime_sets_disjoint, prime_set_size_lower_bound)
require p-adic valuation theory and computational bounds on partial
sums of prime reciprocals — nontrivial but documented for future work.

Tags: number-theory, primes, egyptian-fractions
-/

open Finset BigOperators

namespace Erdos307OQ02

-- ============================================================
-- Part I: Setup (from parent)
-- ============================================================

/-- Sum of reciprocals of elements in a finite set. -/
noncomputable def reciprocalSum (S : Finset ℕ) : ℚ :=
  ∑ n ∈ S, (n : ℚ)⁻¹

/-- Product of two reciprocal sums. -/
noncomputable def reciprocalProduct (P Q : Finset ℕ) : ℚ :=
  reciprocalSum P * reciprocalSum Q

/-- A set of primes: all elements are prime. -/
def IsSetOfPrimes (S : Finset ℕ) : Prop :=
  ∀ n ∈ S, Nat.Prime n

-- ============================================================
-- Part II: Tight Bound for 3 Distinct Primes
-- ============================================================

/-- For 2 distinct primes, reciprocal sum ≤ 5/6.
    (Reproduced from parent for self-containment.) -/
private lemma reciprocal_sum_two_primes_le {P : Finset ℕ}
    (hcard : P.card = 2) (hP : IsSetOfPrimes P) :
    reciprocalSum P ≤ 5 / 6 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  simp only [reciprocalSum, Finset.sum_pair hab]
  have ha : Nat.Prime a := hP a (Finset.mem_insert_self a {b})
  have hb : Nat.Prime b := hP b (by simp)
  have ha2 : 2 ≤ a := ha.two_le
  have hb2 : 2 ≤ b := hb.two_le
  have hab3 : 3 ≤ a ∨ 3 ≤ b := by
    by_contra h; push_neg at h
    have hae : a = 2 := le_antisymm (by omega) ha2
    have hbe : b = 2 := le_antisymm (by omega) hb2
    exact hab (hae.trans hbe.symm)
  have ha_pos : (0 : ℚ) < a := by exact_mod_cast ha.pos
  have hb_pos : (0 : ℚ) < b := by exact_mod_cast hb.pos
  rcases hab3 with h3 | h3
  · have h1 : (a : ℚ)⁻¹ ≤ 1 / 3 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast h3)
    have h2 : (b : ℚ)⁻¹ ≤ 1 / 2 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast hb2)
    linarith
  · have h1 : (a : ℚ)⁻¹ ≤ 1 / 2 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast ha2)
    have h2 : (b : ℚ)⁻¹ ≤ 1 / 3 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast h3)
    linarith

/-- For 3 distinct primes, reciprocal sum ≤ 31/30.
    Maximum is 1/2 + 1/3 + 1/5 = 31/30.

    Proof: The three smallest distinct primes are 2, 3, 5.
    Since primes are ≥ 2 and distinct, the third-largest
    is ≥ 5 (it can't equal 2 or 3). -/
theorem reciprocal_sum_three_primes_le {Q : Finset ℕ}
    (hcard : Q.card = 3) (hQ : IsSetOfPrimes Q) :
    reciprocalSum Q ≤ 31 / 30 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  have ha : Nat.Prime a := hQ a (by simp)
  have hb : Nat.Prime b := hQ b (by simp)
  have hc : Nat.Prime c := hQ c (by simp)
  have ha2 : 2 ≤ a := ha.two_le
  have hb2 : 2 ≤ b := hb.two_le
  have hc2 : 2 ≤ c := hc.two_le
  have hsum : reciprocalSum ({a, b, c} : Finset ℕ)
      = (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ := by
    unfold reciprocalSum
    rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
      Finset.sum_singleton]
    ring
  rw [hsum]
  -- Among three distinct primes (all ≥ 2), at most one is 2
  -- and at most one is 3, so at least one is ≥ 5.
  -- The reciprocal sum is maximized at {2, 3, 5}: 1/2+1/3+1/5 = 31/30.
  -- Each reciprocal ≤ 1/2, and sum ≤ 1/2 + 1/3 + 1/5 = 31/30.
  have ha_pos : (0 : ℚ) < a := by exact_mod_cast ha.pos
  have hb_pos : (0 : ℚ) < b := by exact_mod_cast hb.pos
  have hc_pos : (0 : ℚ) < c := by exact_mod_cast hc.pos
  -- Each 1/p ≤ 1/2 (fallback bound for whichever variable isn't tightened below)
  have hha2 : (a : ℚ)⁻¹ ≤ 1/2 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast ha2)
  have hhb2 : (b : ℚ)⁻¹ ≤ 1/2 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast hb2)
  have hhc2 : (c : ℚ)⁻¹ ≤ 1/2 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast hc2)
  -- Pigeonhole: at least one of a, b, c is ≥ 5
  -- (Only primes < 5 are 2 and 3, so at most 2 of 3 distinct primes can be < 5)
  have h5 : 5 ≤ a ∨ 5 ≤ b ∨ 5 ≤ c := by
    by_contra h; push_neg at h
    obtain ⟨ha5, hb5, hc5⟩ := h
    interval_cases a <;> interval_cases b <;> interval_cases c <;>
      first
        | omega
        | exact absurd ha (by decide)
        | exact absurd hb (by decide)
        | exact absurd hc (by decide)
  -- For the one ≥ 5: reciprocal ≤ 1/5. Among the other two distinct primes,
  -- one is ≥ 3 (can't both be 2), so its reciprocal ≤ 1/3.
  -- Total ≤ 1/2 + 1/3 + 1/5 = 31/30.
  rcases h5 with h5a | h5b | h5c
  · have ha5 : (a : ℚ)⁻¹ ≤ 1/5 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast h5a)
    have h3 : 3 ≤ b ∨ 3 ≤ c := by omega
    rcases h3 with h3 | h3
    · have hb3 : (b : ℚ)⁻¹ ≤ 1/3 := by
        rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast h3)
      linarith
    · have hc3 : (c : ℚ)⁻¹ ≤ 1/3 := by
        rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast h3)
      linarith
  · have hb5 : (b : ℚ)⁻¹ ≤ 1/5 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast h5b)
    have h3 : 3 ≤ a ∨ 3 ≤ c := by omega
    rcases h3 with h3 | h3
    · have ha3 : (a : ℚ)⁻¹ ≤ 1/3 := by
        rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast h3)
      linarith
    · have hc3 : (c : ℚ)⁻¹ ≤ 1/3 := by
        rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast h3)
      linarith
  · have hc5 : (c : ℚ)⁻¹ ≤ 1/5 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast h5c)
    have h3 : 3 ≤ a ∨ 3 ≤ b := by omega
    rcases h3 with h3 | h3
    · have ha3 : (a : ℚ)⁻¹ ≤ 1/3 := by
        rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast h3)
      linarith
    · have hb3 : (b : ℚ)⁻¹ ≤ 1/3 := by
        rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast h3)
      linarith

-- ============================================================
-- Part III: No |P|=2, |Q|=3 Prime Solution (Sorry Elimination)
-- ============================================================

/-- No prime solution with |P| = 2 and |Q| = 3.
    Product ≤ (5/6)(31/30) = 155/180 = 31/36 < 1. -/
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

-- ============================================================
-- Part IV: 1 Helps Balance (Sorry Elimination)
-- ============================================================

/-- If 1 ∈ P and the product is 1, then reciprocalSum P > 1.
    Proof: reciprocalSum P = 1 + Σ_{p ∈ P\{1}} 1/p > 1
    since P must have other elements (otherwise product can't be 1).

    NOTE (soundness fix, migration v4.31): the original statement omitted the
    hypothesis that every element of `P` is positive. Without it the claim is
    false in general — e.g. `P = {0, 1}` has `card = 2 > 1`, `1 ∈ P`, but
    `reciprocalSum P = 1⁻¹ + 0⁻¹ = 1`, not `> 1` (Lean's `(0:ℚ)⁻¹ = 0` junk
    value). The parent file `Erdos307Problem.lean`'s `one_helps_balance`
    already carries this hypothesis (`hpos : ∀ p ∈ P, 0 < p`); it is restored
    here (this file's own docs call this hypothesis "slightly stronger" than
    the parent's, so its absence here was a drift bug, not a deliberate
    weakening). See #38611. -/
theorem one_helps_balance {P Q : Finset ℕ}
    (h1P : 1 ∈ P)
    (hP_nonempty : 1 < P.card)
    (hpos : ∀ p ∈ P, 0 < p)
    (hprod : reciprocalProduct P Q = 1) :
    reciprocalSum P > 1 := by
  unfold reciprocalSum
  -- Split P = {1} ∪ (P \ {1})
  have h_split : ∑ n ∈ P, (n : ℚ)⁻¹ =
      (1 : ℚ)⁻¹ + ∑ n ∈ P.erase 1, (n : ℚ)⁻¹ := by
    rw [← Finset.add_sum_erase P _ h1P]
    norm_num
  rw [h_split]
  simp only [inv_one]
  -- Need to show: 1 + Σ_{P\{1}} 1/n > 1, i.e., Σ_{P\{1}} 1/n > 0
  -- P \ {1} is nonempty since P.card > 1
  have h_erase_nonempty : (P.erase 1).Nonempty := by
    rw [Finset.erase_nonempty h1P]
    exact Finset.one_lt_card_iff_nontrivial.mp hP_nonempty
  -- Each term 1/n > 0, since every n ∈ P (hence n ∈ P.erase 1) is positive
  have h_pos : 0 < ∑ n ∈ P.erase 1, (n : ℚ)⁻¹ := by
    apply Finset.sum_pos
    · intro n hn
      exact inv_pos.mpr (Nat.cast_pos.mpr (hpos n (Finset.mem_of_mem_erase hn)))
    · exact h_erase_nonempty
  linarith

-- ============================================================
-- Part V: Product Rigidity (Axiom → Theorem)
-- ============================================================

/-- The product_rigidity "axiom" is a trivial equivalence:
    ∃Q with product=1 ⟺ ∃Q with sum = 1/sum(P).

    This follows from: a * b = 1 ⟺ b = 1/a. -/
theorem product_rigidity (P : Finset ℕ) (hP : IsSetOfPrimes P)
    (hcard : P.card > 0) :
    (∃ Q : Finset ℕ, IsSetOfPrimes Q ∧ reciprocalProduct P Q = 1) ↔
    ∃ Q : Finset ℕ, IsSetOfPrimes Q ∧
      reciprocalSum Q = (reciprocalSum P)⁻¹ := by
  unfold reciprocalProduct
  constructor
  · rintro ⟨Q, hQprime, hprod⟩
    refine ⟨Q, hQprime, ?_⟩
    have hP_pos : reciprocalSum P > 0 := by
      unfold reciprocalSum
      apply Finset.sum_pos
      · intro n hn
        have hp := hP n hn
        exact inv_pos.mpr (Nat.cast_pos.mpr hp.pos)
      · exact Finset.card_pos.mp hcard
    field_simp at hprod ⊢
    linarith
  · rintro ⟨Q, hQprime, hsum⟩
    refine ⟨Q, hQprime, ?_⟩
    have hP_pos : reciprocalSum P > 0 := by
      unfold reciprocalSum
      apply Finset.sum_pos
      · intro n hn
        have hp := hP n hn
        exact inv_pos.mpr (Nat.cast_pos.mpr hp.pos)
      · exact Finset.card_pos.mp hcard
    rw [hsum]
    exact mul_inv_cancel₀ (ne_of_gt hP_pos)

-- ============================================================
-- Part VI: Documentation of Remaining Sorries
-- ============================================================

/-
  What remains from the parent file:

  1. prime_sets_disjoint: If P, Q are prime sets with product 1, then P ∩ Q = ∅.
     Approach: p-adic valuation argument.
     If p₀ ∈ P ∩ Q, then v_{p₀}(∏P · ∏Q) ≥ 2, but the numerator of the
     product has v_{p₀} = 0 (since the "cross term" 1/p₀² contributes
     uniquely). This contradicts the product being 1.
     Status: requires Mathlib's p-adic valuation theory.

  2. prime_set_size_lower_bound: |P ∪ Q| ≥ 60.
     Approach: computational bound on Σ_{p≤281} 1/p ≈ 2.009.
     Need: Σ 1/p < 2 for the first 59 primes, and ≥ 2 for first 60.
     Status: requires verified computation or Mertens-type estimates.

  3. no_two_three_solution: PROVED in this file (reduces to product bound).
     The supporting lemma reciprocal_sum_three_primes_le is fully proved.

  4. one_helps_balance: PROVED in this file (with slightly stronger hypothesis).

  5. product_rigidity: PROVED in this file (was trivial iff).

  Score: 3 results proved, 2 remain (both requiring substantial Mathlib infra).
-/

/-
  Summary

  This file addresses OQ-02 from Erdős Problem #307:
  "Can the sorry theorems be proved from Mathlib?"

  Proved:
  - product_rigidity: trivial iff (was unnecessarily an axiom)
  - one_helps_balance: reciprocalSum P > 1 when 1 ∈ P
  - no_two_three_solution: no |P|=2, |Q|=3 prime solution
  - reciprocal_sum_three_primes_le: tight bound for 3 primes

  Remaining from parent:
  - prime_sets_disjoint: needs p-adic theory
  - prime_set_size_lower_bound: needs computational bound

  0 sorries, 0 axioms.
-/

end Erdos307OQ02
