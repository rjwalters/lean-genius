/-
# Erdős #10 — WIP OQ-02: the equality case of binary-popcount subadditivity

The parent `Erdos10WIP01` proves **binary popcount is subadditive**,
`popcount (a + b) ≤ popcount a + popcount b` (`bitIndices_length_add_le`), where
`popcount n = (Nat.bitIndices n).length` is the number of binary 1-bits.

This file answers the open question **when equality holds**:

> `popcount (a + b) = popcount a + popcount b  ↔  a &&& b = 0`

i.e. equality holds **exactly** when `a` and `b` have disjoint binary supports (no
carries: a carry is *born* only at a position where both operands have a 1-bit).
The seeker's other proposed target — a matching lower bound
`popcount(a+b) ≥ |popcount a − popcount b|` — is **false** (`(a,b) = (1,7)`:
`popcount 8 = 1 < |1 − 3| = 2`), so the equality characterization is the correct
well-posed statement.

The proof is self-contained (Mathlib only) and 0-axiom. It re-derives subadditivity
`popcount_add_le` directly by a binary parity strong induction (rather than through the
parent's `RepWithAtMost` machinery), using the popcount recursions
`popcount (2n) = popcount n`, `popcount (2n+1) = popcount n + 1` and the `&&&` bit
recursions `(2a)&&&(2b) = 2(a&&&b)`, `(2a+1)&&&(2b) = 2(a&&&b)`,
`(2a+1)&&&(2b+1) = 2(a&&&b)+1`. The same induction then proves the equality
characterization: in the odd/odd case a carry is born (`a &&& b` is odd, hence nonzero)
and popcount strictly drops, so both sides are false; the other three parity cases reduce
to the inductive hypothesis on the halved sum. The strict corollary
`popcount_add_lt` (`a &&& b ≠ 0 ⇒ popcount(a+b) < popcount a + popcount b`) falls out.

Tags: number-theory, binary, popcount, additive-combinatorics, carries, erdos
-/
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.BitIndices

open Nat

namespace Erdos10WIP01OQ02

/-- Binary popcount: the number of 1-bits, as the length of the sorted bit-index list. -/
def popcount (n : ℕ) : ℕ := (Nat.bitIndices n).length

@[simp] theorem popcount_zero : popcount 0 = 0 := by simp [popcount]
@[simp] theorem popcount_one : popcount 1 = 1 := by simp [popcount]

theorem popcount_two_mul (n : ℕ) : popcount (2 * n) = popcount n := by
  simp [popcount, bitIndices_two_mul]

theorem popcount_two_mul_add_one (n : ℕ) : popcount (2 * n + 1) = popcount n + 1 := by
  simp [popcount, bitIndices_two_mul_add_one]

/-! ### `&&&` bit recursions -/

theorem and_two_mul (a b : ℕ) : (2*a) &&& (2*b) = 2*(a &&& b) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero => simp [Nat.testBit_and, Nat.testBit_zero, Nat.mul_mod_right]
  | succ j =>
      rw [Nat.testBit_and]
      simp [Nat.testBit_succ, Nat.testBit_and, Nat.mul_div_cancel_left, Nat.mul_add_div]

theorem and_two_mul_add_one_left (a b : ℕ) : (2*a+1) &&& (2*b) = 2*(a &&& b) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero => simp [Nat.testBit_and, Nat.testBit_zero, Nat.mul_mod_right]
  | succ j =>
      rw [Nat.testBit_and]
      simp [Nat.testBit_succ, Nat.testBit_and, Nat.mul_div_cancel_left, Nat.mul_add_div]

theorem and_two_mul_add_one_both (a b : ℕ) : (2*a+1) &&& (2*b+1) = 2*(a &&& b)+1 := by
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero => simp [Nat.testBit_and, Nat.testBit_zero]
  | succ j =>
      rw [Nat.testBit_and]
      simp [Nat.testBit_succ, Nat.testBit_and, Nat.mul_div_cancel_left, Nat.mul_add_div]

/-! ### Subadditivity, via the parity strong induction (self-contained) -/

theorem popcount_add_le : ∀ (a b : ℕ), popcount (a + b) ≤ popcount a + popcount b := by
  have key : ∀ n a b, a + b = n → popcount (a + b) ≤ popcount a + popcount b := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro a b hab
      -- base
      rcases Nat.eq_zero_or_pos (a + b) with h0 | hpos
      · obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
        simp
      subst hab
      -- parity cases
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
        rcases Nat.mod_two_eq_zero_or_one b with hb | hb
      · -- a even, b even
        obtain ⟨qa, rfl⟩ : ∃ q, a = 2 * q := ⟨a/2, by omega⟩
        obtain ⟨qb, rfl⟩ : ∃ q, b = 2 * q := ⟨b/2, by omega⟩
        have he : 2 * qa + 2 * qb = 2 * (qa + qb) := by omega
        rw [he, popcount_two_mul, popcount_two_mul, popcount_two_mul]
        exact IH (qa + qb) (by omega) qa qb rfl
      · -- a even, b odd
        obtain ⟨qa, rfl⟩ : ∃ q, a = 2 * q := ⟨a/2, by omega⟩
        obtain ⟨qb, rfl⟩ : ∃ q, b = 2 * q + 1 := ⟨b/2, by omega⟩
        have he : 2 * qa + (2 * qb + 1) = 2 * (qa + qb) + 1 := by omega
        rw [he, popcount_two_mul_add_one, popcount_two_mul, popcount_two_mul_add_one]
        have := IH (qa + qb) (by omega) qa qb rfl
        omega
      · -- a odd, b even
        obtain ⟨qa, rfl⟩ : ∃ q, a = 2 * q + 1 := ⟨a/2, by omega⟩
        obtain ⟨qb, rfl⟩ : ∃ q, b = 2 * q := ⟨b/2, by omega⟩
        have he : 2 * qa + 1 + 2 * qb = 2 * (qa + qb) + 1 := by omega
        rw [he, popcount_two_mul_add_one, popcount_two_mul_add_one, popcount_two_mul]
        have := IH (qa + qb) (by omega) qa qb rfl
        omega
      · -- a odd, b odd
        obtain ⟨qa, rfl⟩ : ∃ q, a = 2 * q + 1 := ⟨a/2, by omega⟩
        obtain ⟨qb, rfl⟩ : ∃ q, b = 2 * q + 1 := ⟨b/2, by omega⟩
        have he : 2 * qa + 1 + (2 * qb + 1) = 2 * (qa + qb + 1) := by omega
        rw [he, popcount_two_mul, popcount_two_mul_add_one, popcount_two_mul_add_one]
        have h1 : popcount (qa + (qb + 1)) ≤ popcount qa + popcount (qb + 1) :=
          IH (qa + (qb + 1)) (by omega) qa (qb + 1) rfl
        have h2 : popcount (qb + 1) ≤ popcount qb + popcount 1 :=
          IH (qb + 1) (by omega) qb 1 rfl
        have hqq : qa + (qb + 1) = qa + qb + 1 := by omega
        rw [hqq] at h1
        simp only [popcount_one] at h2
        omega
  intro a b; exact key (a + b) a b rfl

/-! ### The equality characterization: no carries ⟺ disjoint binary supports -/

theorem popcount_add_eq_iff : ∀ (a b : ℕ),
    popcount (a + b) = popcount a + popcount b ↔ a &&& b = 0 := by
  have key : ∀ n a b, a + b = n →
      (popcount (a + b) = popcount a + popcount b ↔ a &&& b = 0) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro a b hab
      rcases Nat.eq_zero_or_pos (a + b) with h0 | hpos
      · obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
        simp
      subst hab
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
        rcases Nat.mod_two_eq_zero_or_one b with hb | hb
      · -- even, even
        obtain ⟨qa, rfl⟩ : ∃ q, a = 2 * q := ⟨a/2, by omega⟩
        obtain ⟨qb, rfl⟩ : ∃ q, b = 2 * q := ⟨b/2, by omega⟩
        have he : 2 * qa + 2 * qb = 2 * (qa + qb) := by omega
        rw [he, popcount_two_mul, popcount_two_mul, popcount_two_mul, and_two_mul]
        have hIH := IH (qa + qb) (by omega) qa qb rfl
        constructor
        · intro h; have := hIH.mp (by omega); omega
        · intro h; have := hIH.mpr (by omega); omega
      · -- even, odd
        obtain ⟨qa, rfl⟩ : ∃ q, a = 2 * q := ⟨a/2, by omega⟩
        obtain ⟨qb, rfl⟩ : ∃ q, b = 2 * q + 1 := ⟨b/2, by omega⟩
        have he : 2 * qa + (2 * qb + 1) = 2 * (qa + qb) + 1 := by omega
        have hand : (2 * qa) &&& (2 * qb + 1) = 2 * (qa &&& qb) := by
          rw [Nat.and_comm (2 * qa) (2 * qb + 1), and_two_mul_add_one_left, Nat.and_comm qb qa]
        rw [he, popcount_two_mul_add_one, popcount_two_mul, popcount_two_mul_add_one, hand]
        have hIH := IH (qa + qb) (by omega) qa qb rfl
        constructor
        · intro h; have := hIH.mp (by omega); omega
        · intro h; have := hIH.mpr (by omega); omega
      · -- odd, even
        obtain ⟨qa, rfl⟩ : ∃ q, a = 2 * q + 1 := ⟨a/2, by omega⟩
        obtain ⟨qb, rfl⟩ : ∃ q, b = 2 * q := ⟨b/2, by omega⟩
        have he : 2 * qa + 1 + 2 * qb = 2 * (qa + qb) + 1 := by omega
        rw [he, popcount_two_mul_add_one, popcount_two_mul_add_one, popcount_two_mul,
            and_two_mul_add_one_left]
        have hIH := IH (qa + qb) (by omega) qa qb rfl
        constructor
        · intro h; have := hIH.mp (by omega); omega
        · intro h; have := hIH.mpr (by omega); omega
      · -- odd, odd : both sides false (a &&& b is odd, popcount strictly drops)
        obtain ⟨qa, rfl⟩ : ∃ q, a = 2 * q + 1 := ⟨a/2, by omega⟩
        obtain ⟨qb, rfl⟩ : ∃ q, b = 2 * q + 1 := ⟨b/2, by omega⟩
        have he : 2 * qa + 1 + (2 * qb + 1) = 2 * (qa + qb + 1) := by omega
        rw [he, popcount_two_mul, popcount_two_mul_add_one, popcount_two_mul_add_one,
            and_two_mul_add_one_both]
        apply iff_of_false
        · have hle := popcount_add_le qa (qb + 1)
          have hqq : qa + (qb + 1) = qa + qb + 1 := by omega
          rw [hqq] at hle
          have h1 := popcount_add_le qb 1
          simp only [popcount_one] at h1
          omega
        · omega
  intro a b; exact key (a + b) a b rfl

/-- **Strict subadditivity when supports overlap.** If `a` and `b` share a 1-bit
(`a &&& b ≠ 0`), the binary popcount strictly drops under addition (carries annihilate bits). -/
theorem popcount_add_lt (a b : ℕ) (h : a &&& b ≠ 0) :
    popcount (a + b) < popcount a + popcount b :=
  lt_of_le_of_ne (popcount_add_le a b) (fun heq => h ((popcount_add_eq_iff a b).mp heq))

/-! ### Axiom audit -/

#print axioms popcount_add_eq_iff
#print axioms popcount_add_lt
#print axioms popcount_add_le

end Erdos10WIP01OQ02

