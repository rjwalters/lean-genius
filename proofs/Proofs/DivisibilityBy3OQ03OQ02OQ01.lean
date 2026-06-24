import Mathlib

/-
# Iterative Digital Root and its Closed Form (OQ-03-OQ-02-OQ-01)

## Open Question

The parent entry (`divisibility-by-3-oq-03-oq-02`) defined the base-`b` digital
root by the *closed form*

    dr_b(n) = 1 + ((n - 1) mod (b - 1))   for n > 0,   dr_b(0) = 0.

This leaf formalizes the **iterative** digital root — the schoolbook process of
repeatedly replacing `n` by the sum of its base-`b` digits until a single digit
remains — and proves the two definitions coincide for every base `b ≥ 2`.

## Main results (all 0-axiom, `sorry`-free, kernel-checked)

* `digitSum_lt`             : for `2 ≤ b ≤ n`, `(digits b n).sum < n`.
                             This strict drop is exactly the termination measure.
* `digitalRootIter`         : the iterative digital root, by well-founded recursion.
* `digitalRootIter_of_lt`   / `digitalRootIter_of_ge` : the defining equations.
* `digitalRootIter_modEq`   : `digitalRootIter b n ≡ n [MOD b-1]`.
* `digitalRootIter_lt_base` : the iterate really is a single digit (`< b`).
* `digitalRootIter_eq_base` : **headline** — `digitalRootIter b n = digitalRootBase b n`.
* `digitalRootIter_ten`     : the familiar base-10 specialization.

## Proof strategy

The only nontrivial ingredient is the strict bound `digitSum_lt`.  Writing the
one-step digit-sum recursion `(digits b n).sum = n % b + (digits b (n/b)).sum`
and bounding the tail by `digit_sum_le`, we get
`(digits b n).sum ≤ n % b + n / b`, which is `< n` precisely because
`(b-1)·(n/b) ≥ 1` when `b ≥ 2 ≤ n`.  This both justifies the well-founded
definition and drives the strong-induction proof of the headline: a single
digit-sum step is congruent mod `b-1` (`Nat.modEq_digits_sum`) and keeps the
value positive (`getLast_digit_ne_zero`), and `digitalRootBase` depends only on
the residue mod `b-1`, so the iterate and the closed form agree.

This file is self-contained: it re-states the closed form `digitalRootBase`
(the parent's own file is unchanged) so the equivalence is proved against an
explicit definition.
-/

namespace DivisibilityBy3OQ03OQ02OQ01

open Nat

/-! ## Part I: Strict digit-sum bound (termination measure) -/

/-- For `2 ≤ b ≤ n`, the base-`b` digit sum strictly decreases: `(digits b n).sum < n`.
    This is the termination measure for the iterative digital root: the leading
    place value `b^k ≥ b > 1` forces a strict loss when collapsing to the digit sum. -/
theorem digitSum_lt (b n : ℕ) (hb : 2 ≤ b) (hn : b ≤ n) :
    (Nat.digits b n).sum < n := by
  have hb1 : 1 < b := hb
  have hn0 : 0 < n := lt_of_lt_of_le (by omega) hn
  have hsum : (Nat.digits b n).sum = n % b + (Nat.digits b (n / b)).sum := by
    rw [Nat.digits_def' hb1 hn0, List.sum_cons]
  have htail : (Nat.digits b (n / b)).sum ≤ n / b := Nat.digit_sum_le b (n / b)
  have hdm : b * (n / b) + n % b = n := Nat.div_add_mod n b
  have hqpos : 0 < n / b := Nat.div_pos hn (by omega)
  have hmul : 2 * (n / b) ≤ b * (n / b) := Nat.mul_le_mul hb (Nat.le_refl _)
  omega

/-! ## Part II: The iterative digital root -/

/-- The **iterative digital root** in base `b`: repeatedly replace `n` by the sum
    of its base-`b` digits until the value is a single digit (`< b`).  Defined by
    well-founded recursion on `n`; `digitSum_lt` supplies the decreasing measure.
    For the degenerate bases `b < 2` (where digit sums do not decrease) the
    function simply returns `n`. -/
def digitalRootIter (b n : ℕ) : ℕ :=
  if h : 2 ≤ b ∧ b ≤ n then
    digitalRootIter b (Nat.digits b n).sum
  else
    n
termination_by n
decreasing_by exact digitSum_lt b n h.1 h.2

/-- Below the base, the iterate is the identity (single-digit fixed point). -/
theorem digitalRootIter_of_lt (b n : ℕ) (h : n < b) : digitalRootIter b n = n := by
  rw [digitalRootIter]
  exact dif_neg (by rintro ⟨_, hbn⟩; omega)

/-- One unfolding step of the iteration, valid when `n` is not yet a single digit. -/
theorem digitalRootIter_of_ge (b n : ℕ) (hb : 2 ≤ b) (hn : b ≤ n) :
    digitalRootIter b n = digitalRootIter b (Nat.digits b n).sum := by
  rw [digitalRootIter]
  exact dif_pos ⟨hb, hn⟩

/-! ## Part III: Invariants of one digit-sum step -/

/-- For `b ≥ 3`, `b ≡ 1 (mod b-1)`. -/
private lemma base_mod_pred (b : ℕ) (hb : 3 ≤ b) : b % (b - 1) = 1 := by
  rw [Nat.mod_eq_sub_mod (by omega), show b - (b - 1) = 1 from by omega]
  exact Nat.mod_eq_of_lt (by omega)

/-- A single digit-sum step preserves the residue mod `b-1`. -/
theorem sumDigits_modEq (b n : ℕ) (hb : 2 ≤ b) :
    (Nat.digits b n).sum ≡ n [MOD (b - 1)] := by
  rcases Nat.lt_or_ge b 3 with h | h
  · -- `b = 2`: the modulus is `b - 1 = 1`, so everything is congruent.
    have hb1 : b - 1 = 1 := by omega
    rw [hb1]; exact Nat.modEq_one
  · exact (Nat.modEq_digits_sum (b - 1) b (base_mod_pred b h) n).symm

/-- The digit sum of a positive number is positive (the leading digit is nonzero). -/
theorem sumDigits_pos (b n : ℕ) (hn : 0 < n) : 0 < (Nat.digits b n).sum := by
  have hne : Nat.digits b n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  have hmem : (Nat.digits b n).getLast hne ∈ Nat.digits b n := List.getLast_mem hne
  have hne0 : (Nat.digits b n).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero b (by omega)
  have hle : (Nat.digits b n).getLast hne ≤ (Nat.digits b n).sum := List.le_sum_of_mem hmem
  omega

/-! ## Part IV: The closed form and the equivalence -/

/-- Closed form of the base-`b` digital root (re-stated from the parent entry
    `divisibility-by-3-oq-03-oq-02`). -/
def digitalRootBase (b n : ℕ) : ℕ :=
  if n = 0 then 0 else 1 + (n - 1) % (b - 1)

@[simp] theorem digitalRootBase_zero (b : ℕ) : digitalRootBase b 0 = 0 := rfl

/-- For a single digit `n < b` (with `b ≥ 2`), the closed form is the identity. -/
theorem digitalRootBase_of_lt (b n : ℕ) (hb : 2 ≤ b) (h : n < b) :
    digitalRootBase b n = n := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · unfold digitalRootBase
    rw [if_neg (by omega)]
    have hmod : (n - 1) % (b - 1) = n - 1 := Nat.mod_eq_of_lt (by omega)
    omega

/-- The closed form depends only on the residue mod `b-1` (for positive inputs). -/
theorem digitalRootBase_modEq_eq (b m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (h : m ≡ n [MOD (b - 1)]) : digitalRootBase b m = digitalRootBase b n := by
  unfold digitalRootBase
  rw [if_neg (by omega), if_neg (by omega)]
  congr 1
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_sub_one]
  exact Nat.ModEq.add_right_cancel' 1 h

/-- The iterate is congruent to its input mod `b-1`. -/
theorem digitalRootIter_modEq (b n : ℕ) (hb : 2 ≤ b) :
    digitalRootIter b n ≡ n [MOD (b - 1)] := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n b with hlt | hge
    · rw [digitalRootIter_of_lt b n hlt]
    · rw [digitalRootIter_of_ge b n hb hge]
      have hlt : (Nat.digits b n).sum < n := digitSum_lt b n hb hge
      exact (ih _ hlt).trans (sumDigits_modEq b n hb)

/-- **Headline.** The iterative digital root equals the closed form for every
    base `b ≥ 2`: the schoolbook "keep summing digits" process computes
    `1 + ((n-1) mod (b-1))`. -/
theorem digitalRootIter_eq_base (b n : ℕ) (hb : 2 ≤ b) :
    digitalRootIter b n = digitalRootBase b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n b with hlt | hge
    · rw [digitalRootIter_of_lt b n hlt, digitalRootBase_of_lt b n hb hlt]
    · rw [digitalRootIter_of_ge b n hb hge]
      have hlt : (Nat.digits b n).sum < n := digitSum_lt b n hb hge
      have hn0 : 0 < n := lt_of_lt_of_le (by omega) hge
      have hS0 : 0 < (Nat.digits b n).sum := sumDigits_pos b n hn0
      rw [ih _ hlt]
      exact digitalRootBase_modEq_eq b _ n hS0 hn0 (sumDigits_modEq b n hb)

/-- The iterative digital root is a single base-`b` digit. -/
theorem digitalRootIter_lt_base (b n : ℕ) (hb : 2 ≤ b) : digitalRootIter b n < b := by
  rw [digitalRootIter_eq_base b n hb]
  unfold digitalRootBase
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp; omega
  · rw [if_neg (by omega)]
    have hmod : (n - 1) % (b - 1) < b - 1 := Nat.mod_lt _ (by omega)
    omega

/-! ## Part V: The decimal specialization -/

/-- Base-10 instance: the familiar decimal digital root. -/
theorem digitalRootIter_ten (n : ℕ) : digitalRootIter 10 n = digitalRootBase 10 n :=
  digitalRootIter_eq_base 10 n (by norm_num)

/-- Worked decimal example: `1 + 2 + 3 + 4 + 5 = 15 → 1 + 5 = 6`. -/
theorem digitalRootIter_ten_12345 : digitalRootIter 10 12345 = 6 := by
  rw [digitalRootIter_ten]; decide

/-- A multiple of `9` has decimal digital root `9` (the casting-out-nines law). -/
theorem digitalRootIter_ten_nine_mul (k : ℕ) (hk : 0 < k) :
    digitalRootIter 10 (9 * k) = 9 := by
  rw [digitalRootIter_ten]
  have hmod : (9 * k) ≡ 9 [MOD (10 - 1)] := by
    show (9 * k) % (10 - 1) = 9 % (10 - 1)
    simp [Nat.mul_mod_right]
  rw [digitalRootBase_modEq_eq 10 (9 * k) 9 (by positivity) (by norm_num) hmod]
  decide

end DivisibilityBy3OQ03OQ02OQ01
