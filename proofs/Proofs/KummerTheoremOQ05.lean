import Mathlib

/-
# Kummer's digit-sum criterion for binomial coefficients

The companion gallery entry `kummer-theorem` records Legendre's factorial
identity in digit-sum form,

  `(p - 1) * ν_p(n!) = n - S_p(n)`            (`legendre_digit_sum`),

where `S_p(m) = (p.digits m).sum` is the sum of the base-`p` digits of `m`, but
leaves the **binomial** side as a docstring remark.  This file completes it.

The starting point is the elementary factorization
`C(n,k) · k! · (n-k)! = n!` (`Nat.choose_mul_factorial_mul_factorial`).  Taking
`p`-adic valuations turns the product into a sum,

  `ν_p C(n,k) + ν_p(k!) + ν_p((n-k)!) = ν_p(n!)`,

and multiplying by `(p - 1)` and substituting Legendre three times gives, after
cancelling `k + (n-k) = n`, the exact (untruncated) identity

  `S_p(n) + (p - 1) · ν_p C(n,k) = S_p(k) + S_p(n-k)`   (`digit_sum_padicValNat_choose`).

From this single equation everything else drops out by linear arithmetic:

* the classical **Kummer digit-sum formula**
  `(p - 1) · ν_p C(n,k) = S_p(k) + S_p(n-k) - S_p(n)` (`sub_one_mul_padicValNat_choose`);
* the **subadditivity of digit sums** across a split `n = k + (n-k)`,
  `S_p(n) ≤ S_p(k) + S_p(n-k)` (`digit_sum_add_le`), a fact interesting in its own
  right (the digit sum can only *decrease* under carries); and
* the **divisibility criterion** `p ∤ C(n,k) ↔ S_p(k) + S_p(n-k) = S_p(n)`
  (`not_dvd_choose_iff_digit_sum_add`): a prime fails to divide `C(n,k)` exactly
  when adding `k` and `n-k` in base `p` produces no carries (each carry costs the
  digit sum `p-1` and forces one factor of `p`).

The central valuation identity `(p-1)·ν_p C(n,k) = S_p(k)+S_p(n-k)-S_p(n)` is
already available in Mathlib as `sub_one_mul_padicValNat_choose_eq_sub_sum_digits`;
the contribution here is the untruncated ordered form, the subadditivity corollary,
and the clean divisibility criterion, all assembled over the parent's Legendre
identity.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open Nat

namespace KummerTheorem

/-- **Exact (untruncated) Kummer digit-sum identity.**  For `k ≤ n` and a prime
`p`, the base-`p` digit sums of `k`, `n - k`, and `n` are linked to the `p`-adic
valuation of the binomial coefficient by

  `S_p(n) + (p - 1) · ν_p C(n,k) = S_p(k) + S_p(n-k)`.

This is the binomial companion of the parent's `legendre_digit_sum`.  It is stated
without truncated subtraction, so both the classical formula and the subadditivity
of digit sums follow from it by `omega`.

Proof: `C(n,k)·k!·(n-k)! = n!`, so `ν_p` is additive across the three factors;
multiplying by `p - 1` and substituting Legendre's factorial identity three times
cancels `k + (n-k) = n`. -/
theorem digit_sum_padicValNat_choose {p n k : ℕ} [Fact p.Prime] (h : k ≤ n) :
    (p.digits n).sum + (p - 1) * padicValNat p (n.choose k)
      = (p.digits k).sum + (p.digits (n - k)).sum := by
  -- `C(n,k)·k!·(n-k)! = n!`, with all three factors nonzero.
  have hCne : n.choose k ≠ 0 := (Nat.choose_pos h).ne'
  have hkf : (k ! : ℕ) ≠ 0 := Nat.factorial_ne_zero k
  have hnkf : ((n - k)! : ℕ) ≠ 0 := Nat.factorial_ne_zero (n - k)
  have hprod : n.choose k * k ! * (n - k)! = n ! :=
    Nat.choose_mul_factorial_mul_factorial h
  -- Additivity of `padicValNat` across the product.
  have hadd : padicValNat p (n.choose k) + padicValNat p (k !)
        + padicValNat p ((n - k)!) = padicValNat p (n !) := by
    rw [← hprod, padicValNat.mul (mul_ne_zero hCne hkf) hnkf, padicValNat.mul hCne hkf]
  -- Multiply the additive relation by `(p - 1)` and distribute.
  have hmul : (p - 1) * padicValNat p (n.choose k)
        + (p - 1) * padicValNat p (k !)
        + (p - 1) * padicValNat p ((n - k)!)
      = (p - 1) * padicValNat p (n !) := by
    have h2 : (p - 1) * (padicValNat p (n.choose k) + padicValNat p (k !)
        + padicValNat p ((n - k)!)) = (p - 1) * padicValNat p (n !) := by rw [hadd]
    simpa [mul_add] using h2
  -- Legendre's factorial identity (digit-sum form) for each factorial.
  have leg_k := sub_one_mul_padicValNat_factorial (p := p) k
  have leg_nk := sub_one_mul_padicValNat_factorial (p := p) (n - k)
  have leg_n := sub_one_mul_padicValNat_factorial (p := p) n
  -- Digit sums never exceed their number, so the truncated subtractions are honest.
  have hbk : (p.digits k).sum ≤ k := Nat.digit_sum_le p k
  have hbnk : (p.digits (n - k)).sum ≤ n - k := Nat.digit_sum_le p (n - k)
  have hbn : (p.digits n).sum ≤ n := Nat.digit_sum_le p n
  omega

/-- **Kummer's digit-sum formula** (classical, truncated form).  For `k ≤ n`,

  `(p - 1) · ν_p C(n,k) = S_p(k) + S_p(n-k) - S_p(n)`.

Equivalently `ν_p C(n,k)` is the number of carries when adding `k` and `n - k` in
base `p`, since each carry lowers the digit sum by exactly `p - 1`.  (Matches
Mathlib's `sub_one_mul_padicValNat_choose_eq_sub_sum_digits`.) -/
theorem sub_one_mul_padicValNat_choose {p n k : ℕ} [Fact p.Prime] (h : k ≤ n) :
    (p - 1) * padicValNat p (n.choose k)
      = (p.digits k).sum + (p.digits (n - k)).sum - (p.digits n).sum := by
  have key := digit_sum_padicValNat_choose (p := p) h
  omega

/-- **Subadditivity of digit sums across a split.**  For `k ≤ n` and prime `p`,

  `S_p(n) ≤ S_p(k) + S_p(n-k)`.

Writing `n = k + (n-k)`, the base-`p` digit sum of the whole never exceeds the sum
of the digit sums of the parts: carries can only decrease it.  Immediate from the
untruncated identity, since `(p - 1) · ν_p C(n,k) ≥ 0`. -/
theorem digit_sum_add_le {p n k : ℕ} [Fact p.Prime] (h : k ≤ n) :
    (p.digits n).sum ≤ (p.digits k).sum + (p.digits (n - k)).sum := by
  have key := digit_sum_padicValNat_choose (p := p) h
  omega

/-- **Kummer's divisibility criterion.**  For `k ≤ n` and a prime `p`,

  `p ∤ C(n,k) ↔ S_p(k) + S_p(n-k) = S_p(n)`.

A prime `p` fails to divide `C(n,k)` exactly when adding `k` and `n - k` in base
`p` produces no carries — equivalently, when the digit sums add without loss.  This
is the binomial (Lucas-type) sharpening of the digit-sum identity: divisibility is
detected purely by comparing digit sums. -/
theorem not_dvd_choose_iff_digit_sum_add {p n k : ℕ} [Fact p.Prime] (h : k ≤ n) :
    ¬ p ∣ n.choose k ↔
      (p.digits k).sum + (p.digits (n - k)).sum = (p.digits n).sum := by
  have key := digit_sum_padicValNat_choose (p := p) h
  have hCne : n.choose k ≠ 0 := (Nat.choose_pos h).ne'
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  rw [dvd_iff_padicValNat_ne_zero hCne, not_not]
  constructor
  · intro h0
    have hz : (p - 1) * padicValNat p (n.choose k) = 0 := by rw [h0, Nat.mul_zero]
    omega
  · intro heq
    have hz : (p - 1) * padicValNat p (n.choose k) = 0 := by omega
    rcases Nat.mul_eq_zero.mp hz with h1 | h2
    · omega
    · exact h2

end KummerTheorem
