/-
# Chebyshev–PNT bridge, OQ-01-OQ-04: multinomial prime-power bounds

This file addresses the open question:

  *Does the carry-counting bound `p^{v_p(C(2n,n))} ≤ 2n` generalize to the
  multinomial coefficient `C(kn; n,…,n) = (kn)!/(n!)^k`, giving `p^{v_p} ≤ kn`?*

The central-binomial bound (Mathlib `Nat.pow_factorization_choose_le`) is a
Kummer/Legendre consequence: the number of base-`p` carries when adding `n + n`
is at most `log_p (2n)`, so `p^{v_p(C(2n,n))} ≤ 2n`.

## Results

* `multiProd_mul_pow_factorial` — the identity
  `(∏_{j=1}^{k} C(jn, n)) · (n!)^k = (kn)!`, i.e. the product of binomials
  `∏_{j=1}^{k} C(jn, n)` equals the multinomial coefficient `(kn)!/(n!)^k`.
  (Standard telescoping identity; proved here by induction on `k`.)

* `multiProd_prime_pow_le` — the **correct** Kummer-type bound:
  `p ^ v_p(∏_{j=1}^{k} C(jn,n)) ≤ n^k · k!`.
  This is the honest generalization: `v_p` of a product is the sum of the
  `v_p`'s, and each factor obeys `p^{v_p(C(jn,n))} ≤ jn`, so the product is at
  most `∏_{j=1}^{k} (jn) = n^k · k!`.

* `naive_multinomial_bound_false` — the **refutation** of the naively conjectured
  generalization `p^{v_p} ≤ kn`. It is FALSE. Smallest witness: `k = 3, n = 2,
  p = 3`, where the multinomial coefficient is `90 = 2 · 3² · 5`, so
  `p^{v_p} = 3² = 9 > 6 = kn`. (The product bound `n^k·k! = 48` is respected.)

The takeaway: the central-binomial bound is special because `v_p` telescopes over
a *two-term* sum; for `k ≥ 3` terms the carries accumulate and the bound `kn`
must be replaced by the multiplicative bound `n^k · k!` (equivalently, by the
weaker `(kn)^{k-1}`).
-/
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

open Nat Finset

namespace ChebyshevPNTBridgeOQ01OQ04

/-- `multiProd k n = ∏_{j=1}^{k} C(jn, n)`.  By the telescoping identity below
this equals the multinomial coefficient `(kn)! / (n!)^k`. -/
def multiProd (k n : ℕ) : ℕ := ∏ j ∈ Finset.Icc 1 k, (j * n).choose n

@[simp] lemma multiProd_zero (n : ℕ) : multiProd 0 n = 1 := by
  simp [multiProd]

/-- One-step unfolding: `multiProd (k+1) n = multiProd k n · C((k+1)n, n)`. -/
lemma multiProd_succ (k n : ℕ) :
    multiProd (k + 1) n = multiProd k n * (((k + 1) * n).choose n) := by
  unfold multiProd
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1)]

/-- **Product–multinomial identity.**  The product of binomials
`∏_{j=1}^{k} C(jn, n)` equals `(kn)! / (n!)^k`, stated multiplicatively:
`(∏_{j=1}^{k} C(jn, n)) · (n!)^k = (kn)!`. -/
lemma multiProd_mul_pow_factorial (k n : ℕ) :
    multiProd k n * (n !) ^ k = (k * n)! := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hle : n ≤ (k + 1) * n := le_mul_of_one_le_left (Nat.zero_le n) (by omega)
    have hsub : (k + 1) * n - n = k * n := by
      have : (k + 1) * n = k * n + n := by ring
      omega
    have key := Nat.choose_mul_factorial_mul_factorial hle
    rw [hsub] at key
    -- key : ((k+1)*n).choose n * n ! * (k*n)! = ((k+1)*n)!
    calc multiProd (k + 1) n * (n !) ^ (k + 1)
        = (multiProd k n * (n !) ^ k) * (((k + 1) * n).choose n * n !) := by
          rw [multiProd_succ, pow_succ]; ring
      _ = (k * n)! * (((k + 1) * n).choose n * n !) := by rw [ih]
      _ = ((k + 1) * n).choose n * n ! * (k * n)! := by ring
      _ = ((k + 1) * n)! := key

/-- Auxiliary: `∏_{j=1}^{k} (jn) = n^k · k!`. -/
lemma prod_Icc_mul_const (k n : ℕ) :
    ∏ j ∈ Finset.Icc 1 k, (j * n) = n ^ k * k ! := by
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_Icc_id_eq_factorial,
    Nat.card_Icc, Nat.add_sub_cancel]
  ring

/-- **Correct Kummer-type bound.**  For every prime power `p` (indeed every
`p`), the highest power of `p` dividing `∏_{j=1}^{k} C(jn, n) = (kn)!/(n!)^k`
is at most `n^k · k!`:
`p ^ v_p(multiProd k n) ≤ n^k · k!`.

This is the honest generalization of `Nat.pow_factorization_choose_le`
(`p^{v_p(C(2n,n))} ≤ 2n`) to `k`-fold multinomial coefficients. -/
theorem multiProd_prime_pow_le (k n p : ℕ) (hn : 0 < n) :
    p ^ ((multiProd k n).factorization p) ≤ n ^ k * k ! := by
  have hne : ∀ j ∈ Finset.Icc 1 k, (j * n).choose n ≠ 0 := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have : n ≤ j * n := le_mul_of_one_le_left (Nat.zero_le n) (by omega)
    exact (Nat.choose_pos this).ne'
  -- v_p of the product is the sum of the v_p's
  have hsum : (multiProd k n).factorization p
      = ∑ j ∈ Finset.Icc 1 k, ((j * n).choose n).factorization p := by
    unfold multiProd
    rw [Nat.factorization_prod hne]
    exact Finsupp.finset_sum_apply _ _ _
  rw [hsum, ← Finset.prod_pow_eq_pow_sum, ← prod_Icc_mul_const]
  apply Finset.prod_le_prod
  · intro i _; exact Nat.zero_le _
  · intro j hj
    rw [Finset.mem_Icc] at hj
    exact Nat.pow_factorization_choose_le (mul_pos (by omega) hn)

/-- **Refutation of the naive generalization.**  The conjectured bound
`p ^ v_p(multiProd k n) ≤ k · n` (the direct analogue of the central-binomial
bound `≤ 2n`) is FALSE.

Witness: `k = 3, n = 2, p = 3`.  Here `multiProd 3 2 = C(2,2)·C(4,2)·C(6,2)
= 1·6·15 = 90 = 2 · 3² · 5`, so `v_3 = 2` and `3² = 9 > 6 = 3·2`. -/
theorem naive_multinomial_bound_false :
    ¬ ∀ (k n p : ℕ), 0 < n → p.Prime →
      p ^ ((multiProd k n).factorization p) ≤ k * n := by
  intro h
  have hp : Nat.Prime 3 := by norm_num
  -- The identity pins down the value: multiProd 3 2 · (2!)^3 = 6!, i.e. · 8 = 720.
  have hval : multiProd 3 2 = 90 := by
    have hid := multiProd_mul_pow_factorial 3 2
    have e1 : (2 !) ^ 3 = 8 := by decide
    have e2 : (3 * 2)! = 720 := by decide
    rw [e1, e2] at hid
    omega
  -- 3² ∣ 90, so v₃(90) ≥ 2.
  have hfact : 2 ≤ (multiProd 3 2).factorization 3 := by
    rw [hval]
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp (by norm_num)).mp (by norm_num)
  -- The (false) hypothesis at k=3, n=2, p=3 gives 3^{v₃} ≤ 6.
  have hle := h 3 2 3 (by norm_num) hp
  have h9 : (9 : ℕ) ≤ 3 ^ ((multiProd 3 2).factorization 3) := by
    calc (9 : ℕ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ ((multiProd 3 2).factorization 3) :=
          Nat.pow_le_pow_right (by norm_num) hfact
  omega

end ChebyshevPNTBridgeOQ01OQ04
