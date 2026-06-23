import Proofs.BaselProblemOQ01OQ01OQ02OQ01
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic

/-
# Apéry numbers: an axiom-free geometric UPPER bound, and parity

## Context
The companion file `BaselProblemOQ01OQ01OQ02OQ01.lean` builds the Apéry
`b`-sequence
    bₙ = ∑_{k=0}^{n} C(n,k)² · C(n+k,k)²            (1, 5, 73, 1445, 33001, …)
and proves the **lower** half of the geometric squeeze that drives Apéry's
irrationality proof for ζ(3): `4ⁿ ≤ bₙ` (and a sharper rate-16 bound).  The
parent irrationality file `BaselProblemOQ01OQ01OQ02.lean` supplies the
**upper** half only as an *axiom*: a recurrence-based bound `bₙ ≤ 34ⁿ`.

This file removes the need for that axiom on the elementary side by proving a
fully self-contained, 0-axiom geometric upper bound, and — separately — pins
the *parity* of every Apéry number.

## What is proved (all 0-axiom, 0-sorry)
* `sum_choose_sq` — Vandermonde on the diagonal: `∑_{k} C(n,k)² = C(2n,n)`.
* `aperyB_le_centralBinom_cube` — `bₙ ≤ C(2n,n)³`.  Every `C(n+k,k)` is
  dominated by the central coefficient `C(2n,n)`, and the leftover row
  `∑ C(n,k)²` collapses to `C(2n,n)` by Vandermonde — so no polynomial factor
  survives.
* `centralBinom_le_four_pow` — `C(2n,n) ≤ 4ⁿ` (drop to a single term of
  `∑_i C(2n,i) = 2^{2n}`).
* `aperyB_le_64_pow` — `bₙ ≤ 64ⁿ`, a clean axiom-free geometric upper bound.
  Combined with the parent's `4ⁿ ≤ bₙ`, this brackets the exponential base of
  the Apéry numbers in `[4, 64]` with zero axioms (the true base is the
  irrational `(1+√2)⁴ = 17+12√2 ≈ 33.97`).
* `two_dvd_choose_mul` — for `k ≥ 1`, `C(n,k)·C(n+k,k)` is even.  Key identity:
  the trinomial-revision `C(n,k)·C(n+k,k) = C(n+k,2k)·C(2k,k)` exposes the
  central factor `C(2k,k)`, which is even for `k ≥ 1`.
* `aperyB_odd` — **every Apéry number is odd.**  Modulo 2 only the `k = 0`
  summand (`= 1`) survives; all others carry the even factor above.

Reference: Apéry (1979); van der Poorten, *A proof that Euler missed* (1979).
-/

open BigOperators Finset Nat

namespace AperyCentralBinom

-- ============================================================================
-- Vandermonde on the diagonal: the squared binomial row sums to C(2n,n)
-- ============================================================================

/-- Vandermonde's identity specialised to the diagonal:
`∑_{k=0}^{n} C(n,k)² = C(2n,n) = centralBinom n`.  (Pair the `k`-th term with the
`(n-k)`-th term in the antidiagonal expansion of `(n+n).choose n`.) -/
theorem sum_choose_sq (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k) ^ 2 = Nat.centralBinom n := by
  rw [Nat.centralBinom_eq_two_mul_choose, two_mul, Nat.add_choose_eq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  rw [Nat.choose_symm hk, pow_two]

-- ============================================================================
-- The geometric UPPER bound
-- ============================================================================

/-- `bₙ ≤ C(2n,n)³`.  Each `C(n+k,k)` (for `k ≤ n`) is bounded by the central
coefficient, and the residual `∑ C(n,k)²` is itself `C(2n,n)` by Vandermonde. -/
theorem aperyB_le_centralBinom_cube (n : ℕ) :
    aperyB n ≤ (Nat.centralBinom n) ^ 3 := by
  have key : aperyB n
      ≤ ∑ k ∈ range (n + 1), (n.choose k) ^ 2 * (Nat.centralBinom n) ^ 2 := by
    unfold aperyB
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    have hb : (n + k).choose k ≤ Nat.centralBinom n :=
      le_trans (Nat.choose_le_choose k (by omega)) (Nat.choose_le_centralBinom k n)
    exact Nat.mul_le_mul (Nat.le_refl _) (Nat.pow_le_pow_left hb 2)
  calc aperyB n
      ≤ ∑ k ∈ range (n + 1), (n.choose k) ^ 2 * (Nat.centralBinom n) ^ 2 := key
    _ = (∑ k ∈ range (n + 1), (n.choose k) ^ 2) * (Nat.centralBinom n) ^ 2 := by
        rw [← Finset.sum_mul]
    _ = Nat.centralBinom n * (Nat.centralBinom n) ^ 2 := by rw [sum_choose_sq]
    _ = (Nat.centralBinom n) ^ 3 := by ring

/-- `C(2n,n) ≤ 4ⁿ`.  Drop to a single term of `∑_i C(2n,i) = 2^{2n} = 4ⁿ`. -/
theorem centralBinom_le_four_pow (n : ℕ) : Nat.centralBinom n ≤ 4 ^ n := by
  have h : Nat.centralBinom n ≤ 2 ^ (2 * n) := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    calc (2 * n).choose n
        ≤ ∑ i ∈ range (2 * n + 1), (2 * n).choose i :=
          Finset.single_le_sum (fun i _ => Nat.zero_le _)
            (Finset.mem_range.mpr (by omega))
      _ = 2 ^ (2 * n) := Nat.sum_range_choose (2 * n)
  calc Nat.centralBinom n
      ≤ 2 ^ (2 * n) := h
    _ = 4 ^ n := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]

/-- Clean axiom-free geometric upper bound: `bₙ ≤ 64ⁿ`.  With the parent's
`4ⁿ ≤ bₙ` this brackets the Apéry exponential base in `[4, 64]`. -/
theorem aperyB_le_64_pow (n : ℕ) : aperyB n ≤ 64 ^ n := by
  calc aperyB n
      ≤ (Nat.centralBinom n) ^ 3 := aperyB_le_centralBinom_cube n
    _ ≤ (4 ^ n) ^ 3 := Nat.pow_le_pow_left (centralBinom_le_four_pow n) 3
    _ = 64 ^ n := by
        rw [show (64 : ℕ) = 4 ^ 3 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]

-- ============================================================================
-- Parity: every Apéry number is odd
-- ============================================================================

/-- For `k ≥ 1`, the product `C(n,k)·C(n+k,k)` is even.  The trinomial-revision
identity `C(n,k)·C(n+k,k) = C(n+k,2k)·C(2k,k)` exposes the central binomial
factor `C(2k,k)`, which is even whenever `k ≥ 1`. -/
theorem two_dvd_choose_mul (n k : ℕ) (hk : 1 ≤ k) :
    2 ∣ n.choose k * (n + k).choose k := by
  -- `choose_mul` with `s = k ≤ 2k` gives the revision identity.
  have h := Nat.choose_mul (n := n + k) (k := 2 * k) (s := k) (by omega)
  have e1 : n + k - k = n := by omega
  have e2 : 2 * k - k = k := by omega
  rw [e1, e2] at h
  -- h : (n+k).choose (2*k) * (2*k).choose k = (n+k).choose k * n.choose k
  have hcentral : 2 ∣ (2 * k).choose k := by
    have h2 := Nat.two_dvd_centralBinom_of_one_le (n := k) hk
    rwa [Nat.centralBinom_eq_two_mul_choose] at h2
  have hdvd : 2 ∣ (n + k).choose k * n.choose k := h ▸ hcentral.mul_left _
  rw [Nat.mul_comm]
  exact hdvd

/-- Each summand of `bₙ` with `k ≥ 1` is even (it is the square of an even
number). -/
theorem two_dvd_aperyB_term (n k : ℕ) (hk : 1 ≤ k) :
    2 ∣ (n.choose k) ^ 2 * ((n + k).choose k) ^ 2 := by
  have h := two_dvd_choose_mul n k hk
  have hsq : (n.choose k) ^ 2 * ((n + k).choose k) ^ 2
      = (n.choose k * (n + k).choose k) * (n.choose k * (n + k).choose k) := by ring
  rw [hsq]
  exact h.mul_right _

/-- **Every Apéry number is odd.**  Modulo 2 only the `k = 0` term (which is `1`)
survives; every later term carries the even factor `C(n,k)·C(n+k,k)`. -/
theorem aperyB_odd (n : ℕ) : Odd (aperyB n) := by
  unfold aperyB
  rw [Finset.sum_range_succ']
  -- peel the `k = 0` term `(C(n,0))²·(C(n,0))² = 1`
  have h0 : (n.choose 0) ^ 2 * ((n + 0).choose 0) ^ 2 = 1 := by simp
  rw [h0]
  have heven : 2 ∣ ∑ k ∈ range n,
      (n.choose (k + 1)) ^ 2 * ((n + (k + 1)).choose (k + 1)) ^ 2 := by
    apply Finset.dvd_sum
    intro k _
    exact two_dvd_aperyB_term n (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
  obtain ⟨m, hm⟩ := heven
  rw [hm]
  exact ⟨m, by ring⟩

end AperyCentralBinom
