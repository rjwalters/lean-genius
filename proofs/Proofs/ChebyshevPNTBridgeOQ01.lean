import Mathlib

/-
# Factorization Bound: p^{v_p(C(2n,n))} ≤ 2n

## Research Problem: chebyshev-pnt-bridge-oq-01

Proves that for any prime p and any n ≥ 1:
  p^{v_p(C(2n,n))} ≤ 2n

This is a key ingredient in Chebyshev's proof of Bertrand's postulate
and the PNT bridge. The proof uses Kummer's theorem: the p-adic
valuation v_p(C(m,k)) counts the number of carries when adding k
and m-k in base p. Each carry contributes at most one power of p,
and there are at most log_p(m) digits.

Equivalently: v_p(C(2n,n)) ≤ log_p(2n), so p^{v_p(C(2n,n))} ≤ 2n.

Tags: number-theory, analytic-number-theory, Kummer, Chebyshev
-/

namespace ChebyshevPNTBridgeOQ01

open Nat Finset

-- ============================================================
-- Part I: p-adic Valuation of Central Binomial Coefficients
-- ============================================================

/-- The p-adic valuation of n! via Legendre's formula:
    v_p(n!) = ∑_{i≥1} ⌊n/p^i⌋. -/
theorem legendre_factorial_val (p n : ℕ) (hp : p.Prime) :
    (n !).factorization p = ∑ i ∈ Finset.Ico 1 (n + 1), n / p ^ i := by
  sorry

/-- The p-adic valuation of C(2n,n) via Legendre:
    v_p(C(2n,n)) = v_p((2n)!) - 2·v_p(n!)
                  = ∑_{i≥1} (⌊2n/p^i⌋ - 2⌊n/p^i⌋).

    Each term ⌊2n/p^i⌋ - 2⌊n/p^i⌋ is 0 or 1 (the "carry" indicator). -/
theorem central_binom_val_terms (p n : ℕ) (hp : p.Prime) (i : ℕ) (hi : i ≥ 1) :
    2 * n / p ^ i - 2 * (n / p ^ i) ≤ 1 := by
  have h : 2 * (n / p ^ i) ≤ 2 * n / p ^ i := by
    omega
  omega

/-- Carry count bound: the number of nonzero carry terms is at most
    the number of base-p digits of 2n, which is ⌊log_p(2n)⌋ + 1. -/
theorem carry_terms_bounded (p n : ℕ) (hp : p.Prime) (i : ℕ)
    (hi : p ^ i > 2 * n) : 2 * n / p ^ i = 0 := by
  exact Nat.div_eq_zero_iff (by positivity).2 (le_of_lt hi) |>.mpr (by omega) |> fun _ => by
    omega

/-- The number of digits of 2n in base p is at most log_p(2n) + 1. -/
theorem digits_bound (p n : ℕ) (hp : p.Prime) (hn : n ≥ 1) :
    ∃ k : ℕ, p ^ k > 2 * n ∧ k ≤ 2 * n := by
  exact ⟨2 * n, by
    calc p ^ (2 * n) ≥ 2 ^ (2 * n) := Nat.pow_le_pow_left hp.two_le (2 * n)
    _ > 2 * n := by
      have : 2 ^ (2 * n) ≥ 2 * n + 1 := by
        induction n with
        | zero => omega
        | succ n ih => calc 2 ^ (2 * (n + 1)) = 4 * 2 ^ (2 * n) := by ring_nf; ring
                         _ ≥ 4 * (2 * n + 1) := by omega
                         _ = 8 * n + 4 := by ring
                         _ ≥ 2 * (n + 1) + 1 := by omega
      omega,
    le_refl _⟩

-- ============================================================
-- Part II: The Main Bound
-- ============================================================

/-- **Main theorem**: p^{v_p(C(2n,n))} ≤ 2n for any prime p and n ≥ 1.

    Proof: Direct from Mathlib's `Nat.pow_factorization_choose_le` which gives
    p^{v_p(C(m,k))} ≤ m for k ≤ m. -/
theorem prime_pow_val_central_binom_le (p n : ℕ) (hp : p.Prime) (hn : n ≥ 1) :
    p ^ ((2 * n).choose n).factorization p ≤ 2 * n :=
  Nat.pow_factorization_choose_le (show n ≤ 2 * n by omega)

/-- Corollary: the product ∏_{p ≤ 2n} p^{v_p(C(2n,n))} = C(2n,n),
    so C(2n,n) ≤ (2n)^{π(2n)} where π is the prime counting function. -/
theorem central_binom_le_pow_prime_counting (n : ℕ) (hn : n ≥ 1) :
    (2 * n).choose n ≤ (2 * n) ^ (2 * n).primeCounting' := by
  sorry

-- ============================================================
-- Part III: Connection to Chebyshev/Bertrand
-- ============================================================

/-- The central binomial coefficient satisfies C(2n,n) ≥ 4^n/(2n+1).
    This is a well-known lower bound from the binomial theorem.
    Proof: 4^n = ∑ C(2n,i) ≤ (2n+1) * max C(2n,i) = (2n+1) * C(2n,n). -/
theorem central_binom_lower (n : ℕ) :
    (2 * n + 1) * (2 * n).choose n ≥ 4 ^ n := by
  -- 4^n = 2^(2n) = ∑_{i=0}^{2n} C(2n,i)
  have h_sum := Nat.sum_range_choose (2 * n)
  have h_pow : 2 ^ (2 * n) = 4 ^ n := by ring
  -- Each C(2n, i) ≤ C(2n, n) (middle binomial is largest)
  have h_mid : ∀ i, (2 * n).choose i ≤ (2 * n).choose n := by
    intro i
    have := Nat.choose_le_middle (2 * n) i
    rwa [show (2 * n) / 2 = n from by omega] at this
  -- Sum bound: ∑ C(2n, i) ≤ (2n+1) * C(2n, n)
  have h_bound : ∑ i in Finset.range (2 * n + 1), (2 * n).choose i ≤
      (2 * n + 1) * (2 * n).choose n := by
    have := Finset.sum_le_card_nsmul (Finset.range (2 * n + 1))
      (fun i => (2 * n).choose i) ((2 * n).choose n) (fun i _ => h_mid i)
    simp [Finset.card_range] at this
    exact this
  linarith [h_sum, h_pow]

/-- Combining: 4^n/(2n+1) ≤ C(2n,n) ≤ (2n)^{π(2n)},
    so π(2n) ≥ n·log(4)/log(2n) - log(2n+1)/log(2n).
    This is Chebyshev's lower bound on π. -/
theorem chebyshev_lower_via_kummer (n : ℕ) (hn : n ≥ 1) :
    4 ^ n ≤ (2 * n + 1) * (2 * n) ^ (2 * n).primeCounting' := by
  calc 4 ^ n
      ≤ (2 * n + 1) * (2 * n).choose n := central_binom_lower n
    _ ≤ (2 * n + 1) * (2 * n) ^ (2 * n).primeCounting' :=
        Nat.mul_le_mul_left _ (central_binom_le_pow_prime_counting n hn)

-- ============================================================
-- Part IV: Concrete Computations
-- ============================================================

/-- C(6,3) = 20, and 2^{v_2(20)} = 4, 3^{v_3(20)} = 1, 5^{v_5(20)} = 5.
    All satisfy p^{v_p} ≤ 6. -/
theorem example_n3 : (6).choose 3 = 20 := by native_decide

/-- C(10,5) = 252. -/
theorem example_n5 : (10).choose 5 = 252 := by native_decide

/-- C(20,10) = 184756. -/
theorem example_n10 : (20).choose 10 = 184756 := by native_decide

end ChebyshevPNTBridgeOQ01
