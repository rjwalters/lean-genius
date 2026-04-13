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

    Proof sketch: v_p(C(2n,n)) ≤ log_p(2n) (each carry ≤ 1, at most
    log_p(2n) nonzero terms), so p^{v_p(C(2n,n))} ≤ p^{log_p(2n)} ≤ 2n. -/
theorem prime_pow_val_central_binom_le (p n : ℕ) (hp : p.Prime) (hn : n ≥ 1) :
    p ^ ((2 * n).choose n).factorization p ≤ 2 * n :=
  Nat.pow_factorization_choose_le (by omega)

/-- Corollary: the product ∏_{p ≤ 2n} p^{v_p(C(2n,n))} = C(2n,n),
    so C(2n,n) ≤ (2n)^{π(2n)} where π is the prime counting function.
    Note: uses Nat.primeCounting (primes ≤ 2n), not primeCounting' (primes < 2n),
    because for n=1 the prime 2 divides C(2,1)=2 and must be counted. -/
theorem central_binom_le_pow_prime_counting (n : ℕ) (hn : n ≥ 1) :
    (2 * n).choose n ≤ (2 * n) ^ Nat.primeCounting (2 * n) := by
  sorry

-- ============================================================
-- Part III: Connection to Chebyshev/Bertrand
-- ============================================================

/-- The central binomial coefficient satisfies C(2n,n) ≥ 4^n/(2n+1).
    This is a well-known lower bound from the binomial theorem.
    Proof: 4^n = ∑_{k=0}^{2n} C(2n,k) ≤ (2n+1) · C(2n,n) since C(2n,n) is max term. -/
theorem central_binom_lower (n : ℕ) :
    (2 * n + 1) * (2 * n).choose n ≥ 4 ^ n := by
  -- 4^n = 2^(2n) = Σ_{k < 2n+1} C(2n, k)
  have h4eq : 4 ^ n = ∑ m ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) m := by
    rw [Nat.sum_range_choose, show (4 : ℕ) ^ n = (2 ^ 2) ^ n from by norm_num, ← pow_mul]
  rw [h4eq, ge_iff_le]
  -- Each C(2n, k) ≤ C(2n, n) (central term is maximum)
  calc ∑ m ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) m
      ≤ ∑ _m ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) n := by
        apply Finset.sum_le_sum
        intro k _
        calc Nat.choose (2 * n) k
            ≤ Nat.choose (2 * n) ((2 * n) / 2) := Nat.choose_le_middle k (2 * n)
          _ = Nat.choose (2 * n) n := by rw [Nat.mul_div_cancel_left n (by omega)]
    _ = (2 * n + 1) * Nat.choose (2 * n) n := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- Combining: 4^n/(2n+1) ≤ C(2n,n) ≤ (2n)^{π(2n)},
    so π(2n) ≥ n·log(4)/log(2n) - log(2n+1)/log(2n).
    This is Chebyshev's lower bound on π. -/
theorem chebyshev_lower_via_kummer (n : ℕ) (hn : n ≥ 1) :
    4 ^ n ≤ (2 * n + 1) * (2 * n) ^ Nat.primeCounting (2 * n) := by
  calc 4 ^ n
      ≤ (2 * n + 1) * (2 * n).choose n := central_binom_lower n
    _ ≤ (2 * n + 1) * (2 * n) ^ Nat.primeCounting (2 * n) :=
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
