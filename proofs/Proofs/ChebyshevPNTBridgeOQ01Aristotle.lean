/-
  Aristotle targets for ChebyshevPNTBridgeOQ01 (Factorization Bound for C(2n,n))
  Routine supporting lemmas for automated proof search.
  See ChebyshevPNTBridgeOQ01.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely in Mathlib (central binomial bounds, Legendre formula)
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)

  Targets:
  1. central_binom_lower_ari: C(2n,n) * (2n+1) ≥ 4^n
     Proof: Sum of all C(2n,k) = 4^n (by Nat.sum_range_choose), and C(2n,n) is
     the maximum term (by symmetry: C(2n,k) = C(2n,2n-k), and the central term
     is largest). So 4^n = ∑_k C(2n,k) ≤ (2n+1) * C(2n,n).

  2. legendre_val_ari: v_p(n!) = ∑_{i≥1} ⌊n/p^i⌋
     Mathlib has Nat.factorization_factorial or Nat.Prime.factorization_factorial_eq.
-/
import Mathlib

open Nat Finset BigOperators

namespace ChebyshevPNTBridgeOQ01.Aristotle

/-- **Central binomial lower bound** (Aristotle target):
    (2n+1) * C(2n,n) ≥ 4^n.

    Proof: ∑_{k=0}^{2n} C(2n,k) = 2^(2n) = 4^n by Nat.sum_range_choose.
    The central term C(2n,n) is the maximum, so:
    4^n = ∑_{k} C(2n,k) ≤ (2n+1) * C(2n,n). -/
theorem central_binom_lower_ari (n : ℕ) :
    (2 * n + 1) * Nat.choose (2 * n) n ≥ 4 ^ n := by
  -- 4^n = 2^(2n) = Σ_{k < 2n+1} C(2n, k)
  have h4eq : 4 ^ n = ∑ m ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) m := by
    rw [Nat.sum_range_choose, show (4 : ℕ) ^ n = (2 ^ 2) ^ n from by norm_num, ← pow_mul]
  rw [h4eq, ge_iff_le]
  calc ∑ m ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) m
      ≤ ∑ _m ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) n := by
        apply Finset.sum_le_sum
        intro k _
        calc Nat.choose (2 * n) k
            ≤ Nat.choose (2 * n) ((2 * n) / 2) := Nat.choose_le_middle k (2 * n)
          _ = Nat.choose (2 * n) n := by rw [Nat.mul_div_cancel_left n (by omega)]
    _ = (2 * n + 1) * Nat.choose (2 * n) n := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- The p-adic valuation of C(2n,n) satisfies:
    v_p(C(2n,n)) = v_p((2n)!) - 2 * v_p(n!)
    and equals ∑_{i≥1} (⌊2n/p^i⌋ - 2⌊n/p^i⌋). -/
theorem central_binom_factorization_eq (p n : ℕ) (hp : Nat.Prime p) :
    ((2 * n).choose n).factorization p =
    ((2 * n).factorization p) - 2 * (n.factorization p) := by
  sorry

end ChebyshevPNTBridgeOQ01.Aristotle
