/-
  Irrationality of ∛2 (cube root of 2)

  Extension of the √2 irrationality proof to cube roots.
  Unlike √2 where a parity argument suffices, ∛2 requires the
  Rational Root Theorem or unique prime factorization.

  Proof strategy: If ∛2 = p/q in lowest terms, then p³ = 2q³.
  Since 2 | p³ and 2 is prime, 2 | p. Write p = 2k, then 8k³ = 2q³,
  so 4k³ = q³, hence 2 | q³, so 2 | q. Contradicts gcd(p,q) = 1.
-/
import Mathlib

namespace Sqrt2IrrationalOQ01

/-- ∛2 is irrational.
    Proof: Use Mathlib's Nat.Prime.irrational_nrt which shows that
    the n-th root of a natural number is irrational unless it's
    a perfect n-th power. Since 2 is not a perfect cube, ∛2 is irrational. -/
theorem cbrt_two_irrational : Irrational (2 : ℝ) ^ (1/3 : ℝ) := by
  sorry

/-- Alternative: use Int.Prime.not_dvd_of_coprime approach.
    If p/q = ∛2 with gcd(p,q) = 1, then p³ = 2q³.
    Since 2 is prime: 2 | p³ → 2 | p → p = 2k → 8k³ = 2q³ → 4k³ = q³ → 2 | q.
    This contradicts gcd(p,q) = 1. -/
theorem cbrt_two_irrational_elementary :
    ¬∃ (p q : ℤ), q ≠ 0 ∧ Int.gcd p q = 1 ∧ p ^ 3 = 2 * q ^ 3 := by
  intro ⟨p, q, hq, hcoprime, heq⟩
  -- 2 | p³ (from p³ = 2q³)
  have h2_dvd_p3 : (2 : ℤ) ∣ p ^ 3 := ⟨q ^ 3, by linarith⟩
  -- 2 is prime, so 2 | p
  have h2_prime : Prime (2 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by decide)
  have h2_dvd_p : (2 : ℤ) ∣ p := by
    have := h2_prime.dvd_of_dvd_pow h2_dvd_p3
    exact this
  -- Write p = 2k
  obtain ⟨k, hk⟩ := h2_dvd_p
  -- Substitute: (2k)³ = 2q³, i.e., 8k³ = 2q³, i.e., 4k³ = q³
  have heq2 : 4 * k ^ 3 = q ^ 3 := by nlinarith
  -- 2 | q³ (since 4k³ = q³ implies 2 | q³)
  have h2_dvd_q3 : (2 : ℤ) ∣ q ^ 3 := ⟨2 * k ^ 3, by linarith⟩
  -- 2 | q
  have h2_dvd_q : (2 : ℤ) ∣ q := h2_prime.dvd_of_dvd_pow h2_dvd_q3
  -- But gcd(p,q) = 1 and 2 | p, 2 | q → 2 | gcd(p,q) = 1, contradiction
  have : (2 : ℤ).natAbs ∣ Int.gcd p q := Int.natAbs_dvd_natAbs.mpr
    (Int.dvd_gcd h2_dvd_p h2_dvd_q)
  rw [hcoprime] at this
  simp at this

/-- Generalization: ∛n is irrational for non-perfect-cube n. -/
theorem cbrt_irrational_of_not_cube (n : ℕ) (hn : ¬∃ m : ℕ, m ^ 3 = n) :
    ¬∃ (p q : ℤ), q ≠ 0 ∧ Int.gcd p q = 1 ∧ p ^ 3 = ↑n * q ^ 3 := by
  sorry

end Sqrt2IrrationalOQ01
