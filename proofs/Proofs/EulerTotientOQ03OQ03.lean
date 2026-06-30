import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-
# Exact Consequences of the GCD–Totient Identity

## Parent Open Question (euler-totient-oq-03)

> Can the super-multiplicativity inequality φ(a)·φ(b) ≤ φ(ab) be *sharpened*
> to an exact equality
>
>     φ(a)·φ(b)·gcd(a,b) / φ(gcd(a,b)) = φ(ab)
>
> via the GCD–totient identity?

The parent entry states the identity itself,

    φ(gcd(a,b)) · φ(ab) = φ(a) · φ(b) · gcd(a,b)          (★)

(`Nat.totient_gcd_mul_totient_mul` in Mathlib). This leaf answers the open
question by *using* (★) to extract its quantitative consequences.

## What This Proves (new content beyond the identity)

1. **Exact division form** (`totient_mul_eq_div`): the literal sharpening the
   question asks for — solving (★) for φ(ab) as an exact ℕ-division.
2. **Coprime collapse** (`totient_mul_coprime`): gcd = 1 recovers ordinary
   multiplicativity φ(ab) = φ(a)·φ(b).
3. **Divisibility collapse** (`totient_mul_of_dvd`): a ∣ b gives the exact
   value φ(ab) = a·φ(b).
4. **General power formula** (`totient_pow_succ`, `totient_pow`, `totient_sq`):
   for *every* base n (not just primes),

       φ(nᵏ⁺¹) = nᵏ · φ(n).

   Mathlib only provides this for prime bases (`Nat.totient_prime_pow`); the
   general statement is derived here by induction from (★).

## Key Insight

The single identity (★) is the exact form of super-multiplicativity: the gap
between φ(a)·φ(b) and φ(ab) is governed precisely by the factor
gcd(a,b) / φ(gcd(a,b)) ≥ 1. Specializing the two arguments collapses (★) to
the multiplicative, divisibility, and prime-power laws — and an induction on
the exponent upgrades the divisibility case to the full power formula for an
arbitrary base.
-/

open Nat

namespace EulerTotientOQ03OQ03

/-- The GCD–totient identity (Mathlib / parent entry), restated as the
foundation for this file:
`φ(gcd(a,b)) · φ(ab) = φ(a) · φ(b) · gcd(a,b)`. -/
theorem totient_gcd_identity (a b : ℕ) :
    φ (Nat.gcd a b) * φ (a * b) = φ a * φ b * Nat.gcd a b :=
  Nat.totient_gcd_mul_totient_mul a b

/-- **Exact sharpening of super-multiplicativity** — the literal form requested
by the open question. Whenever `gcd(a,b) > 0` (i.e. `a, b` not both zero),
`φ(ab)` is recovered as an exact natural-number division:
`φ(a)·φ(b)·gcd(a,b) / φ(gcd(a,b)) = φ(ab)`. -/
theorem totient_mul_eq_div (a b : ℕ) (h : 0 < Nat.gcd a b) :
    φ a * φ b * Nat.gcd a b / φ (Nat.gcd a b) = φ (a * b) := by
  have hφ : 0 < φ (Nat.gcd a b) := Nat.totient_pos.mpr h
  exact Nat.div_eq_of_eq_mul_left hφ (by rw [← totient_gcd_identity]; ring)

/-- **Coprime collapse.** When `gcd(a,b) = 1`, the identity reduces to ordinary
multiplicativity `φ(ab) = φ(a)·φ(b)`. -/
theorem totient_mul_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    φ (a * b) = φ a * φ b := by
  have key := totient_gcd_identity a b
  rw [Nat.Coprime] at h
  rw [h] at key
  simpa using key

/-- **Divisibility collapse.** When `a ∣ b` (and `a > 0`), `gcd(a,b) = a` and the
identity gives the exact value `φ(ab) = a·φ(b)`. -/
theorem totient_mul_of_dvd {a b : ℕ} (ha : 0 < a) (h : a ∣ b) :
    φ (a * b) = a * φ b := by
  have key := totient_gcd_identity a b
  rw [Nat.gcd_eq_left h] at key
  have hφ : 0 < φ a := Nat.totient_pos.mpr ha
  apply Nat.eq_of_mul_eq_mul_left hφ
  rw [key]; ring

/-- **General power formula.** For *every* base `n`,
`φ(nᵏ⁺¹) = nᵏ · φ(n)`. Proved by induction on `k`, using the divisibility case
of the GCD–totient identity at each step. Mathlib only supplies this for prime
bases (`Nat.totient_prime_pow`). -/
theorem totient_pow_succ (n k : ℕ) : φ (n ^ (k + 1)) = n ^ k * φ n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hgcd : Nat.gcd (n ^ (k + 1)) n = n :=
        Nat.gcd_eq_right (dvd_pow_self n (Nat.succ_ne_zero k))
      have key := Nat.totient_gcd_mul_totient_mul (n ^ (k + 1)) n
      rw [hgcd, ← pow_succ, ih] at key
      have hφ : 0 < φ n := Nat.totient_pos.mpr hn
      apply Nat.eq_of_mul_eq_mul_left hφ
      rw [key]; ring

/-- The general power formula in `k - 1` form: for `k ≥ 1` and any base `n`,
`φ(nᵏ) = nᵏ⁻¹ · φ(n)`. -/
theorem totient_pow {n k : ℕ} (hk : 1 ≤ k) : φ (n ^ k) = n ^ (k - 1) * φ n := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simpa using totient_pow_succ n j

/-- **Square case** of the power formula: `φ(n²) = n · φ(n)` for every `n`. -/
theorem totient_sq (n : ℕ) : φ (n ^ 2) = n * φ n := by
  simpa using totient_pow_succ n 1

-- ============================================================================
-- Sanity checks (no computation: these are direct specializations)
-- ============================================================================

/-- φ(3²) = 3·φ(3): instance of the general power formula at a non-prime exponent
of a prime base. -/
example : φ (3 ^ 2) = 3 * φ 3 := totient_sq 3

/-- φ(6²) = 6·φ(6): the power formula at a composite base (where Mathlib's
prime-power lemma does not apply). -/
example : φ (6 ^ 2) = 6 * φ 6 := totient_sq 6

/-- Coprime collapse recovers φ(15) = φ(3)·φ(5). -/
example : φ (3 * 5) = φ 3 * φ 5 := totient_mul_coprime (by decide)

/-- Divisibility collapse: φ(2 · 6) = 2 · φ(6) since 2 ∣ 6. -/
example : φ (2 * 6) = 2 * φ 6 := totient_mul_of_dvd (by norm_num) (by norm_num)

end EulerTotientOQ03OQ03
