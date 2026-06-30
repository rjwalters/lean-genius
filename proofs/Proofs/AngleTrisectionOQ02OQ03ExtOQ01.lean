/-
# Angle Trisection OQ02-OQ03 Extension — OQ01
# The Role of the Prime 2 in the Gauss–Wantzel Arithmetic Bridge

The parent file `AngleTrisectionOQ02OQ03Ext` established the arithmetic bridge
behind Gauss–Wantzel: a regular `n`-gon is constructible iff `φ(n)` is a power
of two, together with the *coprime* multiplicativity
`TotientIsPow2 m → TotientIsPow2 n → Coprime m n → TotientIsPow2 (m*n)`.

That multiplicativity says nothing about the prime `2` itself, because `2` is
never coprime to an even number. This file fills exactly that gap: it isolates
the role of the prime `2`, which classically corresponds to **angle bisection**.

## Main result (the doubling invariance)

  `totient_pow2_double_iff : TotientIsPow2 (2 * n) ↔ TotientIsPow2 n`

Geometrically: **the regular `2n`-gon is constructible iff the regular
`n`-gon is.** The forward direction (`2n` constructible ⇒ `n` constructible) is
the non-obvious one — bisecting backwards is not a ruler-and-compass move, yet
the arithmetic forces it. The reverse is the familiar bisection step.

Iterating gives the **2-power invariance**

  `totient_pow2_two_pow_mul_iff : TotientIsPow2 (2^a * n) ↔ TotientIsPow2 n`,

so constructibility of a regular polygon depends only on the **odd part** of `n`.
Thus the 7-gon, 14-gon, 28-gon, … are all non-constructible (no amount of
bisection helps), while the 15-gon, 30-gon, 60-gon, … are all constructible.

## Engine

The two single-step totient identities for the prime `2`:
  * `2 ∣ n  → φ(2n) = 2·φ(n)`  (`Nat.totient_mul_of_prime_of_dvd`)
  * `2 ∤ n  → φ(2n) =   φ(n)`  (`Nat.totient_mul_of_prime_of_not_dvd`, since `2-1=1`)

Results: 0 sorries, 0 axioms — fully proved.
-/

import Mathlib

set_option linter.unusedVariables false

namespace AngleTrisectionOQ02OQ03ExtOQ01

/-- `φ(n)` is a power of two — the Gauss–Wantzel constructibility predicate
    (matching the parent file's `TotientIsPow2`). -/
def TotientIsPow2 (n : ℕ) : Prop := ∃ k : ℕ, Nat.totient n = 2 ^ k

-- ============================================================
-- SECTION I: The two single-step totient identities for p = 2
-- ============================================================

/-- If `n` is even then `φ(2n) = 2·φ(n)`. -/
theorem totient_two_mul_of_even {n : ℕ} (h : 2 ∣ n) :
    Nat.totient (2 * n) = 2 * Nat.totient n :=
  Nat.totient_mul_of_prime_of_dvd (by norm_num) h

/-- If `n` is odd then `φ(2n) = φ(n)`. -/
theorem totient_two_mul_of_odd {n : ℕ} (h : ¬ 2 ∣ n) :
    Nat.totient (2 * n) = Nat.totient n := by
  have := Nat.totient_mul_of_prime_of_not_dvd (p := 2) (n := n) (by norm_num) h
  simpa using this

-- ============================================================
-- SECTION II: The doubling invariance
-- ============================================================

/-- **Doubling invariance.** `φ(2n)` is a power of two iff `φ(n)` is.

    Geometrically: the regular `2n`-gon is constructible iff the regular
    `n`-gon is. The reverse direction is angle bisection; the forward direction
    is the non-trivial arithmetic converse. -/
theorem totient_pow2_double_iff (n : ℕ) :
    TotientIsPow2 (2 * n) ↔ TotientIsPow2 n := by
  by_cases hd : 2 ∣ n
  · -- even case: φ(2n) = 2·φ(n)
    have hphi : Nat.totient (2 * n) = 2 * Nat.totient n := totient_two_mul_of_even hd
    constructor
    · rintro ⟨k, hk⟩
      rw [hphi] at hk
      -- 2·φ(n) = 2^k forces k ≥ 1 and φ(n) = 2^(k-1)
      have hdvd2 : 2 ∣ 2 ^ k := ⟨Nat.totient n, hk.symm⟩
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · simp at hdvd2
        · exact h
      refine ⟨k - 1, ?_⟩
      have e : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
        conv_lhs => rw [show k = (k - 1) + 1 by omega]
        rw [pow_succ']
      have : 2 * Nat.totient n = 2 * 2 ^ (k - 1) := by rw [hk, e]
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
    · rintro ⟨k, hk⟩
      exact ⟨k + 1, by rw [hphi, pow_succ', hk]⟩
  · -- odd case: φ(2n) = φ(n), so the predicate is literally unchanged
    have hphi : Nat.totient (2 * n) = Nat.totient n := totient_two_mul_of_odd hd
    simp only [TotientIsPow2, hphi]

/-- Bisection (the easy direction): if the regular `n`-gon is constructible,
    so is the regular `2n`-gon. -/
theorem constructible_double {n : ℕ} (h : TotientIsPow2 n) : TotientIsPow2 (2 * n) :=
  (totient_pow2_double_iff n).mpr h

/-- Sharp converse: if the regular `2n`-gon is constructible, so is the
    regular `n`-gon. -/
theorem constructible_of_double {n : ℕ} (h : TotientIsPow2 (2 * n)) : TotientIsPow2 n :=
  (totient_pow2_double_iff n).mp h

-- ============================================================
-- SECTION III: 2-power invariance and reduction to the odd part
-- ============================================================

/-- **2-power invariance.** Multiplying by any power of `2` does not change
    constructibility: `φ(2^a · n)` is a power of two iff `φ(n)` is. -/
theorem totient_pow2_two_pow_mul_iff (a n : ℕ) :
    TotientIsPow2 (2 ^ a * n) ↔ TotientIsPow2 n := by
  induction a with
  | zero => simp only [pow_zero, one_mul]
  | succ a ih =>
    have hrw : 2 ^ (a + 1) * n = 2 * (2 ^ a * n) := by rw [pow_succ']; ring
    rw [hrw, totient_pow2_double_iff, ih]

/-- **Reduction to the odd part.** If `n = 2^a · m`, then the regular `n`-gon
    is constructible iff the regular `m`-gon is. In particular constructibility
    of a regular polygon depends only on the odd part of `n`. -/
theorem totient_pow2_iff_odd_part {n a m : ℕ} (h : n = 2 ^ a * m) :
    TotientIsPow2 n ↔ TotientIsPow2 m := by
  rw [h, totient_pow2_two_pow_mul_iff]

-- ============================================================
-- SECTION IV: Consequences — whole 2-power towers, at once
-- ============================================================

/-- The regular 15-gon is constructible (`φ(15) = 8 = 2^3`). -/
theorem totient_pow2_fifteen : TotientIsPow2 15 := ⟨3, by decide⟩

/-- Every regular `2^a · 15`-gon is constructible: 15, 30, 60, 120, 240, …
    The single arithmetic input is the 15-gon; bisection supplies the rest. -/
theorem constructible_two_pow_mul_fifteen (a : ℕ) : TotientIsPow2 (2 ^ a * 15) :=
  (totient_pow2_two_pow_mul_iff a 15).mpr totient_pow2_fifteen

/-- The regular 7-gon is **not** constructible (`φ(7) = 6 = 2·3`, odd prime 3). -/
theorem not_totient_pow2_seven : ¬ TotientIsPow2 7 := by
  rintro ⟨k, hk⟩
  have h6 : Nat.totient 7 = 6 := by decide
  rw [h6] at hk
  have h3 : (3 : ℕ) ∣ 2 ^ k := hk ▸ (by norm_num : (3 : ℕ) ∣ 6)
  have : (3 : ℕ) ∣ 2 := (by norm_num : Nat.Prime 3).dvd_of_dvd_pow h3
  norm_num at this

/-- No regular `2^a · 7`-gon is constructible: 7, 14, 28, 56, … remain out of
    reach no matter how many bisections are applied. This is the sharp content
    of the doubling invariance — bisection can never *create* constructibility. -/
theorem not_constructible_two_pow_mul_seven (a : ℕ) : ¬ TotientIsPow2 (2 ^ a * 7) := by
  rw [totient_pow2_two_pow_mul_iff]
  exact not_totient_pow2_seven

end AngleTrisectionOQ02OQ03ExtOQ01
