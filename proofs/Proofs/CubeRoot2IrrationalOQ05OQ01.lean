/-
# Cube Root of 2 OQ-05-OQ-01: the full rationality criterion for n-th roots

## Open Question (parent OQ-05, first listed)
State and prove the full criterion: for `m, n ≥ 1`, the real n-th root `m ^ (1/n)` is
**rational iff m is a perfect n-th power** (`∃ k : ℕ, k ^ n = m`).

The parent OQ-05 proves only one direction for prime bases — a prime is never a perfect
power, so its n-th root is irrational. This entry proves the complete two-way
characterization for an arbitrary natural number `m`, and recovers the prime case as a
corollary.

## Approach
Write `x = (m : ℝ) ^ (n : ℝ)⁻¹`. Note `x ≥ 0` and `x ^ n = m` (rpow composition,
`m ≥ 0`).
* (⇐) If `m = k ^ n` then `x = ((k : ℝ) ^ n) ^ n⁻¹ = (k : ℝ) ^ (n · n⁻¹) = k`, rational.
* (⇒) If `x` is rational then `x ^ n = m` (an integer) with `0 < n`, so Mathlib's
  `irrational_nrt_of_notint_nrt` (contrapositive) forces `x = (y : ℤ)`. Since `x ≥ 0`,
  `y ≥ 0`, hence `y = (k : ℕ)` and `k ^ n = m`.

The prime corollary then needs only the elementary fact that a prime is not a perfect
`n`-th power for `n ≥ 2`.

Sorry-free and axiom-free.
-/
import Mathlib

namespace CubeRoot2IrrationalOQ05OQ01

open Real

/-- `m` is a perfect `n`-th power: there is a natural number `k` with `k ^ n = m`. -/
def IsPerfectNthPow (m n : ℕ) : Prop := ∃ k : ℕ, k ^ n = m

/-- The defining identity of the real `n`-th root: for `n ≥ 1`,
`(m ^ (1/n)) ^ n = m`. -/
theorem rpow_inv_pow {m n : ℕ} (hn : 0 < n) :
    ((m : ℝ) ^ ((n : ℝ)⁻¹)) ^ n = (m : ℝ) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [← Real.rpow_natCast ((m : ℝ) ^ ((n : ℝ)⁻¹)) n, ← Real.rpow_mul hm0,
    inv_mul_cancel₀ hn0, Real.rpow_one]

/-- **The rationality criterion.** For `m, n ≥ 1`, the real `n`-th root `m ^ (1/n)` is
rational (i.e. *not* irrational) **iff** `m` is a perfect `n`-th power. -/
theorem rational_rpow_inv_iff {m n : ℕ} (hn : 0 < n) :
    (¬ Irrational ((m : ℝ) ^ ((n : ℝ)⁻¹))) ↔ IsPerfectNthPow m n := by
  constructor
  · -- rational ⟹ perfect power
    intro hrat
    have hxr : ((m : ℝ) ^ ((n : ℝ)⁻¹)) ^ n = ((m : ℤ) : ℝ) := by
      rw [rpow_inv_pow hn]; push_cast; ring
    -- the integral-closedness lemma: a rational `n`-th root of an integer is an integer
    have hint : ∃ y : ℤ, (m : ℝ) ^ ((n : ℝ)⁻¹) = (y : ℝ) := by
      by_contra h
      exact hrat (irrational_nrt_of_notint_nrt n (m : ℤ) hxr h hn)
    obtain ⟨y, hy⟩ := hint
    have hx0 : (0 : ℝ) ≤ (m : ℝ) ^ ((n : ℝ)⁻¹) := by positivity
    rw [hy] at hx0
    have hy0 : 0 ≤ y := by exact_mod_cast hx0
    lift y to ℕ using hy0 with k
    refine ⟨k, ?_⟩
    have h2 : ((m : ℝ) ^ ((n : ℝ)⁻¹)) ^ n = (m : ℝ) := rpow_inv_pow hn
    rw [hy] at h2
    exact_mod_cast h2
  · -- perfect power ⟹ rational
    rintro ⟨k, rfl⟩
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hval : ((↑(k ^ n) : ℝ)) ^ ((n : ℝ)⁻¹) = (k : ℝ) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast (k : ℝ) n, ← Real.rpow_mul hk0,
        mul_inv_cancel₀ hn0, Real.rpow_one]
    rw [hval]
    exact Nat.not_irrational k

/-- **The irrationality criterion** (negated form). For `m, n ≥ 1`, the real `n`-th root
`m ^ (1/n)` is irrational **iff** `m` is not a perfect `n`-th power. -/
theorem irrational_rpow_inv_iff {m n : ℕ} (hn : 0 < n) :
    Irrational ((m : ℝ) ^ ((n : ℝ)⁻¹)) ↔ ¬ IsPerfectNthPow m n := by
  rw [← not_iff_not, not_not]
  exact rational_rpow_inv_iff hn

/-- A prime is never a perfect `n`-th power for `n ≥ 2`. -/
theorem not_isPerfectNthPow_prime {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n) :
    ¬ IsPerfectNthPow p n := by
  rintro ⟨k, hk⟩
  have hdvd : k ∣ p := by
    rw [← hk]; exact dvd_pow_self k (by omega)
  rcases (hp.eq_one_or_self_of_dvd k hdvd) with h1 | hpk
  · subst h1; rw [one_pow] at hk; exact hp.ne_one hk.symm
  · subst hpk
    have h1 : k ^ n = k ^ 1 := by rw [pow_one]; exact hk
    have hk2 : 2 ≤ k := hp.two_le
    have := Nat.pow_right_injective hk2 h1
    omega

/-- **The n-th root of a prime is irrational** — the parent OQ-05 result recovered as a
corollary of the general criterion. -/
theorem irrational_rpow_inv_prime {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n) :
    Irrational ((p : ℝ) ^ ((n : ℝ)⁻¹)) :=
  (irrational_rpow_inv_iff (by omega)).mpr (not_isPerfectNthPow_prime hp hn)

/-- **∛2 is irrational** — the base entry, recovered from the prime corollary. -/
theorem irrational_cbrt_two : Irrational ((2 : ℝ) ^ ((3 : ℝ)⁻¹)) := by
  have := irrational_rpow_inv_prime (p := 2) (n := 3) (by norm_num) (by norm_num)
  simpa using this

/-- **∛8 is rational** (= 2): `8 = 2³` is a perfect cube, so the criterion's rational
branch fires. Demonstrates the converse direction on a genuine perfect power. -/
theorem rational_cbrt_eight : ¬ Irrational ((8 : ℝ) ^ ((3 : ℝ)⁻¹)) := by
  have := (rational_rpow_inv_iff (m := 8) (n := 3) (by norm_num)).mpr ⟨2, by norm_num⟩
  simpa using this

/-- **∛6 is irrational**, although `6` is *not prime*: the criterion handles composite
non-perfect-powers that the prime corollary cannot reach. -/
theorem irrational_cbrt_six : Irrational ((6 : ℝ) ^ ((3 : ℝ)⁻¹)) := by
  have key : Irrational ((6 : ℝ) ^ ((3 : ℝ)⁻¹)) := by
    refine (irrational_rpow_inv_iff (m := 6) (n := 3) (by norm_num)).mpr ?_
    rintro ⟨k, hk⟩
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k <;> omega
    · have : 2 ^ 3 ≤ k ^ 3 := Nat.pow_le_pow_left h 3
      omega
  simpa using key

end CubeRoot2IrrationalOQ05OQ01
