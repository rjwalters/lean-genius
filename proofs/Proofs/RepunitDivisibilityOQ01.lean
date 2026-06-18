import Mathlib

/-!
# Repunit divisibility: `R_m ∣ R_n ↔ m ∣ n`

For an integer base `b ≥ 2`, the **base-`b` repunit** of length `n` is

  `R_b(n) = 1 + b + b² + ⋯ + b^{n-1} = ∑_{i<n} b^i = (b^n − 1)/(b − 1)`,

i.e. the number written as `n` ones in base `b` (so `R₁₀(3) = 111`).

This file proves, fully machine-checked, the classical divisibility criterion

  **`R_b(m) ∣ R_b(n) ↔ m ∣ n`**   (`repunit_dvd_iff`),

with the base-ten special case `R₁₀(m) ∣ R₁₀(n) ↔ m ∣ n` (`repunit_ten_dvd_iff`).

## Method

The engine is the elementary fact `(b^m − 1) ∣ (b^n − 1) ↔ m ∣ n` for `b ≥ 2`
(`pow_sub_one_dvd_iff_dvd`), proved via the division algorithm and `Nat.ModEq`:
writing `n = m·q + r` with `r < m`, one has `b^n ≡ b^r (mod b^m − 1)`, so the
hypothesis forces `b^r ≡ 1`, i.e. `(b^m−1) ∣ (b^r−1)`; since `b^r − 1 < b^m − 1`
this divisor relation forces `r = 0`, hence `m ∣ n`. The converse is the
geometric factorisation `(b^m − 1) ∣ (b^m)^k − 1`.

The bridge from repunits to powers is the additive identity
`(b − 1)·R_b(n) + 1 = b^n` (`pred_mul_repunit_add_one`), which lets us cancel the
common factor `b − 1` (`Nat.mul_dvd_mul_iff_left`).

No axioms, no sorries.
-/

namespace RepunitDivisibilityOQ01

/-- The base-`b` repunit of length `n`: `∑_{i<n} b^i`. -/
def repunit (b n : ℕ) : ℕ := ∑ i ∈ Finset.range n, b ^ i

@[simp] theorem repunit_zero (b : ℕ) : repunit b 0 = 0 := by simp [repunit]

theorem repunit_succ (b n : ℕ) : repunit b (n + 1) = repunit b n + b ^ n := by
  simp only [repunit, Finset.sum_range_succ]

/-- Additive bridge to powers (stated without `ℕ`-subtraction):
`(b − 1)·R_b(n) + 1 = b^n`. -/
theorem pred_mul_repunit_add_one (b n : ℕ) (hb : 1 ≤ b) :
    (b - 1) * repunit b n + 1 = b ^ n := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction n with
  | zero => simp [repunit]
  | succ n ih =>
      rw [repunit_succ, pow_succ, Nat.mul_add]
      rw [(show c * repunit (c + 1) n + c * (c + 1) ^ n + 1
            = (c * repunit (c + 1) n + 1) + c * (c + 1) ^ n by ring), ih]
      ring

/-- Multiplicative bridge: `(b − 1)·R_b(n) = b^n − 1`. -/
theorem pred_mul_repunit (b n : ℕ) (hb : 1 ≤ b) :
    (b - 1) * repunit b n = b ^ n - 1 := by
  have h := pred_mul_repunit_add_one b n hb
  omega

/-- Core arithmetic fact: for `b ≥ 2`, `(b^m − 1) ∣ (b^n − 1) ↔ m ∣ n`. -/
theorem pow_sub_one_dvd_iff_dvd {b : ℕ} (hb : 2 ≤ b) (m n : ℕ) :
    (b ^ m - 1) ∣ (b ^ n - 1) ↔ m ∣ n := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [pow_zero] at h
      simp only [Nat.sub_self, Nat.zero_dvd] at h
      have hbn : b ^ n = 1 := by
        have : 1 ≤ b ^ n := Nat.one_le_pow _ _ (by omega)
        omega
      have hn0 : n = 0 := by
        by_contra hne
        have : b ≤ b ^ n := Nat.le_self_pow hne b
        omega
      simp [hn0]
    · obtain ⟨q, r, hr_lt, hqr⟩ : ∃ q r, r < m ∧ n = m * q + r :=
        ⟨n / m, n % m, Nat.mod_lt n hm, (Nat.div_add_mod n m).symm⟩
      have hmod1 : (1 : ℕ) ≡ b ^ m [MOD (b ^ m - 1)] :=
        (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mpr (dvd_refl _)
      have hbn_br : b ^ n ≡ b ^ r [MOD (b ^ m - 1)] := by
        calc b ^ n
            = (b ^ m) ^ q * b ^ r := by rw [hqr, pow_add, pow_mul]
          _ ≡ 1 ^ q * b ^ r [MOD (b ^ m - 1)] := (hmod1.symm.pow _).mul_right _
          _ = b ^ r := by rw [one_pow, one_mul]
      have hn1 : b ^ n ≡ 1 [MOD (b ^ m - 1)] :=
        ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mpr h).symm
      have hr1 : b ^ r ≡ 1 [MOD (b ^ m - 1)] := hbn_br.symm.trans hn1
      have hdvd_r : (b ^ m - 1) ∣ (b ^ r - 1) :=
        (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp hr1.symm
      have hbrm : b ^ r < b ^ m := by
        have hsplit : m = r + (m - r) := by omega
        rw [hsplit, pow_add]
        have h1 : 1 ≤ b ^ r := Nat.one_le_pow _ _ (by omega)
        have h2 : 2 ≤ b ^ (m - r) := by
          calc 2 ≤ b := hb
            _ = b ^ 1 := (pow_one b).symm
            _ ≤ b ^ (m - r) := Nat.pow_le_pow_right (by omega) (by omega)
        have hmul : b ^ r * 2 ≤ b ^ r * b ^ (m - r) := Nat.mul_le_mul (le_refl _) h2
        omega
      have h1r : 1 ≤ b ^ r := Nat.one_le_pow _ _ (by omega)
      have hrz : b ^ r - 1 = 0 := by
        by_contra hne
        have hpos : 0 < b ^ r - 1 := Nat.pos_of_ne_zero hne
        have hle := Nat.le_of_dvd hpos hdvd_r
        omega
      have hbr1 : b ^ r = 1 := by omega
      have hr0 : r = 0 := by
        by_contra hrne
        have : b ≤ b ^ r := Nat.le_self_pow hrne b
        omega
      exact ⟨q, by omega⟩
  · rintro ⟨k, rfl⟩
    simpa [pow_mul, one_pow] using Nat.sub_dvd_pow_sub_pow (b ^ m) 1 k

/-- **Repunit divisibility criterion** (base `b ≥ 2`):
`R_b(m) ∣ R_b(n) ↔ m ∣ n`. -/
theorem repunit_dvd_iff {b : ℕ} (hb : 2 ≤ b) (m n : ℕ) :
    repunit b m ∣ repunit b n ↔ m ∣ n := by
  rw [← pow_sub_one_dvd_iff_dvd hb m n]
  rw [← pred_mul_repunit b m (by omega), ← pred_mul_repunit b n (by omega)]
  exact (Nat.mul_dvd_mul_iff_left (show 0 < b - 1 by omega)).symm

/-- Base-ten repunits `R_n = 11…1` (`n` ones): `R_m ∣ R_n ↔ m ∣ n`. -/
theorem repunit_ten_dvd_iff (m n : ℕ) :
    repunit 10 m ∣ repunit 10 n ↔ m ∣ n :=
  repunit_dvd_iff (by norm_num) m n

end RepunitDivisibilityOQ01
