import Proofs.RepunitDivisibilityOQ01

/-!
# Repunits are a strong divisibility sequence: `gcd(R_m, R_n) = R_{gcd(m,n)}`

The base-`b` repunit `R_b(n) = ∑_{i<n} b^i` (see `RepunitDivisibilityOQ01`) satisfies
the **divisibility** criterion `R_b(m) ∣ R_b(n) ↔ m ∣ n`. This file proves the strictly
stronger **strong divisibility** identity

  **`gcd(R_b(m), R_b(n)) = R_b(gcd(m, n))`**   (`repunit_gcd`),

i.e. the repunit sequence is a *strong divisibility sequence* (an SDS). The divisibility
criterion is the special case where one index divides the other; the gcd identity holds for
*every* pair of indices.

## Method

The engine is the corresponding identity for `b^k − 1`:

  **`gcd(b^m − 1, b^n − 1) = b^{gcd(m,n)} − 1`**   (`gcd_pow_sub_one`),

proved by Euclidean descent along `Nat.gcd.induction`. Writing `n = m·q + r` with `r = n % m`,
the geometric factorisation `(b^m − 1) ∣ ((b^m)^q − 1)` gives
`b^n − 1 = (b^m − 1)·(c·b^r) + (b^r − 1)`, so
`gcd(b^m − 1, b^n − 1) = gcd(b^m − 1, b^r − 1)` (`Nat.gcd_mul_left_add_right`); this matches the
recursion `gcd m n = gcd (n % m) m` (`Nat.gcd_rec`), closing the induction.

The transfer to repunits cancels the common factor `b − 1` via the multiplicative bridge
`(b − 1)·R_b(n) = b^n − 1` (`pred_mul_repunit`) and `Nat.gcd_mul_left`.

As a corollary, `R_b(m)` and `R_b(n)` are coprime iff `m` and `n` are (`repunit_coprime_iff`),
since `R_b(d) = 1 ↔ d = 1` (`repunit_eq_one_iff`).

No axioms, no sorries.
-/

namespace RepunitDivisibilityOQ02

open RepunitDivisibilityOQ01

/-- **Strong divisibility for `b^k − 1`** (`b ≥ 1`):
`gcd(b^m − 1, b^n − 1) = b^{gcd(m,n)} − 1`.

Proved by Euclidean descent: the geometric factorisation reduces the gcd of
`b^m − 1` and `b^n − 1` to that of `b^m − 1` and `b^{n % m} − 1`, mirroring `Nat.gcd_rec`. -/
theorem gcd_pow_sub_one (b : ℕ) (hb : 1 ≤ b) (m n : ℕ) :
    Nat.gcd (b ^ m - 1) (b ^ n - 1) = b ^ Nat.gcd m n - 1 := by
  induction m, n using Nat.gcd.induction with
  | H0 n => simp
  | H1 m n hm ih =>
    -- `n = m * (n / m) + n % m`; reduce `b^n − 1` modulo `b^m − 1`.
    have hbr_pos : 1 ≤ b ^ (n % m) := Nat.one_le_pow _ _ hb
    have hdvd : (b ^ m - 1) ∣ ((b ^ m) ^ (n / m) - 1) := by
      simpa using Nat.sub_dvd_pow_sub_pow (b ^ m) 1 (n / m)
    obtain ⟨c, hc⟩ := hdvd
    have hAq_pos : 1 ≤ (b ^ m) ^ (n / m) := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hb)
    have hA : (b ^ m) ^ (n / m) = (b ^ m - 1) * c + 1 := by omega
    have hexp : b ^ n = (b ^ m) ^ (n / m) * b ^ (n % m) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have hbn : b ^ n = (b ^ m - 1) * (c * b ^ (n % m)) + b ^ (n % m) := by
      rw [hexp, hA]; ring
    have hbn1 : b ^ n - 1 = (b ^ m - 1) * (c * b ^ (n % m)) + (b ^ (n % m) - 1) := by
      omega
    rw [Nat.gcd_rec m n, ← ih, Nat.gcd_comm (b ^ (n % m) - 1) (b ^ m - 1),
      hbn1, Nat.gcd_mul_left_add_right]

/-- **Repunits are a strong divisibility sequence** (base `b ≥ 2`):
`gcd(R_b(m), R_b(n)) = R_b(gcd(m, n))`.

This strengthens `repunit_dvd_iff`: the divisibility criterion `R_m ∣ R_n ↔ m ∣ n` is the
special case `gcd(m, n) ∈ {m, n}`. -/
theorem repunit_gcd {b : ℕ} (hb : 2 ≤ b) (m n : ℕ) :
    Nat.gcd (repunit b m) (repunit b n) = repunit b (Nat.gcd m n) := by
  have hb1 : 1 ≤ b := by omega
  have lhs : (b - 1) * Nat.gcd (repunit b m) (repunit b n)
      = Nat.gcd ((b - 1) * repunit b m) ((b - 1) * repunit b n) :=
    (Nat.gcd_mul_left (b - 1) (repunit b m) (repunit b n)).symm
  rw [pred_mul_repunit b m hb1, pred_mul_repunit b n hb1, gcd_pow_sub_one b hb1 m n,
    ← pred_mul_repunit b (Nat.gcd m n) hb1] at lhs
  exact Nat.eq_of_mul_eq_mul_left (show 0 < b - 1 by omega) lhs

/-- Base-ten repunits `R_n = 11…1`: `gcd(R_m, R_n) = R_{gcd(m,n)}`. -/
theorem repunit_ten_gcd (m n : ℕ) :
    Nat.gcd (repunit 10 m) (repunit 10 n) = repunit 10 (Nat.gcd m n) :=
  repunit_gcd (by norm_num) m n

/-- A repunit equals `1` exactly at length `1` (base `b ≥ 2`): `R_b(d) = 1 ↔ d = 1`.
(`R_b(0) = 0`, `R_b(1) = 1`, and `R_b(d) ≥ 2` for `d ≥ 2`.) -/
theorem repunit_eq_one_iff {b : ℕ} (hb : 2 ≤ b) (d : ℕ) :
    repunit b d = 1 ↔ d = 1 := by
  constructor
  · intro h
    match d with
    | 0 => simp [repunit] at h
    | 1 => rfl
    | (k + 2) =>
      exfalso
      have hb1 : 2 ≤ b ^ (k + 1) := by
        calc 2 ≤ b := hb
          _ = b ^ 1 := (pow_one b).symm
          _ ≤ b ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      rw [repunit_succ] at h
      omega
  · rintro rfl
    simp [repunit]

/-- **Coprimality criterion** (base `b ≥ 2`): `R_b(m)` and `R_b(n)` are coprime iff
`m` and `n` are coprime. A direct consequence of the strong divisibility identity. -/
theorem repunit_coprime_iff {b : ℕ} (hb : 2 ≤ b) (m n : ℕ) :
    Nat.Coprime (repunit b m) (repunit b n) ↔ Nat.Coprime m n := by
  simp only [Nat.Coprime, repunit_gcd hb, repunit_eq_one_iff hb]

end RepunitDivisibilityOQ02
