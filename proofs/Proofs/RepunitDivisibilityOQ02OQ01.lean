/-
# Strong divisibility for the sequence `bⁿ + 1`

The classical strong-divisibility law for repunits / Mersenne-type sequences states
`gcd(bᵐ − 1, bⁿ − 1) = b^{gcd(m,n)} − 1` (`gcd_pow_sub_one` in the parent entry).
The companion sequence `bⁿ + 1` is **not** a strong divisibility sequence: its gcd
structure is governed by the **2-adic valuations** of the exponents.

Write `d = gcd(m, n)` and let `a = m/d`, `c = n/d` (so `gcd(a, c) = 1`).

* **Both cofactors odd** (equivalently `v₂(m) = v₂(n)`): `bᵈ + 1` is a greatest common
  divisor of `bᵐ + 1` and `bⁿ + 1` — it divides both, and every common divisor divides
  it (`isGCD_pow_add_one`). Over `ℤ`, `gcd(bᵐ + 1, bⁿ + 1) = b^{gcd(m,n)} + 1`
  (`int_gcd_pow_add_one`).
* **Some cofactor even**: every common divisor divides `2`
  (`dvd_two_of_even_quotient`), so the gcd is `1` or `2`.

The development lives over `ℤ`, where the alternating cofactor of `xᵏ + 1` for odd `k`
is handled cleanly by the sign identity `(-1)ᵏ = -1`.

## Engine

The reverse ("every common divisor divides `bᵈ + 1`") direction rests on three facts:
1. `bᵐ + 1 ∣ b^{2m} − 1`, so any common divisor `e` divides `b^{2m} − 1` and `b^{2n} − 1`;
2. the universal divisor property of the `bⁿ − 1` sequence forces `e ∣ b^{2d} − 1`
   (`dvd_pow_gcd_sub_one`, an Euclidean descent);
3. since `m/d` is odd, `b^{2d} − 1 ∣ bᵐ − bᵈ`, so the linear combination
   `(bᵐ + 1) − (bᵐ − bᵈ) = bᵈ + 1` is divisible by `e`.
-/
import Mathlib

namespace RepunitPlusOne

variable {b : ℤ}

/-- For odd `k`, `x + 1` divides `xᵏ + 1`. This is the sign form of
`(x − y) ∣ xᵏ − yᵏ` with `y = -1`. -/
theorem add_one_dvd_pow_add_one (x : ℤ) {k : ℕ} (hk : Odd k) :
    (x + 1) ∣ (x ^ k + 1) := by
  have h := sub_dvd_pow_sub_pow x (-1) k
  rw [hk.neg_one_pow] at h
  simpa [sub_neg_eq_add] using h

/-- If `j ∣ k` then `bʲ − 1 ∣ bᵏ − 1`. -/
theorem pow_sub_one_dvd_pow_sub_one {j k : ℕ} (h : j ∣ k) :
    (b ^ j - 1) ∣ (b ^ k - 1) := by
  obtain ⟨t, rfl⟩ := h
  rw [pow_mul]
  simpa using sub_dvd_pow_sub_pow (b ^ j) 1 t

/-- **Universal divisor property of the `bⁿ − 1` sequence.**
Any common divisor of `bᵃ − 1` and `bᶜ − 1` divides `b^{gcd a c} − 1`.
Proved by Euclidean descent on `(a, c)`. -/
theorem dvd_pow_gcd_sub_one {e : ℤ} :
    ∀ a c : ℕ, e ∣ b ^ a - 1 → e ∣ b ^ c - 1 → e ∣ b ^ Nat.gcd a c - 1 := by
  intro a c
  induction a, c using Nat.gcd.induction with
  | H0 c => intro _ hc; simpa using hc
  | H1 a c ha ih =>
    intro ha1 hc1
    rw [Nat.gcd_rec]
    apply ih
    · -- `e ∣ b ^ (c % a) - 1`
      have hd1 : (b ^ a - 1) ∣ ((b ^ a) ^ (c / a) - 1) := by
        simpa using sub_dvd_pow_sub_pow (b ^ a) 1 (c / a)
      have he2 : e ∣ ((b ^ a) ^ (c / a) - 1) := ha1.trans hd1
      have hkey : b ^ c - b ^ (c % a) = b ^ (c % a) * ((b ^ a) ^ (c / a) - 1) := by
        rw [mul_sub, mul_one, ← pow_mul, ← pow_add, Nat.mod_add_div]
      have hdiff : e ∣ b ^ c - b ^ (c % a) := by
        rw [hkey]; exact he2.mul_left _
      have hsub : e ∣ (b ^ c - 1) - (b ^ c - b ^ (c % a)) := dvd_sub hc1 hdiff
      have heq : (b ^ c - 1) - (b ^ c - b ^ (c % a)) = b ^ (c % a) - 1 := by ring
      rwa [heq] at hsub
    · exact ha1

/-- `bᵈ + 1` divides `bᵐ + 1` whenever `0 < d`, `d ∣ m`, and the cofactor `m / d`
is odd. -/
theorem pow_add_one_dvd_of_odd_quotient {d m : ℕ} (hd : 0 < d) (hdm : d ∣ m)
    (hodd : Odd (m / d)) : (b ^ d + 1) ∣ (b ^ m + 1) := by
  obtain ⟨q, rfl⟩ := hdm
  have hq : Odd q := by rwa [Nat.mul_div_cancel_left q hd] at hodd
  rw [pow_mul]
  exact add_one_dvd_pow_add_one (b ^ d) hq

/-- **Both cofactors odd.** When `m/d` and `n/d` are both odd (`d = gcd m n`),
`bᵈ + 1` is a greatest common divisor of `bᵐ + 1` and `bⁿ + 1`: it divides both,
and every common divisor divides it. -/
theorem isGCD_pow_add_one {m n : ℕ} (hm : 0 < m) (_hn : 0 < n)
    (hmo : Odd (m / Nat.gcd m n)) (hno : Odd (n / Nat.gcd m n)) :
    (b ^ Nat.gcd m n + 1) ∣ (b ^ m + 1) ∧
      (b ^ Nat.gcd m n + 1) ∣ (b ^ n + 1) ∧
      (∀ e : ℤ, e ∣ (b ^ m + 1) → e ∣ (b ^ n + 1) → e ∣ (b ^ Nat.gcd m n + 1)) := by
  set d := Nat.gcd m n with hd
  have hdpos : 0 < d := Nat.gcd_pos_iff.mpr (Or.inl hm)
  have hdm_le : d ≤ m := Nat.le_of_dvd hm (hd ▸ Nat.gcd_dvd_left m n)
  refine ⟨pow_add_one_dvd_of_odd_quotient hdpos (hd ▸ Nat.gcd_dvd_left m n) hmo,
    pow_add_one_dvd_of_odd_quotient hdpos (hd ▸ Nat.gcd_dvd_right m n) hno, ?_⟩
  intro e he_m he_n
  -- Step 1: `e` divides `b^{2m} - 1` and `b^{2n} - 1`.
  have hm2 : e ∣ b ^ (2 * m) - 1 := he_m.trans (by
    have hfac : b ^ (2 * m) - 1 = (b ^ m + 1) * (b ^ m - 1) := by
      rw [two_mul, pow_add]; ring
    rw [hfac]; exact dvd_mul_right _ _)
  have hn2 : e ∣ b ^ (2 * n) - 1 := he_n.trans (by
    have hfac : b ^ (2 * n) - 1 = (b ^ n + 1) * (b ^ n - 1) := by
      rw [two_mul, pow_add]; ring
    rw [hfac]; exact dvd_mul_right _ _)
  -- Step 2: hence `e ∣ b^{2d} - 1`.
  have hgcd2 : Nat.gcd (2 * m) (2 * n) = 2 * d := by rw [Nat.gcd_mul_left, ← hd]
  have h2d : e ∣ b ^ (2 * d) - 1 := by
    have := dvd_pow_gcd_sub_one (b := b) (2 * m) (2 * n) hm2 hn2
    rwa [hgcd2] at this
  -- Step 3: `2d ∣ m - d` because `m/d` is odd.
  obtain ⟨a, hma⟩ : d ∣ m := hd ▸ Nat.gcd_dvd_left m n
  have ha : a = m / d := by rw [hma, Nat.mul_div_cancel_left a hdpos]
  have haodd : Odd a := ha ▸ hmo
  have h2ddvd : (2 * d) ∣ (m - d) := by
    obtain ⟨s, hs⟩ := haodd
    refine ⟨s, ?_⟩
    rw [hma, hs, show d * (2 * s + 1) = 2 * d * s + d from by ring, Nat.add_sub_cancel]
  -- Step 4: `b^{2d} - 1 ∣ bᵐ - bᵈ`, so `e ∣ bᵐ - bᵈ`.
  have hbd : (b ^ (2 * d) - 1) ∣ (b ^ m - b ^ d) := by
    have h2 : b ^ m - b ^ d = b ^ d * (b ^ (m - d) - 1) := by
      have hsum : d + (m - d) = m := by omega
      rw [mul_sub, mul_one, ← pow_add, hsum]
    rw [h2]
    exact (pow_sub_one_dvd_pow_sub_one h2ddvd).mul_left _
  -- Step 5: `e ∣ (bᵐ + 1) - (bᵐ - bᵈ) = bᵈ + 1`.
  have hdiff : e ∣ b ^ m - b ^ d := h2d.trans hbd
  have hsub : e ∣ (b ^ m + 1) - (b ^ m - b ^ d) := dvd_sub he_m hdiff
  have heq : (b ^ m + 1) - (b ^ m - b ^ d) = b ^ d + 1 := by ring
  rwa [heq] at hsub

/-- **Some cofactor even.** If `m/d` is even (`d = gcd m n`), every common divisor
of `bᵐ + 1` and `bⁿ + 1` divides `2` — so their gcd is `1` or `2`. -/
theorem dvd_two_of_even_quotient {m n : ℕ} (hm : 0 < m)
    (hmev : Even (m / Nat.gcd m n)) :
    ∀ e : ℤ, e ∣ (b ^ m + 1) → e ∣ (b ^ n + 1) → e ∣ (2 : ℤ) := by
  intro e he_m he_n
  set d := Nat.gcd m n with hd
  have hdpos : 0 < d := Nat.gcd_pos_iff.mpr (Or.inl hm)
  -- `2d ∣ m` since `m/d` is even.
  have h2dm : (2 * d) ∣ m := by
    obtain ⟨a, hma⟩ : d ∣ m := hd ▸ Nat.gcd_dvd_left m n
    have ha : a = m / d := by rw [hma, Nat.mul_div_cancel_left a hdpos]
    obtain ⟨t, ht⟩ : Even a := ha ▸ hmev
    exact ⟨t, by rw [hma, ht]; ring⟩
  -- `e ∣ b^{2d} - 1` (same engine as the odd case).
  have hm2 : e ∣ b ^ (2 * m) - 1 := he_m.trans (by
    have hfac : b ^ (2 * m) - 1 = (b ^ m + 1) * (b ^ m - 1) := by
      rw [two_mul, pow_add]; ring
    rw [hfac]; exact dvd_mul_right _ _)
  have hn2 : e ∣ b ^ (2 * n) - 1 := he_n.trans (by
    have hfac : b ^ (2 * n) - 1 = (b ^ n + 1) * (b ^ n - 1) := by
      rw [two_mul, pow_add]; ring
    rw [hfac]; exact dvd_mul_right _ _)
  have hgcd2 : Nat.gcd (2 * m) (2 * n) = 2 * d := by rw [Nat.gcd_mul_left, ← hd]
  have h2d : e ∣ b ^ (2 * d) - 1 := by
    have := dvd_pow_gcd_sub_one (b := b) (2 * m) (2 * n) hm2 hn2
    rwa [hgcd2] at this
  -- `b^{2d} - 1 ∣ bᵐ - 1`, so `e ∣ bᵐ - 1`, and `(bᵐ + 1) - (bᵐ - 1) = 2`.
  have hbm : e ∣ b ^ m - 1 := h2d.trans (pow_sub_one_dvd_pow_sub_one h2dm)
  have hsub : e ∣ (b ^ m + 1) - (b ^ m - 1) := dvd_sub he_m hbm
  have heq : (b ^ m + 1) - (b ^ m - 1) = (2 : ℤ) := by ring
  rwa [heq] at hsub

/-- **Closed form for the gcd (both cofactors odd).** For `b ≥ 2`,
`gcd(bᵐ + 1, bⁿ + 1) = b^{gcd(m,n)} + 1` when `m/gcd(m,n)` and `n/gcd(m,n)`
are both odd. -/
theorem int_gcd_pow_add_one {m n : ℕ} (hb : 2 ≤ b) (hm : 0 < m) (hn : 0 < n)
    (hmo : Odd (m / Nat.gcd m n)) (hno : Odd (n / Nat.gcd m n)) :
    (Int.gcd (b ^ m + 1) (b ^ n + 1) : ℤ) = b ^ Nat.gcd m n + 1 := by
  obtain ⟨hA, hB, huniv⟩ := isGCD_pow_add_one (b := b) hm hn hmo hno
  set A := b ^ m + 1 with hAdef
  set B := b ^ n + 1 with hBdef
  set g := b ^ Nat.gcd m n + 1 with hg
  have hb0 : (0 : ℤ) ≤ b := by linarith
  have hpos : (0 : ℤ) < g := by
    have := pow_nonneg hb0 (Nat.gcd m n); rw [hg]; linarith
  have hgcast : (g.toNat : ℤ) = g := Int.toNat_of_nonneg hpos.le
  -- `↑gcd ∣ g` (every common divisor divides `bᵈ + 1`)
  have hgcd_dvd : (Int.gcd A B : ℤ) ∣ g :=
    huniv _ (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)
  -- `g ∣ ↑gcd` (`g` is a common divisor of `A` and `B`)
  have hgdvd : g.toNat ∣ Int.gcd A B := by
    apply Int.dvd_gcd
    · rw [hgcast]; exact hA
    · rw [hgcast]; exact hB
  have hdvd : g ∣ (Int.gcd A B : ℤ) := by
    have := Int.natCast_dvd_natCast.mpr hgdvd
    rwa [hgcast] at this
  have hgnn : (0 : ℤ) ≤ (Int.gcd A B : ℤ) := Int.natCast_nonneg _
  exact Int.dvd_antisymm hgnn hpos.le hgcd_dvd hdvd

/-- **The gcd is `1` or `2` (some cofactor even).** For `b ≥ 2`, if `m/gcd(m,n)`
is even then `gcd(bᵐ + 1, bⁿ + 1) ∣ 2`. -/
theorem int_gcd_pow_add_one_dvd_two {m n : ℕ} (hm : 0 < m)
    (hmev : Even (m / Nat.gcd m n)) :
    Int.gcd (b ^ m + 1) (b ^ n + 1) ∣ 2 := by
  have h : (Int.gcd (b ^ m + 1) (b ^ n + 1) : ℤ) ∣ (2 : ℤ) :=
    dvd_two_of_even_quotient (b := b) hm hmev _ (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)
  exact_mod_cast h

end RepunitPlusOne
