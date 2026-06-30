/-
# Rational radicands: q^(1/n) ∈ ℚ ⟺ numerator and denominator are perfect n-th powers

The parent entry (`cube-root-2-irrational-oq-05-oq-01`) proves, for a *natural* radicand,
that `m^(1/n)` is rational iff `m` is a perfect `n`-th power. Its first open question asks to
extend this to **rational** radicands:

> *Extend the criterion to rational radicands: `q^(1/n)` for `q : ℚ⁺` is rational iff both
> numerator and denominator of `q` (in lowest terms) are perfect n-th powers.*

This file proves exactly that. For `q > 0` and `n ≥ 1`,

  `q^(1/n)` is rational  ⟺  `q.num` and `q.den` are both perfect `n`-th powers.

The key idea: `q^(1/n)` is rational iff `q = sⁿ` for some positive rational `s`. Writing
`s = c/d` in lowest terms, `sⁿ = cⁿ/dⁿ` is *also* in lowest terms (coprimality is preserved by
powers), so by uniqueness of the reduced representation `q.num = cⁿ` and `q.den = dⁿ`. This uses
`Rat.num_pow`/`Rat.den_pow` (`(sⁿ).num = s.numⁿ`, `(sⁿ).den = s.denⁿ`), which already encode that
uniqueness.

The integer/natural criterion is recovered as the special case `q.den = 1` (a positive integer is
a perfect `n`-th power as a rational iff it is as a natural number).

## Main results

* `rat_rpow_inv_pow`                 : `(q^(1/n))ⁿ = q` for `q ≥ 0`.
* `rational_rpow_inv_iff_exists_rat` : `q^(1/n)` rational ⟺ `∃ s : ℚ, 0 < s ∧ sⁿ = q`.
* `exists_rat_pow_iff_perfect`       : `∃ s, 0 < s ∧ sⁿ = q` ⟺ `q.num`, `q.den` perfect n-th powers.
* `rational_rpow_inv_iff_rat`        : the criterion, assembled.
* `irrational_rpow_inv_iff_rat`      : the negated (irrationality) form.
-/

import Mathlib

namespace CubeRoot2IrrationalOQ05OQ01OQ01

open Real

/-- `m` is a perfect `n`-th power: there is a natural number `k` with `k ^ n = m`. -/
def IsPerfectNthPow (m n : ℕ) : Prop := ∃ k : ℕ, k ^ n = m

/-- The defining identity of the real `n`-th root for a rational radicand: for `q ≥ 0` and
`n ≥ 1`, `(q^(1/n))ⁿ = q`. -/
theorem rat_rpow_inv_pow {q : ℚ} (hq : 0 ≤ q) {n : ℕ} (hn : 0 < n) :
    ((q : ℝ) ^ ((n : ℝ)⁻¹)) ^ n = (q : ℝ) := by
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [← Real.rpow_natCast ((q : ℝ) ^ ((n : ℝ)⁻¹)) n, ← Real.rpow_mul hq0,
    inv_mul_cancel₀ hn0, Real.rpow_one]

/-- **Bridge to rational `n`-th powers.** For `q > 0` and `n ≥ 1`, the real root `q^(1/n)` is
rational (not irrational) iff `q` is the `n`-th power of a positive rational. -/
theorem rational_rpow_inv_iff_exists_rat {q : ℚ} (hq : 0 < q) {n : ℕ} (hn : 0 < n) :
    (¬ Irrational ((q : ℝ) ^ ((n : ℝ)⁻¹))) ↔ ∃ s : ℚ, 0 < s ∧ s ^ n = q := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  constructor
  · intro hrat
    obtain ⟨s, hs⟩ := not_not.mp hrat
    refine ⟨s, ?_, ?_⟩
    · have hpos : (0 : ℝ) < (s : ℝ) := by rw [hs]; exact Real.rpow_pos_of_pos hqR _
      exact_mod_cast hpos
    · have hpow : ((s : ℝ)) ^ n = (q : ℝ) := by rw [hs, rat_rpow_inv_pow hq.le hn]
      have : ((s ^ n : ℚ) : ℝ) = ((q : ℚ) : ℝ) := by push_cast; exact hpow
      exact_mod_cast this
  · rintro ⟨s, hs0, hsn⟩
    have hs0R : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs0
    have hval : ((q : ℝ)) ^ ((n : ℝ)⁻¹) = (s : ℝ) := by
      rw [← hsn]
      push_cast
      rw [← Real.rpow_natCast (s : ℝ) n, ← Real.rpow_mul hs0R.le,
        mul_inv_cancel₀ (by positivity), Real.rpow_one]
    rw [hval]
    exact (s).not_irrational

/-- **The arithmetic core.** For `q > 0` and `n ≥ 1`, `q` is the `n`-th power of a positive
rational iff its numerator and denominator are both perfect `n`-th powers. -/
theorem exists_rat_pow_iff_perfect {q : ℚ} (hq : 0 < q) {n : ℕ} (hn : 0 < n) :
    (∃ s : ℚ, 0 < s ∧ s ^ n = q)
      ↔ (IsPerfectNthPow q.num.toNat n ∧ IsPerfectNthPow q.den n) := by
  have hnumpos : 0 < q.num := Rat.num_pos.mpr hq
  constructor
  · rintro ⟨s, hs0, hsn⟩
    have hsnum0 : 0 ≤ s.num := (Rat.num_pos.mpr hs0).le
    have hnum : q.num = s.num ^ n := by rw [← hsn, Rat.num_pow]
    have hden : q.den = s.den ^ n := by rw [← hsn, Rat.den_pow]
    refine ⟨⟨s.num.toNat, ?_⟩, ⟨s.den, ?_⟩⟩
    · -- s.num.toNat ^ n = q.num.toNat
      have key : ((s.num.toNat ^ n : ℕ) : ℤ) = s.num ^ n := by
        push_cast
        rw [Int.toNat_of_nonneg hsnum0]
      rw [hnum, ← key, Int.toNat_natCast]
    · rw [hden]
  · rintro ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
    -- c ^ n = q.num.toNat, d ^ n = q.den
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · exfalso; rw [Nat.zero_pow hn] at hd; exact q.den_pos.ne' hd.symm
      · exact h
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with rfl | h
      · exfalso; rw [Nat.zero_pow hn] at hc
        rw [eq_comm, Int.toNat_eq_zero] at hc; omega
      · exact h
    have hqn0 : 0 ≤ q.num := hnumpos.le
    have hqnum : (q.num : ℚ) = (c : ℚ) ^ n := by
      have hz : q.num = ((c ^ n : ℕ) : ℤ) := by
        rw [← Int.toNat_of_nonneg hqn0, hc]
      rw [hz]; push_cast; ring
    have hqden : (q.den : ℚ) = (d : ℚ) ^ n := by rw [← hd]; push_cast; ring
    refine ⟨(c : ℚ) / (d : ℚ), by positivity, ?_⟩
    rw [div_pow, ← hqnum, ← hqden, Rat.num_div_den]

/-- **The rational-radicand criterion (OQ-05-OQ-01-OQ-01).** For `q > 0` and `n ≥ 1`, the real
`n`-th root `q^(1/n)` is rational **iff** both the numerator and the denominator of `q` (in lowest
terms) are perfect `n`-th powers. -/
theorem rational_rpow_inv_iff_rat {q : ℚ} (hq : 0 < q) {n : ℕ} (hn : 0 < n) :
    (¬ Irrational ((q : ℝ) ^ ((n : ℝ)⁻¹)))
      ↔ (IsPerfectNthPow q.num.toNat n ∧ IsPerfectNthPow q.den n) :=
  (rational_rpow_inv_iff_exists_rat hq hn).trans (exists_rat_pow_iff_perfect hq hn)

/-- **The irrationality form.** `q^(1/n)` is irrational iff `q` fails to have both a perfect
`n`-th power numerator and a perfect `n`-th power denominator. -/
theorem irrational_rpow_inv_iff_rat {q : ℚ} (hq : 0 < q) {n : ℕ} (hn : 0 < n) :
    Irrational ((q : ℝ) ^ ((n : ℝ)⁻¹))
      ↔ ¬ (IsPerfectNthPow q.num.toNat n ∧ IsPerfectNthPow q.den n) := by
  rw [← not_iff_not, not_not]
  exact rational_rpow_inv_iff_rat hq hn

/-- **Integer special case.** For a positive integer radicand (`q.den = 1`), the criterion reduces
to the parent's natural-number criterion: `m^(1/n)` is rational iff `m` is a perfect `n`-th power.
The denominator condition `IsPerfectNthPow 1 n` is automatic (`1 = 1ⁿ`). -/
theorem rational_rpow_inv_iff_natCast {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (¬ Irrational ((m : ℝ) ^ ((n : ℝ)⁻¹))) ↔ IsPerfectNthPow m n := by
  have hmq : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hcast : ((m : ℚ) : ℝ) = (m : ℝ) := by push_cast; ring
  rw [← hcast, rational_rpow_inv_iff_rat hmq hn]
  have hnum : ((m : ℚ)).num.toNat = m := by simp [Rat.num_natCast]
  have hden : ((m : ℚ)).den = 1 := by simp [Rat.den_natCast]
  rw [hnum, hden]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, ⟨1, by simp⟩⟩

end CubeRoot2IrrationalOQ05OQ01OQ01
