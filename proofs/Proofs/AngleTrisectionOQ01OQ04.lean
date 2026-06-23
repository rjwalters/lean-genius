/-
  Gauss–Wantzel: Structural Tools for Regular Polygon Constructibility
  Open Question: angle-trisection-oq-01-oq-04

  The parent AngleTrisectionOQ01.lean classifies the constructible regular
  n-gons for 3 ≤ n ≤ 20 using the criterion

      RegularNgonConstructible n  ⇔  n ≥ 3 ∧ φ(n) is a power of 2,

  but it discharges every individual case with `native_decide` (which depends
  on `Lean.ofReduceBool`). Its fourth open question asks to extend the
  classification beyond n = 20 toward the general Gauss–Wantzel theorem:

      a regular n-gon is constructible  ⇔  n = 2^a · p₁ ⋯ pₘ
      with the pᵢ distinct Fermat primes.

  This file provides the STRUCTURAL machinery for that extension, proved with
  0 axioms / 0 sorries (no `native_decide`):

    • `totient_two_pow_isPow`  : φ(2^a) is a power of 2.
    • `totient_mul_isPow`      : coprime factors with power-of-2 totients
                                  multiply to a power-of-2 totient
                                  (the multiplicative engine of Gauss–Wantzel).
    • `prime_constructible_iff`: for a prime p, the p-gon is constructible iff
                                  p − 1 is a power of 2 (since φ(p) = p − 1).
    • `fermatPrime_constructible` : every Fermat prime gives a constructible
                                  polygon.
    • `twoPow_constructible`   : every 2^a-gon (a ≥ 2) is constructible.

  Using only these (no per-case `native_decide`), we extend the explicit
  classification with new constructible n-gons (24, 32, 34, 40, 48, 51, 60,
  64, 68, 80, 85, 96, …) and new non-constructible ones (21, 28, 36, …).

  Reference: https://en.wikipedia.org/wiki/Constructible_polygon
-/

import Mathlib

namespace AngleTrisectionGaussWantzel

/-- A regular n-gon is constructible iff n ≥ 3 and φ(n) is a power of 2
    (the parent's definition, reproduced for self-containment). -/
def RegularNgonConstructible (n : ℕ) : Prop :=
  n ≥ 3 ∧ ∃ k : ℕ, Nat.totient n = 2 ^ k

/- ## Part I: Structural tools -/

/-- φ(2^a) is a power of 2 (for a ≥ 1): indeed φ(2^a) = 2^(a-1). -/
theorem totient_two_pow_isPow (a : ℕ) (ha : 1 ≤ a) :
    ∃ k : ℕ, Nat.totient (2 ^ a) = 2 ^ k := by
  refine ⟨a - 1, ?_⟩
  rw [Nat.totient_prime_pow Nat.prime_two ha]
  simp

/-- **Multiplicative engine.** If m and n are coprime and each has a power-of-2
    totient, then so does m·n. This is what lets Gauss–Wantzel build up
    n = 2^a · (distinct Fermat primes) one coprime factor at a time. -/
theorem totient_mul_isPow {m n : ℕ} (h : Nat.Coprime m n)
    (hm : ∃ k : ℕ, Nat.totient m = 2 ^ k) (hn : ∃ j : ℕ, Nat.totient n = 2 ^ j) :
    ∃ i : ℕ, Nat.totient (m * n) = 2 ^ i := by
  obtain ⟨k, hk⟩ := hm
  obtain ⟨j, hj⟩ := hn
  exact ⟨k + j, by rw [Nat.totient_mul h, hk, hj, pow_add]⟩

/-- A 2^a-gon is constructible for a ≥ 2 (so that 2^a ≥ 4 ≥ 3). -/
theorem twoPow_constructible (a : ℕ) (ha : 2 ≤ a) :
    RegularNgonConstructible (2 ^ a) := by
  refine ⟨?_, totient_two_pow_isPow a (by omega)⟩
  calc 3 ≤ 2 ^ 2 := by norm_num
    _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha

/- ## Part II: Prime and Fermat-prime criteria -/

/-- For a prime p ≥ 3, the regular p-gon is constructible iff p − 1 is a power
    of 2. (Equality φ(p) = p − 1 turns the totient criterion into this form.) -/
theorem prime_constructible_iff {p : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p) :
    RegularNgonConstructible p ↔ ∃ k : ℕ, p - 1 = 2 ^ k := by
  unfold RegularNgonConstructible
  rw [Nat.totient_prime hp]
  exact ⟨fun h => h.2, fun h => ⟨hp3, h⟩⟩

/-- Every Fermat prime p = 2^(2^k) + 1 yields a constructible polygon:
    φ(p) = p − 1 = 2^(2^k) is a power of 2. -/
theorem fermatPrime_constructible {p : ℕ} (hp : Nat.Prime p) (k : ℕ)
    (hpk : p = 2 ^ (2 ^ k) + 1) : RegularNgonConstructible p := by
  have h2 : 2 ≤ 2 ^ (2 ^ k) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 ^ k) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
  refine ⟨by omega, 2 ^ k, ?_⟩
  rw [Nat.totient_prime hp, hpk, Nat.add_sub_cancel]

/-- A regular n-gon is NOT constructible if an odd prime divides φ(n). -/
theorem not_constructible_of_odd_prime_dvd_totient (n p : ℕ) (hp : Nat.Prime p)
    (hodd : p ≠ 2) (hdvd : p ∣ Nat.totient n) : ¬ RegularNgonConstructible n := by
  rintro ⟨_, k, hk⟩
  rw [hk] at hdvd
  exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))

/- ## Part III: New constructible n-gons (21 ≤ n ≤ 100), all 0-axiom -/

/-- Helper: 2^a · p constructible when p is an odd prime with power-of-2 totient. -/
private theorem twoPow_mul_constructible (a p : ℕ) (ha : 1 ≤ a) (hge : 3 ≤ 2 ^ a * p)
    (hcop : Nat.Coprime (2 ^ a) p) (hp : ∃ k, Nat.totient p = 2 ^ k) :
    RegularNgonConstructible (2 ^ a * p) :=
  ⟨hge, totient_mul_isPow hcop (totient_two_pow_isPow a ha) hp⟩

theorem constructible_24 : RegularNgonConstructible 24 :=
  twoPow_mul_constructible 3 3 (by norm_num) (by norm_num) (by decide) ⟨1, by decide⟩

theorem constructible_32 : RegularNgonConstructible 32 := twoPow_constructible 5 (by norm_num)

theorem constructible_34 : RegularNgonConstructible 34 :=
  twoPow_mul_constructible 1 17 (by norm_num) (by norm_num) (by decide) ⟨4, by decide⟩

theorem constructible_40 : RegularNgonConstructible 40 :=
  twoPow_mul_constructible 3 5 (by norm_num) (by norm_num) (by decide) ⟨2, by decide⟩

theorem constructible_48 : RegularNgonConstructible 48 :=
  twoPow_mul_constructible 4 3 (by norm_num) (by norm_num) (by decide) ⟨1, by decide⟩

theorem constructible_64 : RegularNgonConstructible 64 := twoPow_constructible 6 (by norm_num)

theorem constructible_68 : RegularNgonConstructible 68 :=
  twoPow_mul_constructible 2 17 (by norm_num) (by norm_num) (by decide) ⟨4, by decide⟩

theorem constructible_80 : RegularNgonConstructible 80 :=
  twoPow_mul_constructible 4 5 (by norm_num) (by norm_num) (by decide) ⟨2, by decide⟩

theorem constructible_96 : RegularNgonConstructible 96 :=
  twoPow_mul_constructible 5 3 (by norm_num) (by norm_num) (by decide) ⟨1, by decide⟩

/-- 51 = 3 · 17, a product of two distinct Fermat primes. -/
theorem constructible_51 : RegularNgonConstructible 51 :=
  ⟨by norm_num, totient_mul_isPow (m := 3) (n := 17) (by decide) ⟨1, by decide⟩ ⟨4, by decide⟩⟩

/-- 85 = 5 · 17, a product of two distinct Fermat primes. -/
theorem constructible_85 : RegularNgonConstructible 85 :=
  ⟨by norm_num, totient_mul_isPow (m := 5) (n := 17) (by decide) ⟨2, by decide⟩ ⟨4, by decide⟩⟩

/-- 60 = 4 · 15 = 2² · 3 · 5, the parent's largest entry × 3. -/
theorem constructible_60 : RegularNgonConstructible 60 :=
  twoPow_mul_constructible 2 15 (by norm_num) (by norm_num) (by decide)
    (totient_mul_isPow (m := 3) (n := 5) (by decide) ⟨1, by decide⟩ ⟨2, by decide⟩)

/- ## Part IV: New non-constructible n-gons -/

/-- Helper: a·b is not constructible if an odd prime p divides φ(b)
    (and a, b are coprime), since then p ∣ φ(a·b). -/
private theorem not_constructible_mul (a b p : ℕ) (hp : Nat.Prime p) (hodd : p ≠ 2)
    (hcop : Nat.Coprime a b) (hdvd : p ∣ Nat.totient b) :
    ¬ RegularNgonConstructible (a * b) := by
  apply not_constructible_of_odd_prime_dvd_totient (a * b) p hp hodd
  rw [Nat.totient_mul hcop]
  exact hdvd.mul_left _

/-- 21 = 3 · 7: φ(7) = 6 is divisible by 3. -/
theorem not_constructible_21 : ¬ RegularNgonConstructible 21 :=
  not_constructible_mul 3 7 3 (by decide) (by decide) (by decide) (by decide)

/-- 28 = 4 · 7: φ(7) = 6 is divisible by 3. -/
theorem not_constructible_28 : ¬ RegularNgonConstructible 28 :=
  not_constructible_mul 4 7 3 (by decide) (by decide) (by decide) (by decide)

/-- 36 = 4 · 9: φ(9) = 6 is divisible by 3. -/
theorem not_constructible_36 : ¬ RegularNgonConstructible 36 :=
  not_constructible_mul 4 9 3 (by decide) (by decide) (by decide) (by decide)

/-- 100 = 4 · 25: φ(25) = 20 is divisible by 5. -/
theorem not_constructible_100 : ¬ RegularNgonConstructible 100 :=
  not_constructible_mul 4 25 5 (by decide) (by decide) (by decide) (by decide)

end AngleTrisectionGaussWantzel
