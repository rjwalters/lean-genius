import Mathlib

/-
# Closed form for Jacobi's σ* via the classical divisor sum (OQ-06-OQ-01)

## Open Question (follow-up to `four-square-distribution-oq-06`)

The parent `four-square-distribution-oq-06` computed Jacobi's modified divisor
sum

  σ*(n) = Σ_{d | n, 4 ∤ d} d

only on *prime powers* (`σ*(pᵏ) = 1 + p + ⋯ + pᵏ` for odd `p`, `σ*(2ᵏ) = 3`).
The natural next question: **is there a single closed form valid for every `n`,
expressing σ* through the ordinary — and fully multiplicative — sum-of-divisors
function `σ(n) = Σ_{d | n} d`?**

## What this provides

A complete reduction of σ* to the classical σ, with no `native_decide` and no
axioms beyond Lean's foundations:

* `sigmaStar_eq_sigma_of_not_four_dvd` — if `4 ∤ n` then **σ*(n) = σ(n)**: no
  divisor of such an `n` is divisible by `4`, so nothing is dropped. (This
  generalizes the parent's "odd ⇒ σ* = σ"; `4 ∤ n` is the sharp hypothesis.)

* `sum_filter_four_dvd` — the dropped part is itself a scaled divisor sum:
  for `4 ∣ n`, `Σ_{d | n, 4 ∣ d} d = 4·σ(n/4)`, via the bijection `e ↦ 4e`
  between `divisors(n/4)` and the multiples-of-4 divisors of `n`.

* `sigmaStar_add_eq` / `sigmaStar_eq_sigma_sub` — the **headline identity**

      σ*(n) = σ(n) − 4·σ(n/4)        (whenever 4 ∣ n).

  This is the structural bridge: σ* is fully determined by the classical,
  multiplicative σ.

* `sigmaStar_two_pow_mul_odd` — the **general odd-part capstone**: writing
  `n = 2ᵃ·m` with `m` odd and `a ≥ 1`, **σ*(n) = 3·σ(m)** depends only on the
  odd part `m`. Combined with `sigmaStar_eq_sigma_of_not_four_dvd` for odd `n`,
  this is Jacobi's complete arithmetic prescription.

* `jacobiR4_of_not_four_dvd`, `jacobiR4_two_pow_mul_odd` — restated for
  `jacobiR4 = 8·σ*`: `r₄(n) = 8·σ(n)` when `4 ∤ n`, and `r₄(2ᵃm) = 24·σ(m)`
  for even arguments — the textbook form of Jacobi's four-square count.

## Honest scope

As in the parent, `jacobiR4` is *defined* as `8·σ*`; these theorems compute that
arithmetic prediction in closed form. They do **not** prove the geometric
identity `r₄(n) = #{(a,b,c,d) : a²+b²+c²+d² = n}`, which is the genuinely open
`jacobi_r4_formula` of OQ-01 (needs the q-expansion of `jacobiTheta⁴`). The
contribution here is the complete arithmetic side, fully machine-checked.
-/

namespace FourSquareDistributionOQ06OQ01

open Finset Nat

/-- Jacobi's modified divisor sum `σ*(n) = Σ_{d | n, 4 ∤ d} d` (same definition
    as `FourSquareDistributionOQ01.sigmaStar`, restated for standalone checking). -/
def sigmaStar (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, if 4 ∣ d then 0 else d

/-- Jacobi's prediction `r₄(n) = 8·σ*(n)`. -/
def jacobiR4 (n : ℕ) : ℕ := 8 * sigmaStar n

-- =====================================================================
-- PART 1: when 4 ∤ n, nothing is dropped and σ* = σ
-- =====================================================================

/-- If `4 ∤ n` then no divisor of `n` is divisible by `4`, so Jacobi's modified
    divisor sum coincides with the ordinary sum-of-divisors function. This is the
    sharp form of the parent's "odd ⇒ σ* = σ" (oddness is stronger than needed). -/
theorem sigmaStar_eq_sigma_of_not_four_dvd {n : ℕ} (hn : ¬ 4 ∣ n) :
    sigmaStar n = ∑ d ∈ n.divisors, d := by
  unfold sigmaStar
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [if_neg]
  intro h4
  exact hn (dvd_trans h4 (Nat.dvd_of_mem_divisors hd))

-- =====================================================================
-- PART 2: the dropped multiples-of-4 form a scaled divisor sum
-- =====================================================================

/-- The divisors of `n` that *are* divisible by `4` are exactly `4·e` for
    `e | (n/4)`; hence their sum is `4·σ(n/4)`. The bijection is `e ↦ 4e`. -/
theorem sum_filter_four_dvd {n : ℕ} (hn : 4 ∣ n) :
    ∑ d ∈ n.divisors.filter (fun d => 4 ∣ d), d
      = 4 * ∑ e ∈ (n / 4).divisors, e := by
  have hset : n.divisors.filter (fun d => 4 ∣ d)
      = (n / 4).divisors.image (fun e => 4 * e) := by
    ext d
    simp only [mem_filter, mem_image, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdn, hn0⟩, hd4⟩
      obtain ⟨c, rfl⟩ := hd4
      refine ⟨c, ⟨?_, ?_⟩, by ring⟩
      · have h : 4 * c ∣ 4 * (n / 4) := by rwa [Nat.mul_div_cancel' hn]
        exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 4)).mp h
      · intro h
        apply hn0
        rw [← Nat.mul_div_cancel' hn, h, Nat.mul_zero]
    · rintro ⟨c, ⟨hc, hn40⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_right 4 c⟩
      · have h : 4 * c ∣ 4 * (n / 4) := Nat.mul_dvd_mul_left 4 hc
        rwa [Nat.mul_div_cancel' hn] at h
      · intro h
        apply hn40
        rw [h, Nat.zero_div]
  rw [hset, Finset.sum_image
        (by intro a _ b _ hab; exact Nat.eq_of_mul_eq_mul_left (by norm_num) hab)]
  exact (Finset.mul_sum _ _ _).symm

-- =====================================================================
-- PART 3: the headline identity  σ*(n) = σ(n) − 4·σ(n/4)
-- =====================================================================

/-- Additive form of the headline identity (avoids `ℕ` truncated subtraction):
    `σ*(n) + 4·σ(n/4) = σ(n)` whenever `4 ∣ n`. -/
theorem sigmaStar_add_eq {n : ℕ} (hn : 4 ∣ n) :
    sigmaStar n + 4 * ∑ e ∈ (n / 4).divisors, e = ∑ d ∈ n.divisors, d := by
  have hfilter : ∑ d ∈ n.divisors, (if 4 ∣ d then d else 0)
      = 4 * ∑ e ∈ (n / 4).divisors, e := by
    rw [← Finset.sum_filter, sum_filter_four_dvd hn]
  have key : ∀ d, (if 4 ∣ d then 0 else d) + (if 4 ∣ d then d else 0) = d := by
    intro d; split <;> simp
  unfold sigmaStar
  rw [← hfilter, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun d _ => key d)

/-- **Headline identity.** Jacobi's modified divisor sum is determined by the
    classical (multiplicative) sum-of-divisors function:

      `σ*(n) = σ(n) − 4·σ(n/4)`   whenever `4 ∣ n`. -/
theorem sigmaStar_eq_sigma_sub {n : ℕ} (hn : 4 ∣ n) :
    sigmaStar n = (∑ d ∈ n.divisors, d) - 4 * ∑ e ∈ (n / 4).divisors, e := by
  have h := sigmaStar_add_eq hn
  omega

-- =====================================================================
-- PART 4: the general odd-part capstone  σ*(2ᵃ·m) = 3·σ(m)
-- =====================================================================

/-- Geometric divisor sum of a power of two: `σ(2ᵃ) = 2^{a+1} − 1`. -/
theorem sigma_two_pow (a : ℕ) : ∑ d ∈ (2 ^ a).divisors, d = 2 ^ (a + 1) - 1 := by
  have geom : ∀ b : ℕ, ∑ i ∈ Finset.range (b + 1), 2 ^ i = 2 ^ (b + 1) - 1 := by
    intro b
    induction b with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have h2 : (2 : ℕ) ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; ring
      have h1 : 1 ≤ (2 : ℕ) ^ (k + 1) := Nat.one_le_two_pow
      omega
  rw [Nat.divisors_prime_pow Nat.prime_two, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  exact geom a

/-- **Odd-part capstone.** For `n = 2ᵃ·m` with `m` odd and `a ≥ 1`, Jacobi's
    modified divisor sum depends only on the odd part: `σ*(2ᵃ·m) = 3·σ(m)`. -/
theorem sigmaStar_two_pow_mul_odd {m : ℕ} (hm : Odd m) {a : ℕ} (ha : 1 ≤ a) :
    sigmaStar (2 ^ a * m) = 3 * ∑ d ∈ m.divisors, d := by
  -- 2 (hence 2ᵃ) is coprime to the odd number m
  have hcop2 : Nat.Coprime 2 m :=
    (Nat.prime_two.coprime_iff_not_dvd).mpr (by
      rw [Nat.two_dvd_ne_zero]; exact Nat.odd_iff.mp hm)
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  · -- a = 1 : here 4 ∤ 2m, so σ* = σ and σ(2m) = σ(2)·σ(m) = 3·σ(m)
    interval_cases a
    have hnot : ¬ (4 : ℕ) ∣ 2 * m := by
      have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
      omega
    rw [pow_one, sigmaStar_eq_sigma_of_not_four_dvd hnot,
        Nat.Coprime.sum_divisors_mul hcop2]
    norm_num [show ∑ d ∈ (2 : ℕ).divisors, d = 3 from by decide]
  · -- a ≥ 2 : use σ*(n) = σ(n) − 4·σ(n/4) with n/4 = 2^{a-2}·m
    have hcopA : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a hcop2
    have hcopB : Nat.Coprime (2 ^ (a - 2)) m := Nat.Coprime.pow_left _ hcop2
    -- 4 ∣ 2ᵃ·m
    have h4n : (4 : ℕ) ∣ 2 ^ a * m := by
      have : (2 : ℕ) ^ 2 ∣ 2 ^ a := pow_dvd_pow 2 ha2
      exact Dvd.dvd.mul_right (by simpa using this) m
    -- (2ᵃ·m)/4 = 2^{a-2}·m
    have hquot : (2 ^ a * m) / 4 = 2 ^ (a - 2) * m := by
      have hpow : (2 : ℕ) ^ a = 4 * 2 ^ (a - 2) := by
        rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]
        congr 1; omega
      rw [hpow, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
    -- the additive identity, with both divisor sums factored
    have hadd := sigmaStar_add_eq h4n
    rw [hquot, Nat.Coprime.sum_divisors_mul hcopA,
        Nat.Coprime.sum_divisors_mul hcopB, sigma_two_pow, sigma_two_pow] at hadd
    -- normalise exponents:  a = b + 2,  so  a-2 = b,  a+1 = b+2+1
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
    have hP : 1 ≤ (2 : ℕ) ^ (b + 1) := Nat.one_le_two_pow
    have hpw : (2 : ℕ) ^ (b + 2 + 1) = 4 * 2 ^ (b + 1) := by
      rw [show b + 2 + 1 = (b + 1) + 2 from by ring, pow_add]; ring
    -- simplify the exponent b+2-2 = b in hadd
    simp only [Nat.add_sub_cancel] at hadd
    set S := ∑ d ∈ m.divisors, d with hS
    -- hadd : σ* + 4 * ((2^{b+1} − 1) * S) = (2^{b+2+1} − 1) * S
    -- write 2^{b+1} = Q+1 to clear all truncated subtractions, then cancel
    obtain ⟨Q, hQ⟩ : ∃ Q, (2 : ℕ) ^ (b + 1) = Q + 1 := ⟨2 ^ (b + 1) - 1, by omega⟩
    rw [hpw, hQ] at hadd
    simp only [Nat.add_sub_cancel] at hadd
    have hc : 4 * (Q + 1) - 1 = 4 * Q + 3 := by omega
    rw [hc] at hadd
    have hexp : (4 * Q + 3) * S = 4 * (Q * S) + 3 * S := by ring
    rw [hexp] at hadd
    omega

-- =====================================================================
-- PART 5: Jacobi's r₄ count in textbook closed form
-- =====================================================================

/-- For `4 ∤ n` Jacobi's prediction is `r₄(n) = 8·σ(n)`. -/
theorem jacobiR4_of_not_four_dvd {n : ℕ} (hn : ¬ 4 ∣ n) :
    jacobiR4 n = 8 * ∑ d ∈ n.divisors, d := by
  unfold jacobiR4
  rw [sigmaStar_eq_sigma_of_not_four_dvd hn]

/-- For even arguments `n = 2ᵃ·m` (`m` odd, `a ≥ 1`) Jacobi's prediction depends
    only on the odd part: `r₄(2ᵃ·m) = 24·σ(m)`. -/
theorem jacobiR4_two_pow_mul_odd {m : ℕ} (hm : Odd m) {a : ℕ} (ha : 1 ≤ a) :
    jacobiR4 (2 ^ a * m) = 24 * ∑ d ∈ m.divisors, d := by
  unfold jacobiR4
  rw [sigmaStar_two_pow_mul_odd hm ha]
  ring

-- =====================================================================
-- PART 6: sanity instances, all `native_decide`-free
-- =====================================================================

/-- `σ*(12) = 3·σ(3) = 12` — the `a = 2, m = 3` instance of the capstone. -/
theorem sigmaStar_twelve : sigmaStar 12 = 12 := by
  have h : sigmaStar (2 ^ 2 * 3) = 3 * ∑ d ∈ (3 : ℕ).divisors, d :=
    sigmaStar_two_pow_mul_odd (by decide) (by norm_num)
  norm_num [show ∑ d ∈ (3 : ℕ).divisors, d = 4 from by decide] at h
  simpa using h

/-- `r₄(12) = 24·σ(3) = 96`, recovered symbolically. -/
theorem jacobiR4_twelve : jacobiR4 12 = 96 := by
  unfold jacobiR4
  rw [sigmaStar_twelve]

end FourSquareDistributionOQ06OQ01
