import Mathlib

/-
# Multiplicativity of Jacobi's σ* and the assembled closed form (OQ-06-OQ-02)

## Open Question (follow-up to `four-square-distribution-oq-06`)

The parent `four-square-distribution-oq-06` computed Jacobi's modified divisor
sum

  σ*(n) = Σ_{d | n, 4 ∤ d} d

on individual prime powers, and its child OQ-06-OQ-01 assembled the local values
`σ*(2ᵃ·m) = 3·σ(m)` (a ≥ 1) and `σ*(n) = σ(n)` (4 ∤ n) by a hands-on divisor-sum
computation. The parent's stated open target, however, was the *structural*
reason those local pieces fit together into one formula:

> Writing `n = 2ᵏ·m` with `m` odd, **multiplicativity of σ*** should give
> `σ*(n) = 3·σ(m)` for `k ≥ 1` and `σ*(n) = σ(m)` for `k = 0`; formalizing the
> multiplicativity of σ* would close the gap between the prime-power values and
> arbitrary `n`.

This entry proves exactly that multiplicativity — `σ*` **is a multiplicative
arithmetic function** — and then re-derives the assembled closed form as a clean
one-line corollary, replacing OQ-06-OQ-01's bespoke `ℕ`-subtraction argument.

## What this provides

* `weightedId` — the arithmetic function `g(d) = [4 ∤ d]·d` (the summand of σ*),
  packaged as a `Mathlib` `ArithmeticFunction ℕ`.

* `weightedId_isMultiplicative` — the heart: `g` is multiplicative,
  `g(m·n) = g(m)·g(n)` for coprime `m, n`. The only content is the divisor
  fact `4 ∤ m·n ⟸ 4 ∤ m ∧ 4 ∤ n` for coprime arguments (a factor `2` can live
  in only one of them, so a factor `4` is confined to one side).

* `sigmaStar_eq_zeta_mul` — `σ* = ζ ⋆ g` as a Dirichlet convolution, exhibiting
  σ* as the divisor-summatory function of `g`.

* `sigmaStar_isMultiplicative` / `sigmaStar_mul_coprime` — the **headline
  result**: `σ*` is multiplicative, so `σ*(m·n) = σ*(m)·σ*(n)` whenever
  `gcd(m, n) = 1`. This is the parent's open target.

* `sigmaStar_two_pow` — `σ*(2ᵏ) = 1` for `k = 0` and `= 3` for `k ≥ 1` (only the
  divisors `1, 2` escape being multiples of `4`).

* `sigmaStar_assembled` — the parent's assembled formula, *derived from
  multiplicativity*: for `m` odd, `σ*(2ᵏ·m) = (if k = 0 then 1 else 3)·σ(m)`.

## Honest scope

As in the parent family, `jacobiR4` is *defined* as `8·σ*`; nothing here touches
the genuinely open geometric identity `r₄(n) = #{(a,b,c,d) : Σ = n}` (which needs
the q-expansion of `jacobiTheta⁴`). The contribution is the structural
multiplicativity of the arithmetic side, fully machine-checked and 0-axiom.
-/

namespace FourSquareDistributionOQ06OQ02

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.zeta

/-- Jacobi's modified divisor sum `σ*(n) = Σ_{d | n, 4 ∤ d} d`
    (same definition as the parent family, restated for standalone checking). -/
def sigmaStar (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, if 4 ∣ d then 0 else d

/-- The summand of `σ*`, as an arithmetic function: `g(d) = [4 ∤ d]·d`.
    `g 0 = 0` because `4 ∣ 0`, so this is a genuine `ArithmeticFunction`. -/
def weightedId : ArithmeticFunction ℕ :=
  ⟨fun d => if 4 ∣ d then 0 else d, by simp⟩

@[simp] theorem weightedId_apply (d : ℕ) :
    weightedId d = if 4 ∣ d then 0 else d := rfl

-- =====================================================================
-- PART 1: `g` is multiplicative
-- =====================================================================

/-- Coprimality confines a factor of `4` to one side: if `gcd(m, n) = 1`, then
    `4 ∣ m·n` forces `4 ∣ m` or `4 ∣ n`. (A factor `2` can divide at most one of
    two coprime numbers, so the two factors of `2` in `4` cannot be split.) -/
theorem four_dvd_mul_of_coprime {m n : ℕ} (hmn : Nat.Coprime m n)
    (h4 : 4 ∣ m * n) : 4 ∣ m ∨ 4 ∣ n := by
  by_cases h2m : 2 ∣ m
  · -- 2 ∣ m ⇒ (coprime) 2 ∤ n ⇒ Coprime 4 n ⇒ 4 ∣ m
    have h2n : ¬ 2 ∣ n := by
      intro h2n
      have hd : (2 : ℕ) ∣ Nat.gcd m n := Nat.dvd_gcd h2m h2n
      rw [Nat.Coprime] at hmn
      rw [hmn] at hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    have hc4n : Nat.Coprime 4 n := by
      have hc2n : Nat.Coprime 2 n := (Nat.prime_two.coprime_iff_not_dvd).mpr h2n
      simpa [show (4 : ℕ) = 2 ^ 2 from rfl] using hc2n.pow_left 2
    exact Or.inl (hc4n.dvd_of_dvd_mul_right h4)
  · -- 2 ∤ m ⇒ Coprime 4 m ⇒ 4 ∣ n
    have hc4m : Nat.Coprime 4 m := by
      have hc2m : Nat.Coprime 2 m := (Nat.prime_two.coprime_iff_not_dvd).mpr h2m
      simpa [show (4 : ℕ) = 2 ^ 2 from rfl] using hc2m.pow_left 2
    exact Or.inr (hc4m.dvd_of_dvd_mul_left h4)

/-- **The summand is multiplicative.** `g(d) = [4 ∤ d]·d` satisfies
    `g 1 = 1` and `g(m·n) = g(m)·g(n)` for coprime `m, n`. -/
theorem weightedId_isMultiplicative : weightedId.IsMultiplicative := by
  refine ⟨by simp, ?_⟩
  intro m n hmn
  simp only [weightedId_apply]
  by_cases hm : 4 ∣ m
  · rw [if_pos hm, zero_mul, if_pos (hm.mul_right n)]
  · by_cases hn : 4 ∣ n
    · rw [if_pos hn, mul_zero, if_pos (hn.mul_left m)]
    · rw [if_neg hm, if_neg hn, if_neg ?_]
      intro h4
      rcases four_dvd_mul_of_coprime hmn h4 with h | h
      · exact hm h
      · exact hn h

-- =====================================================================
-- PART 2: σ* = ζ ⋆ g, hence σ* is multiplicative
-- =====================================================================

/-- `σ*` is the divisor-summatory function of `g`, i.e. the Dirichlet
    convolution `ζ ⋆ g`. -/
theorem sigmaStar_eq_zeta_mul (n : ℕ) : sigmaStar n = (ζ * weightedId) n := by
  rw [zeta_mul_apply]
  simp only [sigmaStar, weightedId_apply]

/-- **Headline result.** Jacobi's modified divisor sum `σ*` is a multiplicative
    arithmetic function: it is `ζ ⋆ g` with both factors multiplicative. -/
theorem sigmaStar_isMultiplicative : (ζ * weightedId).IsMultiplicative :=
  isMultiplicative_zeta.mul weightedId_isMultiplicative

/-- **Multiplicativity of σ*** (the parent's open target): for coprime `m, n`,

      σ*(m·n) = σ*(m) · σ*(n). -/
theorem sigmaStar_mul_coprime {m n : ℕ} (hmn : Nat.Coprime m n) :
    sigmaStar (m * n) = sigmaStar m * sigmaStar n := by
  rw [sigmaStar_eq_zeta_mul, sigmaStar_eq_zeta_mul, sigmaStar_eq_zeta_mul]
  exact sigmaStar_isMultiplicative.2 hmn

-- =====================================================================
-- PART 3: local values, and the assembled closed form via multiplicativity
-- =====================================================================

/-- On numbers with `4 ∤ n`, `σ*` is the ordinary sum-of-divisors `σ`. In
    particular this covers all odd `n`. -/
theorem sigmaStar_eq_sigma_of_not_four_dvd {n : ℕ} (hn : ¬ 4 ∣ n) :
    sigmaStar n = ∑ d ∈ n.divisors, d := by
  unfold sigmaStar
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [if_neg]
  exact fun h4 => hn (dvd_trans h4 (Nat.dvd_of_mem_divisors hd))

/-- `σ*(1) = 1`. -/
@[simp] theorem sigmaStar_one : sigmaStar 1 = 1 := by decide

/-- Power-of-two values: `σ*(2ᵏ⁺¹) = 3` — only the divisors `1` and `2` of `2ᵏ⁺¹`
    escape being multiples of `4`. Proved by induction: passing from `2ᵏ⁺¹` to
    `2ᵏ⁺²` adjoins the divisor `2ᵏ⁺²`, a multiple of `4`, contributing `0`. -/
theorem sigmaStar_two_pow_succ (k : ℕ) : sigmaStar (2 ^ (k + 1)) = 3 := by
  have key : ∀ a, sigmaStar (2 ^ a)
      = ∑ i ∈ Finset.range (a + 1), weightedId (2 ^ i) := by
    intro a
    rw [sigmaStar_eq_zeta_mul, zeta_mul_apply, Nat.divisors_prime_pow Nat.prime_two,
        Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk]
  induction k with
  | zero => decide
  | succ j ih =>
    rw [key] at ih ⊢
    rw [Finset.sum_range_succ]
    have htop : weightedId (2 ^ (j + 1 + 1)) = 0 := by
      simp only [weightedId_apply]
      rw [if_pos]
      exact ⟨2 ^ j, by ring⟩
    rw [htop, add_zero]
    exact ih

/-- Uniform statement of the power-of-two values: `σ*(2ᵏ) = if k = 0 then 1 else 3`. -/
theorem sigmaStar_two_pow (k : ℕ) :
    sigmaStar (2 ^ k) = if k = 0 then 1 else 3 := by
  cases k with
  | zero => simp
  | succ j => simp [sigmaStar_two_pow_succ j]

/-- **Assembled closed form, derived from multiplicativity.** Writing
    `n = 2ᵏ·m` with `m` odd,

      σ*(2ᵏ·m) = (if k = 0 then 1 else 3) · σ(m).

    Contrast OQ-06-OQ-01, which proved this by a direct truncated-subtraction
    computation; here it is a one-line consequence of `sigmaStar_mul_coprime`
    together with the two local values `σ*(2ᵏ)` and `σ*(m) = σ(m)`. -/
theorem sigmaStar_assembled {m : ℕ} (hm : Odd m) (k : ℕ) :
    sigmaStar (2 ^ k * m) = (if k = 0 then 1 else 3) * ∑ d ∈ m.divisors, d := by
  have hcop : Nat.Coprime (2 ^ k) m := by
    have hc2 : Nat.Coprime 2 m :=
      (Nat.prime_two.coprime_iff_not_dvd).mpr (by
        rw [Nat.two_dvd_ne_zero]; exact Nat.odd_iff.mp hm)
    exact hc2.pow_left k
  have hmnot : ¬ (4 : ℕ) ∣ m := by
    have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
    omega
  rw [sigmaStar_mul_coprime hcop, sigmaStar_two_pow,
      sigmaStar_eq_sigma_of_not_four_dvd hmnot]

-- =====================================================================
-- PART 4: Jacobi's r₄ prediction, and sanity instances
-- =====================================================================

/-- Jacobi's prediction `r₄(n) = 8·σ*(n)`. -/
def jacobiR4 (n : ℕ) : ℕ := 8 * sigmaStar n

/-- For even arguments `n = 2ᵏ·m` (`m` odd, `k ≥ 1`), Jacobi's prediction depends
    only on the odd part: `r₄(2ᵏ·m) = 24·σ(m)` — now via multiplicativity. -/
theorem jacobiR4_two_pow_mul_odd {m : ℕ} (hm : Odd m) {k : ℕ} (hk : 1 ≤ k) :
    jacobiR4 (2 ^ k * m) = 24 * ∑ d ∈ m.divisors, d := by
  unfold jacobiR4
  rw [sigmaStar_assembled hm k, if_neg (by omega : ¬ k = 0)]
  ring

/-- `σ*(12) = 3·σ(3) = 12`, as the `k = 2, m = 3` instance of the assembled form. -/
theorem sigmaStar_twelve : sigmaStar 12 = 12 := by
  have h := sigmaStar_assembled (show Odd 3 by decide) 2
  norm_num [show ∑ d ∈ (3 : ℕ).divisors, d = 4 from by decide] at h
  simpa using h

/-- `r₄(12) = 24·σ(3) = 96`, recovered from the assembled form. -/
theorem jacobiR4_twelve : jacobiR4 12 = 96 := by
  unfold jacobiR4
  rw [sigmaStar_twelve]

/-- Multiplicativity in action: `σ*(45) = σ*(9)·σ*(5) = 13·6 = 78` (`45 = 9·5`,
    both odd, so `σ* = σ` on each). -/
theorem sigmaStar_fortyfive : sigmaStar 45 = 78 := by
  have h : sigmaStar (9 * 5) = sigmaStar 9 * sigmaStar 5 :=
    sigmaStar_mul_coprime (by decide)
  norm_num at h
  rw [h]
  decide

end FourSquareDistributionOQ06OQ02
