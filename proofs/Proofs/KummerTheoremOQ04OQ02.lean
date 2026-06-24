import Mathlib

/-
# The 2-adic Valuation of the Catalan Number `Cₙ`

## The Open Question

The parent result (`KummerTheoremOQ04`) computes the 2-adic valuation of the
**central** binomial coefficient as the binary digit sum:

$$\nu_2\binom{2n}{n} \;=\; s_2(n),$$

where `s₂(n) = (Nat.digits 2 n).sum` is the number of `1`-bits of `n` (its popcount).

The natural follow-up asks for the exact 2-adic valuation of the **Catalan number**
`Cₙ = catalan n = \frac1{n+1}\binom{2n}{n}` — the quotient of the central binomial
coefficient by `n + 1`. What is `v₂(Cₙ)` in closed form?

## Answer: it is the binary digit sum of `n + 1`, minus one

$$\boxed{\;\nu_2(C_n) \;=\; s_2(n+1) - 1\;}$$

### Why this is true

Catalan's identity `(n+1)·Cₙ = C(2n,n)` (`succ_mul_catalan_eq_centralBinom`)
gives, on taking `v₂` (additive on products of nonzero naturals),

  `v₂(n+1) + v₂(Cₙ) = v₂(C(2n,n)) = s₂(n)`.            (★)

It remains to eliminate `v₂(n+1)` in favour of the digit sums.  Legendre's formula
`v₂(m!) = m − s₂(m)` applied to `m = n` and `m = n+1`, together with
`(n+1)! = (n+1)·n!`, yields the **carry identity**

  `s₂(n) + 1 = s₂(n+1) + v₂(n+1)`.                      (carry)

This is the binary "adding one" relation: incrementing `n` clears its `v₂(n+1)`
trailing one-bits and sets one new bit, changing the popcount by `1 − v₂(n+1)`.
Subtracting (carry) from (★) gives `v₂(Cₙ) + 1 = s₂(n+1)`, i.e. the boxed formula.

### Sharp consequence: which Catalan numbers are odd?

Since `s₂(n+1) ≥ 1`, the valuation vanishes iff `s₂(n+1) = 1`, i.e. iff `n + 1` is a
power of two.  Hence

$$C_n \text{ is odd} \iff n = 2^k - 1.$$

This recovers the classical fact that the odd Catalan numbers occur exactly at the
indices `0, 1, 3, 7, 15, 31, …` (Mersenne-type indices `2^k - 1`).

## What Mathlib already has

Mathlib provides `succ_mul_catalan_eq_centralBinom`, Legendre's formula
`sub_one_mul_padicValNat_factorial`, and `padicValNat.mul`.  It does **not** package
the 2-adic valuation of the Catalan number, the carry identity, nor the
characterisation of the odd Catalan numbers.

## Results in this file (original content, all 0 axioms / 0 sorries)

* `digit_sum_succ_carry`         : `s₂(n) + 1 = s₂(n+1) + v₂(n+1)` (the carry identity)
* `padicValNat_two_catalan_add_one` : `v₂(Cₙ) + 1 = s₂(n+1)` (subtraction-free form)
* `padicValNat_two_catalan`      : **the headline** `v₂(Cₙ) = s₂(n+1) − 1`
* `catalan_ne_zero`              : `Cₙ ≠ 0`
* `two_pow_dvd_catalan` / `not_two_pow_succ_dvd_catalan`
                                 : `2^{s₂(n+1)−1}` divides `Cₙ` *exactly*
* `odd_catalan_iff`              : `Odd Cₙ ↔ ∃ k, n = 2^k − 1` (the odd Catalan numbers)
* worked numeric witnesses (`C₂=2`, `C₃=5` odd, `C₄=14=2·7`, ...)
-/

namespace KummerCatalan

open Nat

/-! ### Reusable digit-sum infrastructure (kept self-contained)

These four lemmas are re-derived from the parent (`KummerTheoremOQ04`) so the file
imports only `Mathlib`. -/

/-- **Doubling-invariance of the binary digit sum.** `s₂(2n) = s₂(n)`. -/
theorem sum_digits_two_mul (n : ℕ) :
    (Nat.digits 2 (2 * n)).sum = (Nat.digits 2 n).sum := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · rw [Nat.digits_base_mul one_lt_two hn]; simp

/-- For `n > 0` the binary digit sum is positive. -/
theorem sum_digits_two_pos {n : ℕ} (hn : 0 < n) : 0 < (Nat.digits 2 n).sum := by
  have hnil : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn.ne'
  exact Nat.sum_pos_iff_exists_pos.mpr
    ⟨_, List.getLast_mem hnil, Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 2 hn.ne')⟩

/-- **Digit sum of a pure power of two is one.** `s₂(2^k) = 1`. -/
theorem sum_digits_two_pow (k : ℕ) : (Nat.digits 2 (2 ^ k)).sum = 1 := by
  rw [show (2 : ℕ) ^ k = 2 ^ k * 1 by ring, Nat.digits_base_pow_mul one_lt_two one_pos]
  simp

/-- **Forward direction:** if `s₂(n) = 1` then `n` is a power of two. -/
theorem sum_digits_two_eq_one_imp (n : ℕ) :
    (Nat.digits 2 n).sum = 1 → ∃ k, n = 2 ^ k := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro h
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | hp
      · simp at h
      · exact hp
    rw [Nat.digits_def' one_lt_two hn, List.sum_cons] at h
    have hhalf : n / 2 < n := Nat.div_lt_self hn one_lt_two
    rcases Nat.even_or_odd n with he | ho
    · have h0 : n % 2 = 0 := Nat.even_iff.mp he
      rw [h0, Nat.zero_add] at h
      obtain ⟨j, hj⟩ := ih (n / 2) hhalf h
      refine ⟨j + 1, ?_⟩
      have he2 : n = 2 * (n / 2) := by omega
      rw [he2, hj]; ring
    · have h1 : n % 2 = 1 := Nat.odd_iff.mp ho
      rw [h1] at h
      have hz : (Nat.digits 2 (n / 2)).sum = 0 := by omega
      have hz2 : n / 2 = 0 := by
        by_contra hne
        have := sum_digits_two_pos (Nat.pos_of_ne_zero hne)
        omega
      exact ⟨0, by rw [pow_zero]; omega⟩

/-- **The binary digit sum equals one exactly for powers of two.**
`s₂(n) = 1 ↔ ∃ k, n = 2^k`. -/
theorem sum_digits_two_eq_one_iff (n : ℕ) :
    (Nat.digits 2 n).sum = 1 ↔ ∃ k, n = 2 ^ k := by
  constructor
  · exact sum_digits_two_eq_one_imp n
  · rintro ⟨k, rfl⟩; exact sum_digits_two_pow k

/-- **The 2-adic valuation of the central binomial coefficient is the binary digit
sum** (parent headline, re-derived to keep this file self-contained):
`v₂(C(2n, n)) = s₂(n)`. -/
theorem padicValNat_two_centralBinom (n : ℕ) :
    padicValNat 2 (Nat.centralBinom n) = (Nat.digits 2 n).sum := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : n ≤ 2 * n := by omega
  have key := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := 2) (k := n) (n := 2 * n) h
  have e1 : (2 : ℕ) * n - n = n := by omega
  rw [e1, sum_digits_two_mul] at key
  rw [Nat.centralBinom_eq_two_mul_choose]
  omega

/-! ### The carry identity -/

/-- **Binary carry identity for adding one.** Incrementing `n` clears its trailing
one-bits (there are `v₂(n+1)` of them) and sets one new bit:

  `s₂(n) + 1 = s₂(n+1) + v₂(n+1)`.

Proved from Legendre's formula `v₂(m!) = m − s₂(m)` applied to `m = n` and `m = n+1`
together with `(n+1)! = (n+1)·n!`. -/
theorem digit_sum_succ_carry (n : ℕ) :
    (Nat.digits 2 n).sum + 1 = (Nat.digits 2 (n + 1)).sum + padicValNat 2 (n + 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- v₂((n+1)!) = v₂(n+1) + v₂(n!)
  have hmul : padicValNat 2 ((n + 1)!) =
      padicValNat 2 (n + 1) + padicValNat 2 (n !) := by
    rw [Nat.factorial_succ]
    exact padicValNat.mul (Nat.succ_ne_zero n) (Nat.factorial_ne_zero n)
  -- Legendre: (2-1)·v₂(m!) = m − s₂(m) for m = n and m = n+1
  have h1 := sub_one_mul_padicValNat_factorial (p := 2) n
  have h2 := sub_one_mul_padicValNat_factorial (p := 2) (n + 1)
  -- digit sums are bounded by the number, so the ℕ subtractions behave
  have hle1 := Nat.digit_sum_le 2 n
  have hle2 := Nat.digit_sum_le 2 (n + 1)
  omega

/-! ### The headline valuation of the Catalan number -/

/-- The Catalan number is nonzero. -/
theorem catalan_ne_zero (n : ℕ) : catalan n ≠ 0 := by
  intro h
  have hrel := succ_mul_catalan_eq_centralBinom n
  rw [h, Nat.mul_zero] at hrel
  exact (Nat.centralBinom_ne_zero n) hrel.symm

/-- **Subtraction-free form of the headline.** `v₂(Cₙ) + 1 = s₂(n+1)`. -/
theorem padicValNat_two_catalan_add_one (n : ℕ) :
    padicValNat 2 (catalan n) + 1 = (Nat.digits 2 (n + 1)).sum := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- v₂(n+1) + v₂(Cₙ) = v₂((n+1)·Cₙ) = v₂(C(2n,n)) = s₂(n)
  have hmul : padicValNat 2 ((n + 1) * catalan n) =
      padicValNat 2 (n + 1) + padicValNat 2 (catalan n) :=
    padicValNat.mul (Nat.succ_ne_zero n) (catalan_ne_zero n)
  rw [succ_mul_catalan_eq_centralBinom, padicValNat_two_centralBinom] at hmul
  -- hmul : s₂(n) = v₂(n+1) + v₂(Cₙ)
  have hcarry := digit_sum_succ_carry n
  omega

/-- **The 2-adic valuation of the Catalan number is the binary digit sum of `n+1`,
minus one:** `v₂(Cₙ) = s₂(n+1) − 1`. -/
theorem padicValNat_two_catalan (n : ℕ) :
    padicValNat 2 (catalan n) = (Nat.digits 2 (n + 1)).sum - 1 := by
  have h := padicValNat_two_catalan_add_one n
  omega

/-! ### Exact power of two dividing `Cₙ` -/

/-- **Exact power dividing `Cₙ` — divisibility half.** `2^{s₂(n+1)−1} ∣ Cₙ`. -/
theorem two_pow_dvd_catalan (n : ℕ) :
    2 ^ ((Nat.digits 2 (n + 1)).sum - 1) ∣ catalan n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← padicValNat_two_catalan]
  exact pow_padicValNat_dvd

/-- **Exact power dividing `Cₙ` — sharpness half.** `¬ 2^{s₂(n+1)} ∣ Cₙ`. -/
theorem not_two_pow_succ_dvd_catalan (n : ℕ) :
    ¬ 2 ^ (Nat.digits 2 (n + 1)).sum ∣ catalan n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := padicValNat_two_catalan_add_one n
  rw [← h]
  exact pow_succ_padicValNat_not_dvd (catalan_ne_zero n)

/-! ### The odd Catalan numbers -/

/-- **Characterisation of the odd Catalan numbers.** `Cₙ` is odd exactly when `n + 1`
is a power of two, i.e. `n = 2^k − 1`:

  `Odd Cₙ ↔ ∃ k, n = 2^k − 1`.

The odd Catalan numbers therefore occur precisely at indices `0, 1, 3, 7, 15, …`. -/
theorem odd_catalan_iff (n : ℕ) :
    Odd (catalan n) ↔ ∃ k, n = 2 ^ k - 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadd := padicValNat_two_catalan_add_one n
  -- Odd Cₙ ↔ v₂(Cₙ) = 0  (for the nonzero `catalan n`)
  have hodd : Odd (catalan n) ↔ padicValNat 2 (catalan n) = 0 := by
    rw [padicValNat.eq_zero_iff, ← Nat.not_even_iff_odd, even_iff_two_dvd]
    constructor
    · intro h; exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · simp at h
      · exact absurd h (catalan_ne_zero n)
      · exact h
  rw [hodd]
  constructor
  · intro hv
    -- v₂(Cₙ) = 0 ⟹ s₂(n+1) = 1 ⟹ n+1 = 2^k
    have hs : (Nat.digits 2 (n + 1)).sum = 1 := by omega
    obtain ⟨k, hk⟩ := (sum_digits_two_eq_one_iff (n + 1)).mp hs
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    have hpos : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) k
    have hn1 : n + 1 = 2 ^ k := by omega
    have hs : (Nat.digits 2 (n + 1)).sum = 1 := by
      rw [hn1]; exact sum_digits_two_pow k
    omega

/-! ### Worked numeric witnesses (0-axiom)

`catalan` is defined by strong recursion, so concrete values come from Mathlib's
`catalan_two` / `catalan_three` and the closed-form characterisation above (kernel
`decide` cannot reduce `catalan`). -/

/-- `C₂ = 2`, an even Catalan number. -/
example : catalan 2 = 2 := catalan_two

/-- `C₃ = 5` is **odd** (`3 = 2² − 1`). -/
example : catalan 3 = 5 := catalan_three
example : Odd (catalan 3) := (odd_catalan_iff 3).mpr ⟨2, by norm_num⟩

/-- `C₇` is **odd** (`7 = 2³ − 1`), the next odd Catalan index after `3`. -/
example : Odd (catalan 7) := (odd_catalan_iff 7).mpr ⟨3, by norm_num⟩

/-- `C₄` is **not** odd: `4 + 1 = 5` is not a power of two. -/
example : ¬ Odd (catalan 4) := by
  rw [odd_catalan_iff]
  rintro ⟨k, hk⟩
  -- `4 = 2^k − 1` forces `2^k = 5`, impossible
  rcases k with _ | _ | _ | k
  · simp at hk
  · simp at hk
  · simp at hk
  · have : 2 ^ 3 ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [pow_succ] at this hk ⊢
    omega

end KummerCatalan
