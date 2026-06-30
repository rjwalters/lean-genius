import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic

/-
# Sum of Two Squares: the Full General-n Characterization

## What This Proves

A natural number `n` is a sum of two squares if and only if every prime
`p ≡ 3 (mod 4)` occurs to an *even* power in the factorization of `n`:

  (∃ x y, n = x² + y²)  ↔  ∀ p prime, p % 4 = 3 → Even (padicValNat p n).

This is the complete classification — valid for *all* `n`, prime or composite —
of which natural numbers are representable by the binary quadratic form x² + y².
It subsumes the two special cases already in the gallery:

* the prime case (Fermat): a prime is a sum of two squares iff it is not ≡ 3 (mod 4);
* the congruence obstruction `fermat-two-squares-oq-05`: no `n ≡ 3 (mod 4)` is a
  sum of two squares.

But the general criterion detects obstructions that the single modulus 4 cannot.
The headline witness is `21 = 3 · 7`: it is `≡ 1 (mod 4)`, so the mod-4 test says
nothing, yet `21` is *not* a sum of two squares because the prime `3 ≡ 3 (mod 4)`
divides it to the odd power 1. Squaring repairs every such defect: `441 = 21²`
*is* a sum of two squares (`441 = 21² + 0²`).

## Honest Provenance

The hard analytic content — that this exact biconditional holds — is Mathlib's
`Nat.eq_sq_add_sq_iff` (its proof goes through `-1` being a square modulo the
relevant residues, the multiplicativity of the form, and squarefree descent).
The contribution of this entry is to (a) repackage that result in the cleaner
"for all primes p ≡ 3 (mod 4)" `padicValNat` form, dropping the `primeFactors`
side condition; (b) derive the prime case and the necessity (odd-power
obstruction) corollary; and (c) work the composite examples — in particular the
`21` / `441` pair — that exhibit what the general criterion sees and the mod-4
obstruction misses.

## Status
- [x] Complete proof (0 sorries, 0 axioms)
- [x] Core characterization from Mathlib, repackaged
- [x] Prime case and necessity corollary derived
- [x] Worked composite witnesses, fully verified (no native_decide)
-/

namespace PythagoreanTriplesOQ04OQ01OQ01

open Nat

/-! ## The general characterization

We first restate Mathlib's `Nat.eq_sq_add_sq_iff` quantifying over *all* primes
`p ≡ 3 (mod 4)`, rather than only the prime factors of `n`. The two are
equivalent: a prime that does not divide `n` has `padicValNat p n = 0`, which is
even, so the extra primes impose no condition. -/

/-- **Full general-n characterization.** `n` is a sum of two squares iff every
prime `p ≡ 3 (mod 4)` divides `n` to an even power. -/
theorem sum_two_squares_iff (n : ℕ) :
    (∃ x y : ℕ, n = x ^ 2 + y ^ 2) ↔
      ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (padicValNat p n) := by
  rw [Nat.eq_sq_add_sq_iff]
  constructor
  · intro h p hp hp4
    rcases eq_or_ne n 0 with rfl | hn
    · exact padicValNat.zero.symm ▸ even_zero
    · by_cases hmem : p ∈ n.primeFactors
      · exact h p hmem hp4
      · have hnd : ¬ p ∣ n := fun hd => hmem (Nat.mem_primeFactors.mpr ⟨hp, hd, hn⟩)
        rw [padicValNat.eq_zero_of_not_dvd hnd]
        exact even_zero
  · intro h q hq hq4
    exact h q (Nat.prime_of_mem_primeFactors hq) hq4

/-! ## Necessity: an odd power of a prime ≡ 3 (mod 4) is an obstruction -/

/-- **Necessity (the obstruction).** If some prime `p ≡ 3 (mod 4)` divides `n` to
an odd power, then `n` is not a sum of two squares. This is the half that
detects non-representability; it does not require `n` itself to be `≡ 3 (mod 4)`. -/
theorem not_sum_two_squares_of_odd_padicValNat {n p : ℕ} (hp : p.Prime)
    (hp4 : p % 4 = 3) (hodd : Odd (padicValNat p n)) :
    ¬ ∃ x y : ℕ, n = x ^ 2 + y ^ 2 := by
  intro h
  have he : Even (padicValNat p n) := (sum_two_squares_iff n).mp h p hp hp4
  exact (Nat.even_iff_not_odd.mp he) hodd

/-- **Sufficiency.** If every prime `p ≡ 3 (mod 4)` divides `n` to an even power,
then `n` is a sum of two squares. -/
theorem sum_two_squares_of_forall_even {n : ℕ}
    (h : ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (padicValNat p n)) :
    ∃ x y : ℕ, n = x ^ 2 + y ^ 2 :=
  (sum_two_squares_iff n).mpr h

/-! ## The prime case (Fermat), recovered

For a prime `p`, the only prime factor is `p` itself, with `padicValNat p p = 1`
(odd). So the characterization collapses to: `p` is a sum of two squares iff
`p % 4 ≠ 3`. -/

/-- **Fermat's two-squares theorem.** A prime is a sum of two squares iff it is
not congruent to `3 (mod 4)`. Recovered as the prime specialization of the
general characterization. -/
theorem prime_sum_two_squares_iff {p : ℕ} (hp : p.Prime) :
    (∃ x y : ℕ, p = x ^ 2 + y ^ 2) ↔ p % 4 ≠ 3 := by
  rw [sum_two_squares_iff]
  constructor
  · intro h hp4
    have he : Even (padicValNat p p) := h p hp hp4
    rw [padicValNat.self hp.one_lt] at he
    exact absurd he (by decide)
  · intro hp4 q hq hq4
    have hqp : q ≠ p := by rintro rfl; exact hp4 hq4
    have hnd : ¬ q ∣ p := by rw [Nat.prime_dvd_prime_iff_eq hq hp]; exact hqp
    rw [padicValNat.eq_zero_of_not_dvd hnd]
    exact even_zero

/-- The prime obstruction: a prime `≡ 3 (mod 4)` is not a sum of two squares. -/
theorem prime_not_sum_two_squares {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ¬ ∃ x y : ℕ, p = x ^ 2 + y ^ 2 :=
  fun h => (prime_sum_two_squares_iff hp).mp h hp4

/-! ## Multiplicativity

The sum-of-two-squares property is closed under multiplication (Brahmagupta–
Fibonacci identity), which is exactly why the criterion is multiplicative in `n`.
This is `Nat.sq_add_sq_mul` from Mathlib, restated. -/

/-- Product of two sums of two squares is a sum of two squares. -/
theorem sum_two_squares_mul {a b : ℕ}
    (ha : ∃ x y : ℕ, a = x ^ 2 + y ^ 2) (hb : ∃ u v : ℕ, b = u ^ 2 + v ^ 2) :
    ∃ x y : ℕ, a * b = x ^ 2 + y ^ 2 := by
  obtain ⟨x, y, hxy⟩ := ha
  obtain ⟨u, v, huv⟩ := hb
  obtain ⟨p, q, hpq⟩ := Nat.sq_add_sq_mul hxy huv
  exact ⟨p, q, hpq⟩

/-! ## Worked witnesses

The general criterion sees obstructions invisible to the modulus 4. -/

/-- `padicValNat 3 21 = 1`: the prime `3` divides `21 = 3 · 7` to the first power. -/
theorem padicValNat_three_twentyone : padicValNat 3 21 = 1 := by
  have h21 : (21 : ℕ) = 3 * 7 := by norm_num
  rw [h21, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.self (by norm_num), padicValNat.eq_zero_of_not_dvd (by norm_num)]

/-- **Headline example.** `21` is `≡ 1 (mod 4)`, so the mod-4 obstruction says
nothing, yet `21` is **not** a sum of two squares: the prime `3 ≡ 3 (mod 4)`
divides it to the odd power `1`. -/
theorem twentyone_not_sum_two_squares : ¬ ∃ x y : ℕ, 21 = x ^ 2 + y ^ 2 := by
  refine not_sum_two_squares_of_odd_padicValNat (p := 3) (by norm_num) (by norm_num) ?_
  rw [padicValNat_three_twentyone]
  exact odd_one

/-- `21 ≡ 1 (mod 4)`, confirming the previous obstruction is not a mod-4 effect. -/
theorem twentyone_mod_four : (21 : ℕ) % 4 = 1 := by norm_num

/-- **Repair by squaring.** `441 = 21²` *is* a sum of two squares: every prime
now occurs to an even power, and indeed `441 = 21² + 0²`. -/
theorem fourfortyone_sum_two_squares : ∃ x y : ℕ, 441 = x ^ 2 + y ^ 2 :=
  ⟨21, 0, by norm_num⟩

/-- `9 = 3²` is a sum of two squares (`3` to the even power `2`): `9 = 0² + 3²`. -/
theorem nine_sum_two_squares : ∃ x y : ℕ, 9 = x ^ 2 + y ^ 2 :=
  ⟨0, 3, by norm_num⟩

/-- `45 = 3² · 5` is a sum of two squares: `45 = 6² + 3²`. -/
theorem fortyfive_sum_two_squares : ∃ x y : ℕ, 45 = x ^ 2 + y ^ 2 :=
  ⟨6, 3, by norm_num⟩

/-- `padicValNat 3 147 = 1`: the prime `3` divides `147 = 3 · 49` once. -/
theorem padicValNat_three_onefortyseven : padicValNat 3 147 = 1 := by
  have h : (147 : ℕ) = 3 * 49 := by norm_num
  rw [h, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.self (by norm_num), padicValNat.eq_zero_of_not_dvd (by norm_num)]

/-- `147 = 3 · 7²` is not a sum of two squares: `3` divides it to an odd power. -/
theorem onefortyseven_not_sum_two_squares : ¬ ∃ x y : ℕ, 147 = x ^ 2 + y ^ 2 := by
  refine not_sum_two_squares_of_odd_padicValNat (p := 3) (by norm_num) (by norm_num) ?_
  rw [padicValNat_three_onefortyseven]
  exact odd_one

end PythagoreanTriplesOQ04OQ01OQ01
