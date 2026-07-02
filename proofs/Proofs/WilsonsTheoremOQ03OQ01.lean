/-
Multinomial Legendre / Kummer Formula: p-adic Valuation of Multinomial Coefficients
(Wilson's Theorem OQ-03-OQ-01)

Source: Generalization of Legendre's formula (1808) and Kummer's theorem (1852).
Status: COMPLETE (0 sorries, 0 axioms)

## Open Question Answered
Parent entry `wilsons-theorem-oq-03` ("Legendre's Formula: p-adic Valuation of n!")
proves the digit-sum form of Legendre's formula for a single factorial:

  (p - 1) · ν_p(n!) = n − S_p(n),   S_p(x) = sum of base-p digits of x.

Its open question asks: *Can Legendre's formula be generalized to multinomial
coefficients* (n; k₁, …, k_m) = n! / (k₁! ⋯ k_m!), with n = k₁ + ⋯ + k_m?

This file proves exactly that. Writing S_p for the base-p digit sum:

  (p - 1) · ν_p( multinomial s f )  +  S_p(∑_{i∈s} f i)  =  ∑_{i∈s} S_p(f i).                (★)

Equivalently, in subtraction form:

  (p - 1) · ν_p( multinomial s f )  =  (∑_{i∈s} S_p(f i)) − S_p(∑_{i∈s} f i).

For a two-element index set this recovers Kummer's theorem (already in Mathlib as
`sub_one_mul_padicValNat_choose_eq_sub_sum_digits`); the content here is the
arbitrary-arity multinomial generalization, which Mathlib does not have.

## Structural consequence
Because the left summand of (★) is a natural number, (★) immediately yields the
subadditivity of the base-p digit sum along the index set:

  S_p(∑_{i∈s} f i)  ≤  ∑_{i∈s} S_p(f i).

## Proof strategy (all-addition, no truncated ℕ subtraction in the core)
1. `padicValNat_prod_factorial`: ν_p distributes over ∏ (f i)!   (Finset induction).
2. `legendre_add`: the additive form of the parent's Legendre lemma,
   (p-1)·ν_p(x!) + S_p(x) = x, obtained from `sub_one_mul_padicValNat_factorial`
   together with `Nat.digit_sum_le`.
3. `multinomial_spec` splits ν_p((∑ f i)!) = ∑ ν_p((f i)!) + ν_p(multinomial),
   and combining the per-index Legendre identities cancels the ∑ f i terms.

## Mathlib Dependencies
- `sub_one_mul_padicValNat_factorial` : (p-1)·ν_p(n!) = n − S_p(n)  (Legendre)
- `Nat.digit_sum_le`                  : S_p(n) ≤ n
- `Nat.multinomial_spec`              : (∏ (f i)!) · multinomial s f = (∑ f i)!
- `Nat.multinomial_pos`               : 0 < multinomial s f
- `padicValNat.mul`                   : ν_p(a·b) = ν_p a + ν_p b   (a,b ≠ 0)

Parent proof: WilsonsTheoremOQ03.lean
-/

import Mathlib

namespace WilsonsTheoremMultinomialLegendre

open Nat Finset

variable {α : Type*}

/-! ## Infrastructure -/

/-- The p-adic valuation distributes over a finite product of factorials.
    (Factorials are always positive, so no nonvanishing hypothesis is needed.) -/
theorem padicValNat_prod_factorial {p : ℕ} [Fact p.Prime] (s : Finset α) (f : α → ℕ) :
    padicValNat p (∏ i ∈ s, (f i)!) = ∑ i ∈ s, padicValNat p (f i)! := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
          padicValNat.mul (Nat.factorial_pos _).ne'
            (Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.factorial_pos _).ne'), ih]

/-- **Legendre's formula, additive form.** For a prime `p`,
    `(p-1)·ν_p(n!) + S_p(n) = n`, where `S_p(n) = (p.digits n).sum`.
    This is the parent's digit-sum Legendre lemma rearranged without ℕ subtraction. -/
theorem legendre_add {p : ℕ} [Fact p.Prime] (n : ℕ) :
    (p - 1) * padicValNat p n ! + (p.digits n).sum = n := by
  have h := sub_one_mul_padicValNat_factorial (p := p) n
  have hle := Nat.digit_sum_le p n
  omega

/-! ## Main theorem: Legendre / Kummer for multinomial coefficients -/

/-- **Multinomial Legendre formula (digit-sum form).**
    For a prime `p`, a finite index set `s`, and any `f : α → ℕ`,

      (p-1)·ν_p( multinomial s f ) + S_p(∑ f) = ∑_i S_p(f i).

    This is the arbitrary-arity generalization of Legendre's formula (single factorial)
    and of Kummer's theorem (binomial coefficient). -/
theorem multinomial_digit_sum {p : ℕ} [Fact p.Prime] (s : Finset α) (f : α → ℕ) :
    (p - 1) * padicValNat p (Nat.multinomial s f) + (p.digits (∑ i ∈ s, f i)).sum
      = ∑ i ∈ s, (p.digits (f i)).sum := by
  classical
  have hprod : (∏ i ∈ s, (f i)!) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.factorial_pos _).ne'
  have hM : Nat.multinomial s f ≠ 0 := (Nat.multinomial_pos s f).ne'
  -- ν_p((∑ f)!) splits as ∑ ν_p((f i)!) + ν_p(multinomial), via multinomial_spec.
  have hval : padicValNat p (∑ i ∈ s, f i)!
      = (∑ i ∈ s, padicValNat p (f i)!) + padicValNat p (Nat.multinomial s f) := by
    have hspec := Nat.multinomial_spec s f
    rw [← hspec, padicValNat.mul hprod hM, padicValNat_prod_factorial]
  -- Legendre (additive) for the total ∑ f.
  have E1 := legendre_add (p := p) (∑ i ∈ s, f i)
  -- Summed per-index Legendre: (p-1)·∑ν_p((f i)!) + ∑ S_p(f i) = ∑ f.
  have E2 : (p - 1) * (∑ i ∈ s, padicValNat p (f i)!) + (∑ i ∈ s, (p.digits (f i)).sum)
      = ∑ i ∈ s, f i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => legendre_add (p := p) (f i)
  -- Scale the valuation split by (p-1).
  have hval' : (p - 1) * padicValNat p (∑ i ∈ s, f i)!
      = (p - 1) * (∑ i ∈ s, padicValNat p (f i)!)
        + (p - 1) * padicValNat p (Nat.multinomial s f) := by
    rw [hval, Nat.mul_add]
  omega

/-- **Multinomial Legendre formula (subtraction form).** -/
theorem multinomial_digit_sum_sub {p : ℕ} [Fact p.Prime] (s : Finset α) (f : α → ℕ) :
    (p - 1) * padicValNat p (Nat.multinomial s f)
      = (∑ i ∈ s, (p.digits (f i)).sum) - (p.digits (∑ i ∈ s, f i)).sum := by
  have h := multinomial_digit_sum (p := p) s f
  omega

/-- **Structural consequence: subadditivity of the base-p digit sum along a Finset.**
    Since the multinomial valuation term in the main identity is a natural number,
    the base-p digit sum of a total is at most the sum of the parts' digit sums. -/
theorem digit_sum_le_sum_digit_sum {p : ℕ} [Fact p.Prime] (s : Finset α) (f : α → ℕ) :
    (p.digits (∑ i ∈ s, f i)).sum ≤ ∑ i ∈ s, (p.digits (f i)).sum := by
  have h := multinomial_digit_sum (p := p) s f
  omega

/-- **Divisibility characterization.** For a prime `p`, the prime `p` divides the
    multinomial coefficient `multinomial s f` iff there is a "carry", i.e. iff the
    digit sum of the total is strictly smaller than the sum of the parts' digit sums.
    (Kummer's divisibility criterion, multinomial form.) -/
theorem prime_dvd_multinomial_iff {p : ℕ} [hp : Fact p.Prime] (s : Finset α) (f : α → ℕ) :
    p ∣ Nat.multinomial s f
      ↔ (p.digits (∑ i ∈ s, f i)).sum < ∑ i ∈ s, (p.digits (f i)).sum := by
  have hp1 : 1 < p := hp.out.one_lt
  have h := multinomial_digit_sum (p := p) s f
  have hM : Nat.multinomial s f ≠ 0 := (Nat.multinomial_pos s f).ne'
  rw [dvd_iff_padicValNat_ne_zero hM]
  -- p ∣ m ↔ ν_p(m) ≠ 0; relate ν_p to the digit-sum gap via the main identity.
  constructor
  · intro hne
    -- ν_p ≠ 0 and p-1 ≥ 1 ⇒ (p-1)·ν_p ≠ 0, so the digit-sum gap is strictly positive.
    have hprod_ne : (p - 1) * padicValNat p (Nat.multinomial s f) ≠ 0 :=
      Nat.mul_ne_zero (by omega) hne
    omega
  · intro hgap h0
    -- ν_p = 0 would force S_p(∑) = ∑ S_p, contradicting the strict gap.
    rw [h0, Nat.mul_zero, Nat.zero_add] at h
    omega

end WilsonsTheoremMultinomialLegendre
