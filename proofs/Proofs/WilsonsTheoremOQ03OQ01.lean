/-
Legendre's Formula for Multinomial Coefficients & Kummer's Theorem
(Wilson's Theorem OQ-03-OQ-01)

Source: Classical number theory — A.-M. Legendre (1808), E. Kummer (1852).
Status: COMPLETE (0 sorries, 0 axioms)

## Open Question Answered
Parent entry WilsonsTheoremOQ03 ("Legendre's Formula: p-adic Valuation of n!")
poses the open question:

  "Can Legendre's formula be generalized to multinomial coefficients
   n! / (n₁! · n₂! ⋯ n_k!)?"

This file answers YES and, in doing so, formalizes **Kummer's theorem** for
multinomial coefficients: the p-adic valuation counts the base-p carries.

## What This Proves
Let `p` be prime, `s` a finite index set, `f : α → ℕ`, and write
`N = ∑ i ∈ s, f i`. The multinomial coefficient is
`multinomial s f = N! / ∏ i ∈ s, (f i)!`.

- [x] **Additivity of valuation** (the heart of the generalization):
        ν_p(N!) = ν_p(multinomial s f) + ∑ i ∈ s, ν_p((f i)!)
      equivalently  ν_p(multinomial s f) = ν_p(N!) − ∑ i ∈ s, ν_p((f i)!).

- [x] **Legendre / Kummer digit-sum form** (no ℕ-subtraction):
        (p − 1) · ν_p(multinomial s f) + S_p(N) = ∑ i ∈ s, S_p(f i)
      where S_p(m) = (Nat.digits p m).sum is the base-p digit sum.
      Rearranged: (p−1)·ν_p(multinomial) = ∑ S_p(f i) − S_p(N), i.e. the
      valuation counts base-p carries (each carry drops the digit sum by p−1).

- [x] **Kummer's non-divisibility criterion**:
        p ∤ multinomial s f  ↔  ∑ i ∈ s, S_p(f i) = S_p(N)
      (the multinomial is coprime to p exactly when adding the f i in base p
      produces no carries).

- [x] **Two-term (binomial) specialization**:
        (p − 1) · ν_p((a+b)!/(a!·b!)) + S_p(a+b) = S_p(a) + S_p(b)
      — the classical statement of Kummer's theorem for `C(a+b, a)`.

## Mathlib Dependencies
- `Nat.multinomial`, `Nat.multinomial_spec`, `Nat.multinomial_pos`
- `padicValNat.mul`            : ν_p(m·n) = ν_p(m) + ν_p(n)   (m,n ≠ 0)
- `sub_one_mul_padicValNat_factorial` : (p−1)·ν_p(n!) = n − S_p(n)
- `Nat.digit_sum_le`           : S_p(n) ≤ n
- `padicValNat.eq_zero_iff`    : ν_p(n) = 0 ↔ p = 1 ∨ n = 0 ∨ ¬ p ∣ n

Parent proof: WilsonsTheoremOQ03.lean (Legendre for a single factorial).
-/

import Mathlib

namespace WilsonsTheoremMultinomialLegendre

open Nat Finset

variable {α : Type*}

/-! ## Step 1 — `padicValNat` is additive over a product of factorials -/

/-- The p-adic valuation of a finite product of factorials is the sum of the
individual p-adic valuations. (Factorials are always positive, so no
non-vanishing hypotheses are needed.) -/
theorem padicValNat_prod_factorial (p : ℕ) (hp : p.Prime)
    (s : Finset α) (f : α → ℕ) :
    padicValNat p (∏ i ∈ s, (f i)!) = ∑ i ∈ s, padicValNat p ((f i)!) := by
  haveI : Fact p.Prime := ⟨hp⟩
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.prod_cons, Finset.sum_cons,
        padicValNat.mul (Nat.factorial_pos _).ne'
          (Finset.prod_pos (fun i _ => Nat.factorial_pos _)).ne', ih]

/-! ## Step 2 — Additive form of Legendre's formula (avoids ℕ-subtraction) -/

/-- A subtraction-free restatement of Legendre's formula: for a prime `p`,
`(p − 1) · ν_p(m!) + S_p(m) = m`, where `S_p(m) = (p.digits m).sum`.
This follows from `sub_one_mul_padicValNat_factorial` together with the bound
`S_p(m) ≤ m` (`Nat.digit_sum_le`). -/
theorem legendre_add (p m : ℕ) [Fact p.Prime] :
    (p - 1) * padicValNat p (m !) + (p.digits m).sum = m := by
  have h := sub_one_mul_padicValNat_factorial (p := p) m
  have hle := Nat.digit_sum_le p m
  omega

/-! ## Step 3 — Legendre's formula for multinomial coefficients -/

/-- **Multinomial Legendre (additive form).** With `N = ∑ i ∈ s, f i`,
the valuation of `N!` splits as the valuation of the multinomial coefficient
plus the valuations of the individual factorials:
`ν_p(N!) = ν_p(multinomial s f) + ∑ i ∈ s, ν_p((f i)!)`.

Proof: apply `padicValNat` to the defining identity
`(∏ i ∈ s, (f i)!) · multinomial s f = N!` (`Nat.multinomial_spec`) and use
multiplicativity plus Step 1. -/
theorem padicValNat_factorial_sum_eq (p : ℕ) (hp : p.Prime)
    (s : Finset α) (f : α → ℕ) :
    padicValNat p ((∑ i ∈ s, f i)!)
      = padicValNat p (Nat.multinomial s f) + ∑ i ∈ s, padicValNat p ((f i)!) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hspec := Nat.multinomial_spec s f
  have hprod : (0 : ℕ) < ∏ i ∈ s, (f i)! :=
    Finset.prod_pos (fun i _ => Nat.factorial_pos _)
  calc padicValNat p ((∑ i ∈ s, f i)!)
      = padicValNat p ((∏ i ∈ s, (f i)!) * Nat.multinomial s f) := by rw [hspec]
    _ = padicValNat p (∏ i ∈ s, (f i)!) + padicValNat p (Nat.multinomial s f) :=
          padicValNat.mul hprod.ne' (Nat.multinomial_pos s f).ne'
    _ = (∑ i ∈ s, padicValNat p ((f i)!)) + padicValNat p (Nat.multinomial s f) := by
          rw [padicValNat_prod_factorial p hp]
    _ = padicValNat p (Nat.multinomial s f) + ∑ i ∈ s, padicValNat p ((f i)!) := by
          ring

/-- **Multinomial Legendre (subtraction form).** The generalization of
Legendre's formula requested by the open question:
`ν_p(multinomial s f) = ν_p(N!) − ∑ i ∈ s, ν_p((f i)!)`. -/
theorem padicValNat_multinomial (p : ℕ) (hp : p.Prime)
    (s : Finset α) (f : α → ℕ) :
    padicValNat p (Nat.multinomial s f)
      = padicValNat p ((∑ i ∈ s, f i)!) - ∑ i ∈ s, padicValNat p ((f i)!) := by
  have h := padicValNat_factorial_sum_eq p hp s f
  omega

/-! ## Step 4 — Kummer's theorem: the digit-sum form -/

/-- **Kummer's theorem (digit-sum form).** For a prime `p` and `N = ∑ i ∈ s, f i`:
`(p − 1) · ν_p(multinomial s f) + S_p(N) = ∑ i ∈ s, S_p(f i)`.

Equivalently `(p − 1)·ν_p(multinomial) = ∑ S_p(f i) − S_p(N)`: since each base-p
carry when summing the `f i` decreases the total digit sum by exactly `p − 1`,
the valuation equals the number of carries. -/
theorem sub_one_mul_padicValNat_multinomial (p : ℕ) (hp : p.Prime)
    (s : Finset α) (f : α → ℕ) :
    (p - 1) * padicValNat p (Nat.multinomial s f) + (p.digits (∑ i ∈ s, f i)).sum
      = ∑ i ∈ s, (p.digits (f i)).sum := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- Additive valuation identity, scaled by (p-1).
  have hval := padicValNat_factorial_sum_eq p hp s f
  have hIII : (p - 1) * padicValNat p ((∑ i ∈ s, f i)!)
      = (p - 1) * padicValNat p (Nat.multinomial s f)
        + (p - 1) * (∑ i ∈ s, padicValNat p ((f i)!)) := by
    rw [hval, Nat.mul_add]
  -- Legendre (additive) for N and, summed, for each f i.
  have hI := legendre_add p (∑ i ∈ s, f i)
  have hII : (p - 1) * (∑ i ∈ s, padicValNat p ((f i)!))
      + (∑ i ∈ s, (p.digits (f i)).sum) = ∑ i ∈ s, f i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => legendre_add p (f i))
  omega

/-! ## Step 5 — Kummer's non-divisibility criterion -/

/-- **Kummer's criterion.** For a prime `p`, the multinomial coefficient is
coprime to `p` exactly when the base-p digit sums add without loss, i.e. when
summing the `f i` in base `p` produces no carries:
`p ∤ multinomial s f  ↔  ∑ i ∈ s, S_p(f i) = S_p(∑ i ∈ s, f i)`. -/
theorem prime_not_dvd_multinomial_iff (p : ℕ) (hp : p.Prime)
    (s : Finset α) (f : α → ℕ) :
    ¬ p ∣ Nat.multinomial s f
      ↔ (∑ i ∈ s, (p.digits (f i)).sum) = (p.digits (∑ i ∈ s, f i)).sum := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hkummer := sub_one_mul_padicValNat_multinomial p hp s f
  have hp2 := hp.two_le
  -- ¬ p ∣ multinomial ↔ ν_p(multinomial) = 0.
  have hzero : ¬ p ∣ Nat.multinomial s f ↔ padicValNat p (Nat.multinomial s f) = 0 := by
    rw [padicValNat.eq_zero_iff]
    constructor
    · intro h; exact Or.inr (Or.inr h)
    · rintro (h1 | h2 | h3)
      · exact absurd h1 hp.ne_one
      · exact absurd h2 (Nat.multinomial_pos s f).ne'
      · exact h3
  rw [hzero]
  constructor
  · intro h
    have hprod : (p - 1) * padicValNat p (Nat.multinomial s f) = 0 := by rw [h]; ring
    omega
  · intro h
    have hprod : (p - 1) * padicValNat p (Nat.multinomial s f) = 0 := by omega
    rcases Nat.mul_eq_zero.mp hprod with h1 | h2
    · omega
    · exact h2

/-! ## Step 6 — The classical binomial case (Kummer for `C(a+b, a)`) -/

/-- **Kummer's theorem for binomial coefficients.** Specializing the multinomial
identity to two terms `![a, b]` recovers the classical statement: the number of
carries in adding `a` and `b` base `p`,
`(p − 1) · ν_p((a+b)!/(a!·b!)) + S_p(a+b) = S_p(a) + S_p(b)`. -/
theorem sub_one_mul_padicValNat_multinomial_two (p : ℕ) (hp : p.Prime) (a b : ℕ) :
    (p - 1) * padicValNat p (Nat.multinomial Finset.univ ![a, b])
        + (p.digits (a + b)).sum
      = (p.digits a).sum + (p.digits b).sum := by
  have h := sub_one_mul_padicValNat_multinomial p hp (Finset.univ : Finset (Fin 2)) ![a, b]
  simpa [Fin.sum_univ_two] using h

/-! ## Step 7 — Concrete sanity checks -/

/-- `ν₂(C(4,1)) = ν₂(4!/(1!·3!)) = 2`: adding `1 + 3` in base 2 produces two
carries (`01₂ + 11₂ = 100₂`), matching the Kummer count.
Digit sums: `S₂(1) + S₂(3) = 1 + 2 = 3` and `S₂(4) = 1`, so `(2−1)·ν + 1 = 3`. -/
example : (2 - 1) * padicValNat 2 (Nat.multinomial Finset.univ ![1, 3])
      + (Nat.digits 2 (1 + 3)).sum = (Nat.digits 2 1).sum + (Nat.digits 2 3).sum :=
  sub_one_mul_padicValNat_multinomial_two 2 (by norm_num) 1 3

end WilsonsTheoremMultinomialLegendre
