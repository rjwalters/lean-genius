/-
  Erdős Problem #729 — OQ-04 follow-up: the MULTINOMIAL analogue of Legendre.

  Companion to `Erdos729Problem.lean` and `Erdos729LegendreGeneral.lean`.

  ## The question (OQ-04)

  The parent problem and its OQ-02 general Legendre companion study the base-`p`
  valuation of *binomial* coefficients `n!/(a!b!)` via Legendre's identity
  `v_p(n!) = (n - s_p(n))/(p-1)`. The parent entry lists as an open question:

      Is there an analogue for the *multinomial* coefficients
      `n! / (a₁! ⋯ a_k!)` with `k > 2`?

  There is, and it is the natural generalisation of Kummer's theorem. If
  `N = a₁ + ⋯ + a_k` and `s_p(m) = (p.digits m).sum` is the base-`p` digit sum,
  then for every prime `p`

        (p - 1) · v_p( N! / (a₁!⋯a_k!) )  =  (Σᵢ s_p(aᵢ)) − s_p(N).                (★)

  Equivalently `v_p(multinomial) = (Σᵢ s_p(aᵢ) − s_p(N)) / (p − 1)`, and this
  common value is exactly the number of carries produced when the `aᵢ` are added
  together in base `p` (the multinomial Kummer theorem). The parent's binomial
  bound argument (`v_p(a!) + v_p(b!) ≤ v_p(n!)`) is the two-part special case.

  ## What this file proves (0 axioms / 0 sorries)

  * `padicValNat_prod_factorial` — `v_p` distributes over a finite product of
    factorials (each factor is nonzero, so `padicValNat.mul` applies termwise).
  * `legendre_add` — the subtraction-free additive form of Legendre,
    `(p-1)·v_p(n!) + s_p(n) = n`, obtained from Mathlib's multiplied form
    `sub_one_mul_padicValNat_factorial` plus `Nat.digit_sum_le`.
  * `sub_one_mul_padicValNat_multinomial` — the identity (★) in additive,
    subtraction-free form, over an arbitrary `Finset` index set (any `k`).
  * `padicValNat_multinomial_eq_div` — the classical division form
    `v_p = (Σ s_p(aᵢ) − s_p(N)) / (p−1)`.
  * `sub_one_mul_padicValNat_multinomial_fin` — the same for `k` parts indexed by
    `Fin k`, directly answering the "`k > 2`" phrasing of OQ-04.
  * `prime_dvd_multinomial_iff` — the multinomial Kummer divisibility criterion:
    `p ∣ multinomial ↔ s_p(N) < Σᵢ s_p(aᵢ)` (i.e. adding the `aᵢ` in base `p`
    produces at least one carry).

  Bearer lemmas verified against the Mathlib pin `v4.26.0` (sibling checkout):
  `Nat.multinomial_spec` (Data/Nat/Choose/Multinomial.lean:50),
  `Nat.multinomial_pos` (:46),
  `sub_one_mul_padicValNat_factorial` (Padics/PadicVal/Basic.lean:587),
  `padicValNat.mul` (:402), `dvd_iff_padicValNat_ne_zero` (:220),
  `Nat.digit_sum_le` (Data/Nat/Digits/Defs.lean:432), `Finset.mul_sum`,
  `Finset.sum_add_distrib`, `Finset.prod_ne_zero_iff`, `mul_pos_iff_of_pos_left`,
  `Nat.mul_div_cancel_left`.
-/

import Mathlib

namespace Erdos729Multinomial

open Nat Finset

/-- `p`-adic valuation distributes over a finite product of factorials.
Each factorial is nonzero, so `padicValNat.mul` applies at every step. -/
theorem padicValNat_prod_factorial {α : Type*} (p : ℕ) [Fact p.Prime]
    (s : Finset α) (f : α → ℕ) :
    padicValNat p (∏ i ∈ s, (f i)!) = ∑ i ∈ s, padicValNat p ((f i)!) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have hprod : (∏ i ∈ s, (f i)!) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValNat.mul (Nat.factorial_ne_zero _) hprod, ih]

/-- **Additive (subtraction-free) form of Legendre's identity.**
For a prime `p`, `(p-1)·v_p(n!) + s_p(n) = n`, where `s_p(n) = (p.digits n).sum`.
Derived from Mathlib's `sub_one_mul_padicValNat_factorial` together with the
bound `Nat.digit_sum_le`. -/
theorem legendre_add (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (p - 1) * padicValNat p (n !) + (p.digits n).sum = n := by
  have h := sub_one_mul_padicValNat_factorial (p := p) n
  have hle : (p.digits n).sum ≤ n := Nat.digit_sum_le p n
  omega

/-- **The multinomial Legendre/Kummer identity (★), additive form.**

For any prime `p`, any finite index set `s`, and any parts `f : α → ℕ`,

    (p - 1) · v_p(multinomial s f) + s_p(Σᵢ f i)  =  Σᵢ s_p(f i),

with `s_p(m) = (p.digits m).sum`. This is the exact analogue, for `k = |s|`
parts, of the classical binomial statement, and holds with no subtraction. -/
theorem sub_one_mul_padicValNat_multinomial {α : Type*} (p : ℕ) [Fact p.Prime]
    (s : Finset α) (f : α → ℕ) :
    (p - 1) * padicValNat p (Nat.multinomial s f)
        + (p.digits (∑ i ∈ s, f i)).sum
      = ∑ i ∈ s, (p.digits (f i)).sum := by
  -- v_p of the multinomial in terms of v_p of the factorials, via `multinomial_spec`.
  have hne : (∏ i ∈ s, (f i)!) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _
  have hM : Nat.multinomial s f ≠ 0 := (Nat.multinomial_pos s f).ne'
  have hB : padicValNat p ((∑ i ∈ s, f i)!)
      = (∑ i ∈ s, padicValNat p ((f i)!)) + padicValNat p (Nat.multinomial s f) := by
    calc padicValNat p ((∑ i ∈ s, f i)!)
        = padicValNat p ((∏ i ∈ s, (f i)!) * Nat.multinomial s f) := by
          rw [Nat.multinomial_spec]
      _ = padicValNat p (∏ i ∈ s, (f i)!) + padicValNat p (Nat.multinomial s f) :=
          padicValNat.mul hne hM
      _ = (∑ i ∈ s, padicValNat p ((f i)!)) + padicValNat p (Nat.multinomial s f) := by
          rw [padicValNat_prod_factorial]
  -- Summing the additive Legendre identity over the parts.
  have hC : (p - 1) * (∑ i ∈ s, padicValNat p ((f i)!))
        + (∑ i ∈ s, (p.digits (f i)).sum) = ∑ i ∈ s, f i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => legendre_add p (f i)
  -- Additive Legendre for the total `N = Σᵢ f i`, expanded through `hB`.
  have hAN := legendre_add p (∑ i ∈ s, f i)
  rw [hB, Nat.mul_add] at hAN
  omega

/-- **The multinomial Legendre identity, classical division form.**

`v_p(multinomial s f) = (Σᵢ s_p(f i) − s_p(Σᵢ f i)) / (p − 1)`. -/
theorem padicValNat_multinomial_eq_div {α : Type*} (p : ℕ) [Fact p.Prime]
    (s : Finset α) (f : α → ℕ) :
    padicValNat p (Nat.multinomial s f)
      = ((∑ i ∈ s, (p.digits (f i)).sum) - (p.digits (∑ i ∈ s, f i)).sum) / (p - 1) := by
  have hp1 : 0 < p - 1 := by have := (Fact.out : p.Prime).two_le; omega
  have hmain := sub_one_mul_padicValNat_multinomial p s f
  have hstep : (p - 1) * padicValNat p (Nat.multinomial s f)
      = (∑ i ∈ s, (p.digits (f i)).sum) - (p.digits (∑ i ∈ s, f i)).sum := by omega
  rw [← hstep, Nat.mul_div_cancel_left _ hp1]

/-- **OQ-04, `k`-part form.** The multinomial Legendre/Kummer identity for `k`
parts indexed by `Fin k` — the literal "`n!/(a₁!⋯a_k!)` with `k > 2`" analogue. -/
theorem sub_one_mul_padicValNat_multinomial_fin (p : ℕ) [Fact p.Prime]
    (k : ℕ) (a : Fin k → ℕ) :
    (p - 1) * padicValNat p (Nat.multinomial Finset.univ a)
        + (p.digits (∑ i, a i)).sum
      = ∑ i, (p.digits (a i)).sum :=
  sub_one_mul_padicValNat_multinomial p Finset.univ a

/-- **Multinomial Kummer divisibility criterion.** A prime `p` divides the
multinomial coefficient `multinomial s f` iff the base-`p` digit sum of the total
is strictly smaller than the sum of the digit sums of the parts — equivalently,
iff adding the parts in base `p` produces at least one carry. -/
theorem prime_dvd_multinomial_iff {α : Type*} (p : ℕ) [Fact p.Prime]
    (s : Finset α) (f : α → ℕ) :
    p ∣ Nat.multinomial s f
      ↔ (p.digits (∑ i ∈ s, f i)).sum < ∑ i ∈ s, (p.digits (f i)).sum := by
  have hM : Nat.multinomial s f ≠ 0 := (Nat.multinomial_pos s f).ne'
  have hq : 0 < p - 1 := by have := (Fact.out : p.Prime).two_le; omega
  have hmain := sub_one_mul_padicValNat_multinomial p s f
  rw [dvd_iff_padicValNat_ne_zero hM, ← Nat.pos_iff_ne_zero,
    ← mul_pos_iff_of_pos_left hq]
  omega

/-- **Kummer's identity for binomial coefficients (★), additive form.**

The classical two-part specialisation, stated directly on `Nat.choose`: for any prime
`p` and any `m, n`,

    (p - 1) · v_p( C(m+n, n) ) + s_p(m + n)  =  s_p(m) + s_p(n),

with `s_p(k) = (p.digits k).sum`.  Equivalently `(p-1)·v_p(C(m+n,n)) = s_p(m)+s_p(n)-s_p(m+n)`,
the exact number of base-`p` carries in `m + n` scaled by `p - 1`.  This is the
`Nat.choose` form of the general-`p` Kummer theorem (the `p = 2` case is
`Erdos729DigitSum.excess_eq_v2_choose`), proved by applying the additive Legendre
identity `legendre_add` to the three factorials in `(m+n)! = C(m+n,n) · n! · m!`. -/
theorem sub_one_mul_padicValNat_choose (p : ℕ) [Fact p.Prime] (m n : ℕ) :
    (p - 1) * padicValNat p ((m + n).choose n) + (p.digits (m + n)).sum
      = (p.digits m).sum + (p.digits n).sum := by
  -- `(m+n).choose n · n! · m! = (m+n)!`
  have hfact : (m + n).choose n * n ! * m ! = (m + n)! := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left n m)
    simpa [Nat.add_sub_cancel] using h
  have hCne : (m + n).choose n ≠ 0 := (Nat.choose_pos (Nat.le_add_left n m)).ne'
  -- `v_p((m+n)!) = v_p(C) + v_p(n!) + v_p(m!)`
  have hval : padicValNat p ((m + n)!)
      = padicValNat p ((m + n).choose n) + padicValNat p (n !)
          + padicValNat p (m !) := by
    rw [← hfact,
      padicValNat.mul (mul_ne_zero hCne (Nat.factorial_ne_zero n)) (Nat.factorial_ne_zero m),
      padicValNat.mul hCne (Nat.factorial_ne_zero n)]
  -- distribute `(p-1)·(·)` over the three-term sum
  have hexp : (p - 1) * padicValNat p ((m + n)!)
      = (p - 1) * padicValNat p ((m + n).choose n)
          + (p - 1) * padicValNat p (n !) + (p - 1) * padicValNat p (m !) := by
    rw [hval, Nat.mul_add, Nat.mul_add]
  have hN := legendre_add p (m + n)
  have hm := legendre_add p m
  have hn := legendre_add p n
  omega

/-- **Kummer's carry criterion for binomial coefficients.** A prime `p` divides
`C(m+n, n)` iff the base-`p` digit sum of `m + n` is strictly smaller than the sum of
the digit sums of `m` and `n` — equivalently, iff adding `m` and `n` in base `p`
produces at least one carry.  The `Nat.choose` specialisation of
`prime_dvd_multinomial_iff`. -/
theorem prime_dvd_choose_iff (p : ℕ) [Fact p.Prime] (m n : ℕ) :
    p ∣ (m + n).choose n
      ↔ (p.digits (m + n)).sum < (p.digits m).sum + (p.digits n).sum := by
  have hCne : (m + n).choose n ≠ 0 := (Nat.choose_pos (Nat.le_add_left n m)).ne'
  have hq : 0 < p - 1 := by have := (Fact.out : p.Prime).two_le; omega
  have hmain := sub_one_mul_padicValNat_choose p m n
  rw [dvd_iff_padicValNat_ne_zero hCne, ← Nat.pos_iff_ne_zero,
    ← mul_pos_iff_of_pos_left hq]
  omega

end Erdos729Multinomial
