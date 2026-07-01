import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic
import Proofs.StarsAndBarsWeakCompositions
import Proofs.StarsAndBarsWeakCompositionsOQ01

/-
# Convolution Law of Weak Compositions: W(k₁)·W(k₂) = W(k₁+k₂) and the negative-binomial Vandermonde identity

## What This Proves

The sibling entry `StarsAndBarsWeakCompositionsOQ01.lean` identifies the ordinary
generating function of the weak-composition counts,

  `W k = ∑ₙ #{f : Fin k → ℕ // ∑ i, f i = n} · Xⁿ ∈ S⟦X⟧`,

with Mathlib's algebraic series `invOneSubPow S k = 1/(1 − X)ᵏ`.

This entry records the **multiplicative structure** of that family. Because
`1/(1 − X)ᵏ` is an exponential in `k`, the generating functions satisfy

  `W(k₁) · W(k₂) = W(k₁ + k₂)`        (`weakCompositionGenFun_mul`)

for **all** `k₁, k₂ ≥ 0`, with the empty case `W(0) = 1`
(`weakCompositionGenFun_zero`) as the unit. Combinatorially this is the
*concatenation* law: gluing a weak composition of `i` into `k₁` parts onto a weak
composition of `j` into `k₂` parts produces a weak composition of `i + j` into
`k₁ + k₂` parts, and every such composition arises uniquely.

Reading off the coefficient of `Xⁿ` in `W(k₁) · W(k₂) = W(k₁ + k₂)` via the
Cauchy product turns the algebraic identity into the **Vandermonde convolution for
negative-binomial coefficients** (`vandermonde_negBinomial`):

  `∑_{i+j=n} C(i + k₁ − 1, i) · C(j + k₂ − 1, j) = C(n + k₁ + k₂ − 1, n)`,

valid for `k₁, k₂ ≥ 1`. This is the "addition formula" dual to the parent's closed
form `C(n + k − 1, n)`: it says the count is multiplicative in the number of parts
at the level of generating functions, exactly as the binomial Vandermonde identity
`∑ C(a,i)·C(b,n−i) = C(a+b,n)` expresses multiplicativity of `(1 + X)ᵏ`.

## The argument

`weakCompositionGenFun_eq_invOneSubPow_val` upgrades OQ01's bridge to **all** `k`
(the `k = 0` case is `W(0) = 1 = (invOneSubPow S 0).val`). Multiplicativity is then
immediate from Mathlib's `invOneSubPow_add : invOneSubPow S (d + e) =
invOneSubPow S d * invOneSubPow S e`, pushing the units multiplication through to
the underlying series. The convolution identity is the `n`-th coefficient of both
sides, extracted with `PowerSeries.coeff_mul` over `S = ℤ` and transported to `ℕ`
by injectivity of the cast.

## What Mathlib has — and what this adds

Mathlib supplies `invOneSubPow_add` (multiplicativity of the algebraic inverse) but
has no notion of weak compositions and no negative-binomial convolution identity.
The new content is the enumerative reading: the concatenation law
`weakCompositionGenFun_mul` for the *counts*, and the explicit binomial convolution
`vandermonde_negBinomial` obtained from it.
-/

open PowerSeries Finset

namespace StarsAndBarsGenFun

variable (S : Type*) [CommRing S]

/-- The empty case: the generating function of weak compositions into `0` parts is
the unit `1`. There is a unique map `Fin 0 → ℕ` (summing to `0`), so the only
nonzero coefficient is the constant term. -/
@[simp]
theorem weakCompositionGenFun_zero : weakCompositionGenFun S 0 = 1 := by
  ext n
  rw [coeff_weakCompositionGenFun, StarsAndBars.card_weakComposition, coeff_one]
  -- goal: ((n + 0 - 1).choose n : S) = if n = 0 then 1 else 0
  rcases n with _ | m
  · simp
  · -- n = m + 1: (m + 1 + 0 - 1).choose (m + 1) = m.choose (m + 1) = 0
    rw [if_neg (Nat.succ_ne_zero m)]
    have : (m + 1 + 0 - 1).choose (m + 1) = 0 := by
      rw [Nat.add_zero, Nat.add_sub_cancel]
      exact Nat.choose_eq_zero_of_lt (Nat.lt_succ_self m)
    rw [this, Nat.cast_zero]

/-- **Bridge for all `k`.** The generating function of the weak-composition counts
equals `(invOneSubPow S k).val = 1/(1 − X)ᵏ`, now including `k = 0`. The positive
case is OQ01's `weakCompositionGenFun_eq_invOneSubPow`. -/
theorem weakCompositionGenFun_eq_invOneSubPow_val (k : ℕ) :
    weakCompositionGenFun S k = (invOneSubPow S k).val := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [weakCompositionGenFun_zero, invOneSubPow_zero, Units.val_one]
  · exact weakCompositionGenFun_eq_invOneSubPow S k hk

/-- **Concatenation / convolution law of weak compositions.** The generating
function is multiplicative in the number of parts:
`W(k₁) · W(k₂) = W(k₁ + k₂)` for all `k₁, k₂ ≥ 0`. This is the generating-function
incarnation of "a weak composition of `i + j` into `k₁ + k₂` parts splits uniquely
into a weak composition of `i` into the first `k₁` parts and one of `j` into the
last `k₂` parts." -/
theorem weakCompositionGenFun_mul (k₁ k₂ : ℕ) :
    weakCompositionGenFun S k₁ * weakCompositionGenFun S k₂
      = weakCompositionGenFun S (k₁ + k₂) := by
  rw [weakCompositionGenFun_eq_invOneSubPow_val, weakCompositionGenFun_eq_invOneSubPow_val,
    weakCompositionGenFun_eq_invOneSubPow_val, invOneSubPow_add, Units.val_mul]

end StarsAndBarsGenFun

/-- **Vandermonde convolution for negative-binomial coefficients.**

`∑_{i+j=n} C(i + k₁ − 1, i) · C(j + k₂ − 1, j) = C(n + k₁ + k₂ − 1, n)`.

For `k₁, k₂ ≥ 1` this is the genuine negative-binomial Vandermonde identity: the
number of weak compositions of `n` into `k₁ + k₂` parts equals the sum over all
splits `n = i + j` of the product of the counts into `k₁` and `k₂` parts. (It also
holds at `k = 0`, where `C(·−1,·)` collapses to the indicator of `0`, matching the
unit `W(0) = 1`.) Proved by extracting the `n`-th coefficient of the algebraic
identity `W(k₁) · W(k₂) = W(k₁ + k₂)` over `ℤ` and transporting to `ℕ`. -/
theorem vandermonde_negBinomial (k₁ k₂ n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n,
        (p.1 + k₁ - 1).choose p.1 * (p.2 + k₂ - 1).choose p.2
      = (n + (k₁ + k₂) - 1).choose n := by
  -- Coefficient `m` of `W k` is the closed-form negative-binomial coefficient.
  have hWcoeff : ∀ (k m : ℕ),
      (PowerSeries.coeff m) (StarsAndBarsGenFun.weakCompositionGenFun ℤ k)
        = ((m + k - 1).choose m : ℤ) := by
    intro k m
    rw [StarsAndBarsGenFun.coeff_weakCompositionGenFun, StarsAndBars.card_weakComposition]
  -- Read off coefficient `n` of `W(k₁) · W(k₂) = W(k₁ + k₂)` over ℤ.
  have hmul := StarsAndBarsGenFun.weakCompositionGenFun_mul ℤ k₁ k₂
  have hcoeff := congrArg (fun φ => (PowerSeries.coeff n) φ) hmul
  simp only [PowerSeries.coeff_mul, hWcoeff] at hcoeff
  -- hcoeff is now the ℤ-cast of the desired ℕ identity; transport down.
  exact_mod_cast hcoeff

/-!
## Additive structure: the Pascal recurrence and hockey-stick partial sum

Where `vandermonde_negBinomial` records the *multiplicative* structure of the
weak-composition counts (the convolution coming from `W(k₁)·W(k₂) = W(k₁+k₂)`), the
counts also satisfy the dual *additive* structure: a single Pascal recurrence and its
telescoped consequence, the hockey-stick partial sum. Both are stated directly about
the combinatorial counts `#{f : Fin k → ℕ // ∑ i, f i = n}` and reduce to the closed
form `C(n + k − 1, n)` of the parent via Pascal's rule on binomial coefficients.
-/

open StarsAndBars in
/-- **Pascal recurrence for weak compositions (last-part classification).**
A weak composition of `n + 1` into `k + 1` parts either has its last part equal to
`0` — in which case the first `k` parts form a weak composition of `n + 1` into `k`
parts — or has a positive last part, which after subtracting `1` becomes a weak
composition of `n` into `k + 1` parts. Hence the counts satisfy

  `#(k+1 parts, total n+1) = #(k parts, total n+1) + #(k+1 parts, total n)`.

This is the negative-binomial form of Pascal's rule
`C(n+k+1, n+1) = C(n+k, n+1) + C(n+k, n)`, and is the additive recurrence underlying
the whole stars-and-bars table. -/
theorem card_weakComposition_recurrence (k n : ℕ) :
    Fintype.card {f : Fin (k + 1) → ℕ // ∑ i, f i = n + 1}
      = Fintype.card {f : Fin k → ℕ // ∑ i, f i = n + 1}
        + Fintype.card {f : Fin (k + 1) → ℕ // ∑ i, f i = n} := by
  rw [card_weakComposition, card_weakComposition, card_weakComposition,
    show n + 1 + (k + 1) - 1 = n + k + 1 by omega,
    show n + 1 + k - 1 = n + k by omega,
    show n + (k + 1) - 1 = n + k by omega, Nat.choose_succ_succ (n + k) n]
  simp only [Nat.succ_eq_add_one]
  omega

open StarsAndBars in
/-- **Hockey-stick partial sum for weak compositions (last-part value).**
Classifying a weak composition of `n` into `k + 1` parts by the value of its last
part (which ranges over `0, 1, …, n`, leaving a weak composition of the complementary
total into the first `k` parts) gives

  `#(k+1 parts, total n) = ∑_{m = 0}^{n} #(k parts, total m)`.

Proved by induction on `n` using the Pascal recurrence
`card_weakComposition_recurrence`. -/
theorem card_weakComposition_partial_sum (k n : ℕ) :
    Fintype.card {f : Fin (k + 1) → ℕ // ∑ i, f i = n}
      = ∑ m ∈ Finset.range (n + 1),
          Fintype.card {f : Fin k → ℕ // ∑ i, f i = m} := by
  induction n with
  | zero =>
    rw [Finset.sum_range_one, card_weakComposition, card_weakComposition,
      Nat.choose_zero_right, Nat.choose_zero_right]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, card_weakComposition_recurrence]
    omega

open StarsAndBars in
/-- **Hockey-stick identity for negative-binomial coefficients.**
The pure-arithmetic reading of `card_weakComposition_partial_sum`, obtained by
substituting the closed form `C(m + k − 1, m)` for each count:

  `∑_{m = 0}^{n} C(m + k − 1, m) = C(n + k, n)`.

This is the negative-binomial analogue of the classical hockey-stick (Christmas
stocking) identity `∑_{m} C(m, r) = C(n+1, r+1)`. -/
theorem negBinomial_hockey_stick (k n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), (m + k - 1).choose m = (n + k).choose n := by
  have h := card_weakComposition_partial_sum k n
  simp only [card_weakComposition] at h
  rw [show n + (k + 1) - 1 = n + k by omega] at h
  exact h.symm
