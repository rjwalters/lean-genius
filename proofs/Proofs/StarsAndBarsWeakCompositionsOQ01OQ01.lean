import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Tactic
import Proofs.StarsAndBarsWeakCompositions
import Proofs.StarsAndBarsWeakCompositionsOQ01
import Proofs.StarsAndBarsWeakCompositionsOQ03

/-
# Generating Function of Positive (Strong) Compositions: ∑ₙ #(positive comps) Xⁿ = Xᵏ/(1−X)ᵏ

## What This Proves

A *positive* (or *strong*) composition of `n` into `k` parts is a function
`g : Fin k → ℕ` with every part `≥ 1` and `∑ᵢ g(i) = n`. The sibling entry
(`StarsAndBarsWeakCompositionsOQ03.lean`) counts them via the explicit `±1`
bijection with *weak* compositions of `n − k` (`positiveCompositionEquivWeak`):
there are `C(n − 1, k − 1)` of them for `0 < k ≤ n`.

The parent entry (`StarsAndBarsWeakCompositionsOQ01.lean`) records the
generating-function incarnation of the *weak* count: over any commutative ring `S`,

  `W k = ∑ₙ #(weak comps of n into k parts) · Xⁿ = (invOneSubPow S k).val = 1/(1 − X)ᵏ`.

This entry records the matching generating function for *positive* compositions:

  `P k = ∑ₙ #(positive comps of n into k parts) · Xⁿ`,    and    `P k = Xᵏ · W k = Xᵏ/(1 − X)ᵏ`.

The factor `Xᵏ` is the algebraic shadow of the bijection "subtract `1` from each of the
`k` parts": it lowers the degree by exactly `k`. Reading off the coefficient of `Xⁿ`
recovers the closed form `C(n − 1, k − 1)` for `0 < k ≤ n`, and `0` when `n < k`
(there is no positive composition of a number smaller than its part count).

## The argument

The defining identity `P k = Xᵏ · W k` holds **for every `k`** (no positivity
hypothesis), coefficientwise:

* `coeff n (Xᵏ · W k) = ite (k ≤ n) (coeff (n − k) (W k)) 0` (Mathlib's `coeff_X_pow_mul'`);
* for `k ≤ n`, `coeff (n − k) (W k) = #(weak comps of n − k) = #(positive comps of n)`
  by `positiveCompositionEquivWeak` (the sibling's `±1` bijection);
* for `n < k`, there are no positive compositions, so both sides vanish.

The `Xᵏ/(1 − X)ᵏ` form and the `· (1 − X)ᵏ = Xᵏ` relation then follow from the parent's
weak-composition identities (which require `0 < k`).

## What Mathlib has — and what this adds

Mathlib has the algebraic series `invOneSubPow` and the multiplication-by-`Xᵏ`
coefficient rule. The sibling entries supply the weak generating function and the
positive-composition count/bijection. Neither records that the ordinary generating
function of the positive-composition *counts* is `Xᵏ/(1 − X)ᵏ`. The new content is that
bridge: `positiveCompositionGenFun_eq` (`P k = Xᵏ · W k`, all `k`) and its corollaries
`positiveCompositionGenFun_eq_X_pow_mul_invOneSubPow`,
`positiveCompositionGenFun_mul_one_sub_pow` (`P k · (1 − X)ᵏ = Xᵏ`) and
`coeff_positiveCompositionGenFun_eq_choose` (the coefficient is `C(n − 1, k − 1)`). The
convolution section adds the semigroup law `P j · P k = P (j + k)` (concatenation of
compositions) and its coefficientwise negative-binomial Vandermonde form. The order section
adds the valuation reading: `Xᵏ ∣ P k`, the coefficients vanish below degree `k`, the
degree-`k` coefficient is `1`, and hence the `X`-adic order of `P k` is exactly `k`
(`order_positiveCompositionGenFun`) — the least number with a positive composition into `k`
parts, realised uniquely by the all-ones tuple.
-/

open PowerSeries

namespace StarsAndBarsGenFun

variable (S : Type*) [CommRing S]

/-- The ordinary generating function of the positive-composition counts:
`P k = ∑ₙ #{g : Fin k → ℕ // (∀ i, 1 ≤ g i) ∧ ∑ i, g i = n} · Xⁿ` in `S⟦X⟧`. -/
noncomputable def positiveCompositionGenFun (k : ℕ) : S⟦X⟧ :=
  mk fun n => (Fintype.card {g : Fin k → ℕ // (∀ i, 1 ≤ g i) ∧ ∑ i, g i = n} : S)

@[simp]
theorem coeff_positiveCompositionGenFun (k n : ℕ) :
    coeff n (positiveCompositionGenFun S k) =
      (Fintype.card {g : Fin k → ℕ // (∀ i, 1 ≤ g i) ∧ ∑ i, g i = n} : S) := by
  rw [positiveCompositionGenFun, coeff_mk]

/-- **Vanishing below the diagonal.** There is no positive composition of `n` into `k`
positive parts when `n < k` (the parts already sum to at least `k`), so the coefficient
of `Xⁿ` in `P k` is `0` for every `n < k`. -/
theorem coeff_positiveCompositionGenFun_of_lt (k n : ℕ) (h : n < k) :
    coeff n (positiveCompositionGenFun S k) = 0 := by
  rw [coeff_positiveCompositionGenFun]
  have hemp : IsEmpty {g : Fin k → ℕ // (∀ i, 1 ≤ g i) ∧ ∑ i, g i = n} := by
    refine ⟨fun g => ?_⟩
    have hlt : n < ∑ i, g.1 i := by
      calc n < k := h
        _ = ∑ _i : Fin k, 1 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
        _ ≤ ∑ i, g.1 i := Finset.sum_le_sum (fun i _ => g.2.1 i)
    exact absurd g.2.2 (by omega)
  haveI := hemp
  rw [Fintype.card_eq_zero, Nat.cast_zero]

/-- **Positive-composition generating function, factored form.** Over any commutative
ring `S` and for *every* `k` (no positivity needed), the ordinary generating function of
the positive-composition counts is `Xᵏ` times the weak-composition generating function:

  `P k = Xᵏ · W k`.

The `Xᵏ` factor is the `±1` bijection's degree shift: a positive composition of `n`
into `k` parts is a weak composition of `n − k`, present only once `k ≤ n`. -/
theorem positiveCompositionGenFun_eq (k : ℕ) :
    positiveCompositionGenFun S k = X ^ k * weakCompositionGenFun S k := by
  ext n
  rw [coeff_positiveCompositionGenFun, coeff_X_pow_mul']
  split_ifs with h
  · -- `k ≤ n`: positive comps of `n` biject with weak comps of `n - k`
    rw [coeff_weakCompositionGenFun]
    congr 1
    exact Fintype.card_congr (StarsAndBars.positiveCompositionEquivWeak k n h)
  · -- `n < k`: no positive composition of `n` into `k` positive parts
    rw [← coeff_positiveCompositionGenFun, coeff_positiveCompositionGenFun_of_lt S k n (by omega)]

/-- **The generating function is `Xᵏ/(1 − X)ᵏ`.** For `0 < k`, the positive-composition
generating function equals `Xᵏ · (invOneSubPow S k).val`, i.e. `Xᵏ/(1 − X)ᵏ`. -/
theorem positiveCompositionGenFun_eq_X_pow_mul_invOneSubPow (k : ℕ) (hk : 0 < k) :
    positiveCompositionGenFun S k = X ^ k * (invOneSubPow S k).val := by
  rw [positiveCompositionGenFun_eq, weakCompositionGenFun_eq_invOneSubPow S k hk]

/-- **The defining relation `P k · (1 − X)ᵏ = Xᵏ`.** Multiplying the positive-composition
generating function by `(1 − X)ᵏ` clears the `1/(1 − X)ᵏ` factor, leaving `Xᵏ`. -/
theorem positiveCompositionGenFun_mul_one_sub_pow (k : ℕ) (hk : 0 < k) :
    positiveCompositionGenFun S k * (1 - X) ^ k = X ^ k := by
  rw [positiveCompositionGenFun_eq, mul_assoc,
    weakCompositionGenFun_mul_one_sub_pow S k hk, mul_one]

/-- The `n`-th coefficient of `Xᵏ/(1 − X)ᵏ` is the number of positive compositions of `n`
into `k` parts — the generating-function reading of the strong stars-and-bars count. -/
theorem coeff_positiveCompositionGenFun_eq_card (k n : ℕ) :
    coeff n (positiveCompositionGenFun S k) =
      (Fintype.card {g : Fin k → ℕ // (∀ i, 1 ≤ g i) ∧ ∑ i, g i = n} : S) :=
  coeff_positiveCompositionGenFun S k n

/-- The same coefficient as the closed form `C(n − 1, k − 1)` for `0 < k ≤ n`, casting the
sibling entry's `card_positiveComposition`. -/
theorem coeff_positiveCompositionGenFun_eq_choose (k n : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    coeff n (positiveCompositionGenFun S k) = ((n - 1).choose (k - 1) : S) := by
  rw [coeff_positiveCompositionGenFun, StarsAndBars.card_positiveComposition k n hk hkn]

/-! ## Convolution: concatenation of compositions

The factored forms `W k = (invOneSubPow S k).val` and `P k = Xᵏ · W k` turn Mathlib's
semigroup law `invOneSubPow_add` into a multiplicative law on the generating functions
themselves. The combinatorial meaning is *concatenation of compositions*: gluing a
(weak or positive) composition into `j` parts onto one into `k` parts produces one into
`j + k` parts, and this is a bijection. The Cauchy product of the series is therefore the
generating function for `j + k` parts.
-/

/-- **Semigroup law for the weak-composition generating function.** For `0 < j` and
`0 < k`, the Cauchy product of the weak series for `j` and `k` parts is the weak series
for `j + k` parts:

  `W j · W k = W (j + k)`.

Immediate from Mathlib's `invOneSubPow_add` once each factor is identified with
`(invOneSubPow S ·).val` (the parent entry's `weakCompositionGenFun_eq_invOneSubPow`). -/
theorem weakCompositionGenFun_mul (j k : ℕ) (hj : 0 < j) (hk : 0 < k) :
    weakCompositionGenFun S j * weakCompositionGenFun S k
      = weakCompositionGenFun S (j + k) := by
  rw [weakCompositionGenFun_eq_invOneSubPow S j hj,
      weakCompositionGenFun_eq_invOneSubPow S k hk,
      weakCompositionGenFun_eq_invOneSubPow S (j + k) (by omega),
      invOneSubPow_add, Units.val_mul]

/-- **Semigroup law for the positive-composition generating function.** For `0 < j` and
`0 < k`,

  `P j · P k = P (j + k)`.

This is the generating-function avatar of *concatenating compositions*: a positive
composition of `a` into `j` parts glued to one of `b` into `k` parts is a positive
composition of `a + b` into `j + k` parts. Algebraically it is the `Xᵏ`-shift of the weak
law: `P j · P k = Xʲ⁺ᵏ · (W j · W k) = Xʲ⁺ᵏ · W (j + k) = P (j + k)`. -/
theorem positiveCompositionGenFun_mul (j k : ℕ) (hj : 0 < j) (hk : 0 < k) :
    positiveCompositionGenFun S j * positiveCompositionGenFun S k
      = positiveCompositionGenFun S (j + k) := by
  rw [positiveCompositionGenFun_eq_X_pow_mul_invOneSubPow S j hj,
      positiveCompositionGenFun_eq_X_pow_mul_invOneSubPow S k hk,
      positiveCompositionGenFun_eq_X_pow_mul_invOneSubPow S (j + k) (by omega),
      invOneSubPow_add, Units.val_mul, pow_add]
  ring

/-- **Coefficient form of the convolution law.** Reading off the coefficient of `Xⁿ` in
`P j · P k = P (j + k)` via the Cauchy product gives a convolution identity on the
positive-composition *counts*: summed over the additive splits `a + b = n`, the product of
the counts for `j` and `k` parts equals the count for `j + k` parts (cast in `S`):

  `∑_{a + b = n} #pos(a, j) · #pos(b, k) = #pos(n, j + k)`.

This is the upper-index (negative-binomial) Vandermonde convolution
`∑_{a} C(a − 1, j − 1) · C(n − a − 1, k − 1) = C(n − 1, j + k − 1)` in combinatorial form;
the count vanishes off the range `j ≤ a ≤ n − k`, so no truncated-subtraction conventions
are needed. -/
theorem card_positiveComposition_convolution (j k n : ℕ) (hj : 0 < j) (hk : 0 < k) :
    (∑ p ∈ Finset.antidiagonal n,
        (Fintype.card {g : Fin j → ℕ // (∀ i, 1 ≤ g i) ∧ ∑ i, g i = p.1} : S)
          * (Fintype.card {g : Fin k → ℕ // (∀ i, 1 ≤ g i) ∧ ∑ i, g i = p.2} : S))
      = (Fintype.card {g : Fin (j + k) → ℕ // (∀ i, 1 ≤ g i) ∧ ∑ i, g i = n} : S) := by
  have hmul := congrArg (coeff (R := S) n) (positiveCompositionGenFun_mul S j k hj hk)
  rw [coeff_mul, coeff_positiveCompositionGenFun] at hmul
  simp_rw [coeff_positiveCompositionGenFun] at hmul
  exact hmul

/-! ## Order (valuation): the series starts exactly at `Xᵏ`

The factored form `P k = Xᵏ · W k`, with `W k` having nonzero constant term
(`coeff 0 (W k) = 1`), pins down the lowest-degree behaviour of `P k`: the series is
divisible by `Xᵏ`, its coefficients vanish below degree `k`, and the coefficient at
degree `k` is `1`. Combinatorially, the smallest number admitting a positive composition
into `k` parts is `k` itself, realised uniquely by the all-ones tuple `(1, …, 1)`. Hence
the formal-power-series order (`X`-adic valuation) of `P k` is exactly `k`.
-/

/-- **`Xᵏ` divides `P k`.** Over any commutative ring and for every `k`, the
positive-composition generating function is divisible by `Xᵏ` — the algebraic shadow of
"every part is `≥ 1`, so the total is `≥ k`." Witnessed by the weak series `W k` via the
factored form `P k = Xᵏ · W k`. -/
theorem X_pow_dvd_positiveCompositionGenFun (k : ℕ) :
    (X : S⟦X⟧) ^ k ∣ positiveCompositionGenFun S k :=
  ⟨weakCompositionGenFun S k, positiveCompositionGenFun_eq S k⟩

/-- **Leading coefficient is `1`.** For `0 < k`, the coefficient of `Xᵏ` in `P k` is `1`:
the only positive composition of `k` into `k` parts is the all-ones tuple `(1, …, 1)`
(`C(k − 1, k − 1) = 1`). -/
theorem coeff_positiveCompositionGenFun_self (k : ℕ) (hk : 0 < k) :
    coeff k (positiveCompositionGenFun S k) = 1 := by
  rw [coeff_positiveCompositionGenFun_eq_choose S k k hk (le_refl k), Nat.choose_self,
    Nat.cast_one]

/-- **The order (X-adic valuation) of `P k` is exactly `k`.** Over a nontrivial commutative
ring and for `0 < k`, the formal-power-series order of the positive-composition generating
function equals `k`: all coefficients below degree `k` vanish
(`coeff_positiveCompositionGenFun_of_lt`) and the degree-`k` coefficient is `1 ≠ 0`
(`coeff_positiveCompositionGenFun_self`). This is the valuation-theoretic statement that
`k` is the least integer with a positive composition into `k` parts. -/
theorem order_positiveCompositionGenFun [Nontrivial S] (k : ℕ) (hk : 0 < k) :
    PowerSeries.order (positiveCompositionGenFun S k) = k := by
  rw [PowerSeries.order_eq_nat]
  refine ⟨?_, fun i hi => coeff_positiveCompositionGenFun_of_lt S k i hi⟩
  rw [coeff_positiveCompositionGenFun_self S k hk]
  exact one_ne_zero

end StarsAndBarsGenFun
