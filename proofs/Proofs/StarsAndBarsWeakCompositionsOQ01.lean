import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic
import Proofs.StarsAndBarsWeakCompositions

/-
# Generating-Function View of Weak Compositions: ∑ₙ #(weak comps) Xⁿ = 1/(1−X)ᵏ

## What This Proves

A *weak composition* of `n` into `k` parts is a function `f : Fin k → ℕ` with
`∑ᵢ f(i) = n` (parts may be zero). The parent entry
(`StarsAndBarsWeakCompositions.lean`) counts them combinatorially: there are
`C(n + k − 1, n)` of them (stars and bars).

This entry records the **generating-function** incarnation of that count. Over any
commutative ring `S`, form the ordinary generating function of the sequence
`n ↦ #(weak compositions of n into k parts)`:

  `W k = ∑ₙ #{f : Fin k → ℕ // ∑ i, f i = n} · Xⁿ ∈ S⟦X⟧`.

The headline result is that this is exactly the negative-binomial series, i.e. the
multiplicative inverse of `(1 − X)ᵏ`:

  `W k · (1 − X)ᵏ = 1`,    equivalently    `W k = 1/(1 − X)ᵏ`.

Reading off the coefficient of `Xⁿ` recovers the closed form
`C(n + k − 1, n)` from the parent, now seen as the `n`-th coefficient of `(1−X)⁻ᵏ`.

## The argument

Mathlib provides `PowerSeries.invOneSubPow S k`, the *unit* of `S⟦X⟧` that is the
inverse of `(1 − X)ᵏ`, together with the explicit coefficient formula
`(invOneSubPow S (d+1)).val = mk (n ↦ C(d + n, d))`
(`invOneSubPow_val_succ_eq_mk_add_choose`) and the inverse relation
`(invOneSubPow S k).inv = (1 − X)ᵏ` (`invOneSubPow_inv_eq_one_sub_pow`).

The only content to add is the identification of the *enumerative* generating
function `W k` with this *algebraic* power series. Coefficientwise, for `k = d+1`,

  `coeff n (W k) = #(weak compositions) = C(n + k − 1, n) = C(d + n, d) = coeff n (invOneSubPow)`,

where the middle equality is the parent's `card_weakComposition` and the last is the
binomial symmetry `C(d + n, d) = C(n + d, n)`. Multiplying by `(1 − X)ᵏ` and using the
unit relation gives `W k · (1 − X)ᵏ = 1`.

## What Mathlib has — and what this adds

Mathlib has the algebraic series `invOneSubPow` and its coefficients, and (via the
imported parent) the combinatorial count `card_weakComposition`. It does **not**
record that the ordinary generating function of the weak-composition *counts* is
`1/(1−X)ᵏ`. The new content is precisely that bridge:
`weakCompositionGenFun_eq_invOneSubPow` and its corollaries
`weakCompositionGenFun_mul_one_sub_pow` ( `W k · (1−X)ᵏ = 1` ) and
`coeff_weakCompositionGenFun` (the coefficient is the count).
-/

open PowerSeries

namespace StarsAndBarsGenFun

variable (S : Type*) [CommRing S]

/-- The ordinary generating function of the weak-composition counts:
`W k = ∑ₙ #{f : Fin k → ℕ // ∑ i, f i = n} · Xⁿ` in `S⟦X⟧`. -/
noncomputable def weakCompositionGenFun (k : ℕ) : S⟦X⟧ :=
  mk fun n => (Fintype.card {f : Fin k → ℕ // ∑ i, f i = n} : S)

@[simp]
theorem coeff_weakCompositionGenFun (k n : ℕ) :
    coeff n (weakCompositionGenFun S k) =
      (Fintype.card {f : Fin k → ℕ // ∑ i, f i = n} : S) := by
  rw [weakCompositionGenFun, coeff_mk]

/-- Binomial bookkeeping: the parent's count `C(n + k − 1, n)` for `k = d + 1`
agrees with the coefficient `C(d + n, d)` of `invOneSubPow`. -/
private theorem card_weakComposition_succ (d n : ℕ) :
    Fintype.card {f : Fin (d + 1) → ℕ // ∑ i, f i = n} = Nat.choose (d + n) d := by
  rw [StarsAndBars.card_weakComposition]
  -- goal: (n + (d + 1) - 1).choose n = (d + n).choose d
  have h1 : n + (d + 1) - 1 = d + n := by omega
  rw [h1]
  -- goal: (d + n).choose n = (d + n).choose d
  have hsymm : (d + n).choose ((d + n) - d) = (d + n).choose d :=
    Nat.choose_symm (Nat.le_add_right d n)
  rwa [Nat.add_sub_cancel_left] at hsymm

/-- **Generating function of weak compositions.** Over any commutative ring `S`, the
ordinary generating function of the weak-composition counts equals Mathlib's
`invOneSubPow S k`, the algebraic power series `1/(1 − X)ᵏ`. -/
theorem weakCompositionGenFun_eq_invOneSubPow (k : ℕ) (hk : 0 < k) :
    weakCompositionGenFun S k = (invOneSubPow S k).val := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hk
  -- now k = 0 + d + 1
  rw [Nat.zero_add, invOneSubPow_val_succ_eq_mk_add_choose]
  ext n
  rw [coeff_weakCompositionGenFun, coeff_mk, card_weakComposition_succ]

/-- **The generating function is `1/(1 − X)ᵏ`.** The defining relation of the inverse:
`W k · (1 − X)ᵏ = 1`. Equivalently, `W k = (1 − X)⁻ᵏ` in `S⟦X⟧`. -/
theorem weakCompositionGenFun_mul_one_sub_pow (k : ℕ) (hk : 0 < k) :
    weakCompositionGenFun S k * (1 - X) ^ k = 1 := by
  rw [weakCompositionGenFun_eq_invOneSubPow S k hk,
    ← invOneSubPow_inv_eq_one_sub_pow]
  exact (invOneSubPow S k).val_inv

/-- The `n`-th coefficient of `1/(1 − X)ᵏ` is the number of weak compositions of `n`
into `k` parts — the generating-function reading of stars and bars. -/
theorem coeff_invOneSubPow_eq_card (k n : ℕ) (hk : 0 < k) :
    coeff n (invOneSubPow S k).val =
      (Fintype.card {f : Fin k → ℕ // ∑ i, f i = n} : S) := by
  rw [← weakCompositionGenFun_eq_invOneSubPow S k hk, coeff_weakCompositionGenFun]

/-- The same identification spelled out as the negative-binomial coefficient
`C(n + k − 1, n)`, casting the parent's `card_weakComposition`. -/
theorem coeff_invOneSubPow_eq_choose (k n : ℕ) (hk : 0 < k) :
    coeff n (invOneSubPow S k).val = ((n + k - 1).choose n : S) := by
  rw [coeff_invOneSubPow_eq_card S k n hk, StarsAndBars.card_weakComposition]

end StarsAndBarsGenFun
