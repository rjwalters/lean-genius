/-
# Maclaurin's step via Mathlib symmetric functions — resolving the Newton-identities question

## Open Question (`amgm-inequality-oq-02-oq-03-oq-03-oq-01`)

> Can `maclaurin_step` be proved from
> `Mathlib.RingTheory.MvPolynomial.NewtonIdentities`?

The parent `AmgmInequalityOQ02.lean` records the Maclaurin step
`Mₖ ≥ Mₖ₊₁` (where `Mₖ = (eₖ/C(n,k))^{1/k}`) as an `axiom`, whose stated
proof route is *Newton's log-concavity* `(eₖ/C(n,k))² ≥
(eₖ₋₁/C(n,k-1))·(eₖ₊₁/C(n,k+1))` plus monotonicity of real powers.

## Answer: **No — not from `NewtonIdentities` alone.**

`Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities` proves the
**Newton identities** as *ring equalities* over an arbitrary `CommRing`:

  `mul_esymm_eq_sum`     `k · eₖ = (-1)^{k+1} · Σ (-1)^a · e_a · p_b`
  `psum_eq_mul_esymm_sub_sum`

These relate the elementary symmetric polynomials `eₖ` to the power sums
`pₖ`.  They are **equalities**, valid over *any* commutative ring, and so
they carry **no order information whatsoever**.  Newton's *inequality*
`eₖ² ≥ eₖ₋₁·eₖ₊₁` — the actual engine of `maclaurin_step` — is a
strictly stronger, ℝ-specific *positivity* statement.  It does **not**
follow from the Newton identities; it requires a genuine analytic input,
namely **Cauchy–Schwarz** (equivalently, a sum-of-squares / discriminant
argument).  No amount of the algebraic `eₖ ↔ pₖ` identities can supply
that order content.

Concretely, the de-axiomatisation that *does* exist in this gallery —
`AmgmInequalityOQ02OQ02.lean`'s `newton_log_concavity_proved` and
`maclaurin_step_derived` (both `0`-axiom) — proceeds via Cauchy–Schwarz
and induction, **not** via `NewtonIdentities`.

## What this file contributes (all `0`-axiom, no `sorry`)

This file makes the resolution precise and self-contained, working only
from the parent's public API, by exhibiting the mechanism on the first
step `k = 1`:

* `cauchy_schwarz_engine` — the analytic engine `(Σxᵢ)² ≤ n·Σxᵢ²`,
  obtained from Mathlib's `sq_sum_le_card_mul_sum_sq` (Chebyshev/CS).
  *This* is the ingredient `NewtonIdentities` cannot provide.
* `newton_inequality_k1` — Newton's inequality at `k = 1`,
  `C(n,2)·(Σxᵢ)² ≥ n²·e₂`.  Its proof reduces, via the `k = 2` Newton
  identity `2·e₂ = (Σxᵢ)² − Σxᵢ²` (the relation `NewtonIdentities`
  encodes abstractly), *exactly* to `cauchy_schwarz_engine`.
* `maclaurin_step_one` — the `k = 1` case of the parent's
  `maclaurin_step` **axiom**, proved as a theorem: `M₁ ≥ M₂` for
  non-negative inputs, with no axiom.  The remaining `1/2`-power step is
  pure `Real.sqrt` monotonicity.

The general `k` step needs the *full* log-concavity chain, which the
sibling `AmgmInequalityOQ02OQ02.lean` supplies via Cauchy–Schwarz; this
file documents that the Newton **identities** are not the right tool and
demonstrates the correct one on `k = 1`.

## Status: VERIFIED (0 axioms, 0 sorries)
-/

import Proofs.AmgmInequalityOQ02

open Finset Real

namespace AmgmInequalityOQ02OQ03OQ03OQ01

/-- **The analytic engine.**  Cauchy–Schwarz (the `f = g` case of
Chebyshev's sum inequality, `sq_sum_le_card_mul_sum_sq`): for any real
data `x : Fin n → ℝ`,

  `(∑ᵢ xᵢ)² ≤ n · ∑ᵢ xᵢ²`.

This order-theoretic fact is precisely what `NewtonIdentities` (a family
of ring *equalities*) cannot supply, and it is the real content behind
`maclaurin_step` at `k = 1`. -/
theorem cauchy_schwarz_engine {n : ℕ} (x : Fin n → ℝ) :
    (∑ i, x i) ^ 2 ≤ (n : ℝ) * ∑ i, (x i) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin n))) (f := x)
  simpa [Finset.card_univ, Fintype.card_fin] using h

/-- **Newton's inequality at `k = 1`** (the first Maclaurin step in
cleared-denominator form): `C(n,2)·(∑xᵢ)² ≥ n²·e₂`.

This is the `k = 1` instance of Newton's log-concavity.  Via the `k = 2`
Newton identity `2·e₂ = (∑xᵢ)² − ∑xᵢ²` (the elementary-symmetric ↔
power-sum relation that `MvPolynomial.mul_esymm_eq_sum` encodes), it is
*equivalent* to `cauchy_schwarz_engine`; the parent's
`maclaurin_sq_m1_ge_m2_general` packages exactly that reduction. -/
theorem newton_inequality_k1 {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) :
    (Nat.choose n 2 : ℝ) * (∑ i, x i) ^ 2 ≥ (n : ℝ) ^ 2 * elemSymm 2 x :=
  maclaurin_sq_m1_ge_m2_general hn x

/-- **De-axiomatising the first Maclaurin step.**  The parent records
`maclaurin_step` (`Mₖ ≥ Mₖ₊₁`) as an axiom; here the `k = 1` case is a
theorem with no axioms:

  `M₁ ≥ M₂`,  i.e.  `(∑xᵢ)/n ≥ √(e₂/C(n,2))`,

for non-negative inputs.  The proof is the `newton_inequality_k1`
Cauchy–Schwarz bound followed by `Real.sqrt` monotonicity — no appeal to
Newton's identities, and no axiom. -/
theorem maclaurin_step_one {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    maclaurinMean 1 x ≥ maclaurinMean 2 x := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hC2 : (0 : ℝ) < (Nat.choose n 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : 2 ≤ n)
  have hsum_nonneg : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx i
  -- `M₁ = (∑xᵢ)/n`.
  have hM1 : maclaurinMean 1 x = (∑ i, x i) / (n : ℝ) := by
    unfold maclaurinMean
    rw [elemSymm_one, Nat.choose_one_right, Nat.cast_one, div_one, Real.rpow_one]
  -- `M₂ = √(e₂/C(n,2))`.
  have hM2 : maclaurinMean 2 x = Real.sqrt (elemSymm 2 x / (Nat.choose n 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    unfold maclaurinMean
    norm_num
  rw [hM1, hM2, ge_iff_le]
  -- Write the right side as a square root and compare radicands.
  rw [show (∑ i, x i) / (n : ℝ)
        = Real.sqrt (((∑ i, x i) / (n : ℝ)) ^ 2) from
      (Real.sqrt_sq (div_nonneg hsum_nonneg hn0.le)).symm]
  apply Real.sqrt_le_sqrt
  -- Goal: `e₂/C(n,2) ≤ ((∑xᵢ)/n)²`, i.e. `e₂·n² ≤ (∑xᵢ)²·C(n,2)`.
  rw [div_pow, div_le_div_iff₀ hC2 (by positivity)]
  nlinarith [newton_inequality_k1 hn x]

end AmgmInequalityOQ02OQ03OQ03OQ01
