import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.Real.Irrational
import Proofs.PiTranscendental

/-
# Every even zeta value ζ(2n) is irrational — and the odd case ζ(2n+1) is open

## What This Proves

For every `n ≥ 1` the even-argument zeta value

  `ζ(2n) = ∑' k, 1 / k^(2n)`

is **irrational**.  This is the sharp arithmetic contrast to the parent Basel
open question about `ζ(7)` / `ζ(2n+1)`:

  * **Even values** `ζ(2), ζ(4), ζ(6), …` are *all* irrational — proved here.
  * **Odd values** `ζ(5), ζ(7), ζ(9), …` : irrationality is a **genuinely open
    problem**.  Apéry (1979) proved `ζ(3)` irrational (the only individual odd
    value known), and Ball–Rivoal (2001) showed infinitely many `ζ(2n+1)` are
    irrational, but no single `ζ(2n+1)` with `n ≥ 2` is known to be irrational.
    None of this is in Mathlib.

## Why this is `axiomatized`, not `verified`

Euler's formula (`hasSum_zeta_nat`) gives `ζ(2n) = qₙ · π^(2n)` with `qₙ ∈ ℚ`,
so `ζ(2n)` is irrational **iff** `π^(2n)` is.  Irrationality is *not* closed
under powers (`√2` is irrational, its square is not), so `irrational_pi` alone
is insufficient: we genuinely need the **transcendence of π**, and Mathlib does
not (yet) contain a complete Lindemann–Weierstrass development.  This file
therefore routes through the repository's `axiom hermite_lindemann`
(via `Proofs.PiTranscendental.pi_transcendental_over_rationals`).  The single
assumption is exactly that axiom; everything else is machine-checked.

The nonzero-ness of the rational coefficient `qₙ` is obtained *for free* from
positivity of the series (`ζ(2n) > 0`), so no Bernoulli-number vanishing lemma
is needed.

## Approach

  1. `Transcendental ℚ π`  (from `pi_transcendental_over_rationals`, i.e.
     `hermite_lindemann`).
  2. `Transcendental.pow` ⟹ `Transcendental ℚ (π^m)` for `m ≥ 1`, hence
     `Irrational (π^m)` via `Transcendental.irrational`.
  3. `hasSum_zeta_nat` ⟹ `ζ(2n) = ↑qₙ · π^(2n)`; positivity forces `qₙ ≠ 0`;
     `Irrational.ratCast_mul` finishes.
-/

open Real

namespace BaselProblemOQ01OQ02

/-- **Euler's structure theorem for even zeta values — axiom-free.**  Every even zeta value is a
    *nonzero rational* multiple of `π^(2n)`:  `∑' k, 1/k^(2n) = qₙ · π^(2n)` with `qₙ ∈ ℚ∖{0}`.

    This is the axiom-free skeleton beneath the irrationality/transcendence results below: it uses
    only Mathlib's Bernoulli closed form (`hasSum_zeta_nat`) together with strict positivity of the
    series — **no** `hermite_lindemann`.  The single remaining step, from "rational multiple of
    `π^(2n)`" to "irrational", is *exactly* where transcendence of π enters.  So this lemma marks
    the sharp boundary between what is unconditional (the rational-multiple structure) and what
    requires the deep transcendence input (irrationality of the value itself). -/
theorem zeta_even_eq_rat_mul_pi_pow (n : ℕ) (hn : 0 < n) :
    ∃ q : ℚ, q ≠ 0 ∧ (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n)) = (q : ℝ) * π ^ (2 * n) := by
  have hS := hasSum_zeta_nat (k := n) hn.ne'
  obtain ⟨q, hq⟩ :
      ∃ q : ℚ, (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n)) = (q : ℝ) * π ^ (2 * n) := by
    refine ⟨(-1) ^ (n + 1) * 2 ^ (2 * n - 1) * bernoulli (2 * n) / (2 * n).factorial, ?_⟩
    rw [hS.tsum_eq]; push_cast; ring
  -- The series is strictly positive (its k = 1 term is 1), forcing q ≠ 0.
  have hpos : 0 < ∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n) :=
    hS.summable.tsum_pos (fun m => by positivity) 1 (by norm_num)
  have hqne : q ≠ 0 := by
    intro h0; rw [hq, h0] at hpos; simp at hpos
  exact ⟨q, hqne, hq⟩

/-- **Powers of π are irrational** (`m ≥ 1`).

    Mathlib provides `irrational_pi` but nothing about `π^m` for `m ≥ 2`
    (irrationality does not lift through powers).  This follows from the
    *transcendence* of π: if `π^m` were algebraic over ℚ then so would π be
    (compose the witnessing polynomial with `Xᵐ`), contradicting
    `pi_transcendental_over_rationals`.

    **Assumption:** `hermite_lindemann` (Lindemann–Weierstrass), via
    `Proofs.PiTranscendental`. -/
theorem pi_pow_irrational (m : ℕ) (hm : 0 < m) : Irrational (π ^ m) :=
  (pi_transcendental_over_rationals.pow hm).irrational

/-- **Every even zeta value is irrational.**

    For `n ≥ 1`, `ζ(2n) = ∑' k, 1/k^(2n)` is irrational.  Concretely
    `ζ(2) = π²/6`, `ζ(4) = π⁴/90`, `ζ(6) = π⁶/945`, … are all irrational.

    This is the arithmetic counterpoint to the *open* odd case: whether any
    single `ζ(2n+1)` with `n ≥ 2` (e.g. `ζ(7)`) is irrational is unknown.

    **Assumption:** `hermite_lindemann` (transcendence of π). -/
theorem zeta_even_irrational (n : ℕ) (hn : 0 < n) :
    Irrational (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n)) := by
  -- Euler's axiom-free structure: the sum is a nonzero-rational multiple of π^(2n).
  obtain ⟨q, hqne, hq⟩ := zeta_even_eq_rat_mul_pi_pow n hn
  rw [hq]
  -- π^(2n) is irrational; scaling by the nonzero rational q keeps it irrational.
  exact (pi_pow_irrational (2 * n) (by omega)).ratCast_mul hqne

/-- **ζ(2) = ∑' k, 1/k² is irrational** (the classical Basel value). -/
theorem zeta_two_irrational : Irrational (∑' k : ℕ, 1 / (k : ℝ) ^ 2) := by
  have := zeta_even_irrational 1 one_pos
  simpa using this

/-- **ζ(4) = ∑' k, 1/k⁴ is irrational.** -/
theorem zeta_four_irrational : Irrational (∑' k : ℕ, 1 / (k : ℝ) ^ 4) := by
  have := zeta_even_irrational 2 (by norm_num)
  simpa using this

/-- **ζ(6) = ∑' k, 1/k⁶ is irrational.** -/
theorem zeta_six_irrational : Irrational (∑' k : ℕ, 1 / (k : ℝ) ^ 6) := by
  have := zeta_even_irrational 3 (by norm_num)
  simpa using this

/-- **Every even zeta value is transcendental over ℚ** — strictly stronger than
    irrationality.

    Since `ζ(2n) = qₙ · π^(2n)` with `qₙ ∈ ℚ∖{0}` and `π^(2n)` is transcendental
    over ℚ (transcendence of π, `pi_transcendental_over_rationals`, lifted through
    powers by `Transcendental.pow`), scaling by the nonzero rational `qₙ`
    preserves transcendence: an algebraic `qₙ·π^(2n)` would make
    `π^(2n) = qₙ⁻¹·(qₙ·π^(2n))` algebraic, contradicting transcendence of `π^(2n)`.
    Transcendence over ℚ implies irrationality (`Transcendental.irrational`), so
    this refines `zeta_even_irrational`.

    **Assumption:** `hermite_lindemann` (transcendence of π). -/
theorem zeta_even_transcendental (n : ℕ) (hn : 0 < n) :
    Transcendental ℚ (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n)) := by
  -- Euler's axiom-free structure: the sum is a nonzero-rational multiple of π^(2n).
  obtain ⟨q, hqne, hq⟩ := zeta_even_eq_rat_mul_pi_pow n hn
  have hqne' : (q : ℝ) ≠ 0 := by exact_mod_cast hqne
  -- π^(2n) is transcendental over ℚ.
  have hpi : Transcendental ℚ (π ^ (2 * n)) :=
    pi_transcendental_over_rationals.pow (by omega)
  rw [hq]
  -- Transcendence is preserved under scaling by the nonzero rational q:
  -- if q·π^(2n) were algebraic then π^(2n) = q⁻¹·(q·π^(2n)) would be too.
  intro halg
  apply hpi
  have hqinv : IsAlgebraic ℚ ((q⁻¹ : ℚ) : ℝ) := isAlgebraic_algebraMap (q⁻¹ : ℚ)
  have hmul := halg.mul hqinv
  rwa [show (q : ℝ) * π ^ (2 * n) * ((q⁻¹ : ℚ) : ℝ) = π ^ (2 * n) from by
    push_cast; rw [mul_right_comm, mul_inv_cancel₀ hqne', one_mul]] at hmul

/-- **ζ(2) = ∑' k, 1/k² is transcendental over ℚ** (hence irrational). -/
theorem zeta_two_transcendental : Transcendental ℚ (∑' k : ℕ, 1 / (k : ℝ) ^ 2) := by
  have := zeta_even_transcendental 1 one_pos
  simpa using this

/-!
## The open odd case (documentation only)

We deliberately state **no** irrationality theorem for `ζ(2n+1)`: that is the
content of the parent open question and is beyond current mathematics for every
individual value past `ζ(3)`.  The even-case result above is exactly the sharp
boundary that is provable today.
-/

end BaselProblemOQ01OQ02
