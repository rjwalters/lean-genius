/-
# Erdős #1138 (OQ-03 · OQ-01): Unconditional sublinearity of prime gaps from Baker–Harman–Pintz

The parent entry `Erdos1138OQ03` establishes a chain of prime-gap results, ending in the
*conditional* statement `cramer_implies_gap_sublinear` (Cramér's heuristic bound
`C·(log x)² = o(x)`), together with the *unconditional* Baker–Harman–Pintz bound recorded
as `axiom baker_harman_pintz`:

    (maxPrimeGap x : ℝ) ≤ (x : ℝ) ^ (0.525 : ℝ)   for x ≥ 25.

This follow-up derives the **unconditional** twin of the conditional sublinearity result:
directly from the BHP bound, the normalised maximal prime gap `maxPrimeGap x / x` tends to `0`.

The argument is a real-analysis squeeze:

  0 ≤ maxPrimeGap x / x ≤ x^0.525 / x = x^(-0.475) → 0.

The upper envelope `x^(-0.475) → 0` is `Real.tendsto_rpow_neg_atTop`, moved from `ℝ` to the
`ℕ`-indexed sequence by `tendsto_natCast_atTop_atTop`. The whole thing is closed by
`squeeze_zero'`, valid eventually (for `x ≥ 25`).

No axioms are added beyond the parent's `baker_harman_pintz`; the entry is `axiomatized`
(it depends on the BHP bound, which is quoted rather than proved).
-/

import Mathlib
import Proofs.Erdos1138OQ03

namespace Erdos1138OQ03

open Filter Topology

/-- For `x ≥ 25`, the normalised maximal prime gap is bounded by `x^(-0.475)`.

    This is the pointwise upper envelope: dividing the BHP bound
    `maxPrimeGap x ≤ x^0.525` by `x` and using `x^0.525 / x = x^(0.525 - 1) = x^(-0.475)`. -/
theorem gap_div_le_rpow_neg (x : ℕ) (hx : 25 ≤ x) :
    (maxPrimeGap x : ℝ) / x ≤ (x : ℝ) ^ (-(0.475 : ℝ)) := by
  have hx_pos : (0 : ℝ) < (x : ℝ) := by
    have : (0 : ℕ) < x := lt_of_lt_of_le (by norm_num) hx
    exact_mod_cast this
  -- x^0.525 / x = x^0.525 / x^1 = x^(0.525 - 1) = x^(-0.475)
  have hdiv : (x : ℝ) ^ (0.525 : ℝ) / x = (x : ℝ) ^ (-(0.475 : ℝ)) := by
    have h1 : (-(0.475 : ℝ)) = (0.525 : ℝ) - 1 := by norm_num
    rw [h1, Real.rpow_sub hx_pos, Real.rpow_one]
  calc (maxPrimeGap x : ℝ) / x
      ≤ (x : ℝ) ^ (0.525 : ℝ) / x := by
        gcongr
        exact baker_harman_pintz x hx
    _ = (x : ℝ) ^ (-(0.475 : ℝ)) := hdiv

/-- **Unconditional sublinearity of prime gaps (BHP).**

    From the Baker–Harman–Pintz bound `maxPrimeGap x ≤ x^0.525`, the normalised maximal
    prime gap `maxPrimeGap x / x` tends to `0` as `x → ∞`. This is the unconditional
    counterpart of the conditional `cramer_implies_gap_sublinear`. -/
theorem bhp_implies_gap_littleo :
    Tendsto (fun x : ℕ => (maxPrimeGap x : ℝ) / x) atTop (𝓝 0) := by
  -- Upper envelope: g(x) = x^(-0.475) tends to 0 (compose ℝ-limit with ℕ-cast).
  have h_env : Tendsto (fun x : ℕ => (x : ℝ) ^ (-(0.475 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.475)).comp
      tendsto_natCast_atTop_atTop
  -- Lower bound: 0 ≤ maxPrimeGap x / x everywhere.
  have h_lo : ∀ x : ℕ, 0 ≤ (maxPrimeGap x : ℝ) / x := fun x =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  -- Upper bound: holds eventually (for x ≥ 25).
  have h_hi : ∀ᶠ x : ℕ in atTop, (maxPrimeGap x : ℝ) / x ≤ (x : ℝ) ^ (-(0.475 : ℝ)) :=
    (eventually_ge_atTop 25).mono fun x hx => gap_div_le_rpow_neg x hx
  -- Squeeze between the constant 0 and the envelope.
  exact squeeze_zero' (Eventually.of_forall h_lo) h_hi h_env

/-- ε-form of unconditional sublinearity: for every `ε > 0`, eventually
    `maxPrimeGap x ≤ ε · x`. -/
theorem bhp_gap_eventually_le_eps (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, (maxPrimeGap x : ℝ) ≤ ε * x := by
  -- From the limit, `maxPrimeGap x / x < ε` eventually; clear the denominator.
  have hev : ∀ᶠ x : ℕ in atTop, (maxPrimeGap x : ℝ) / x < ε :=
    bhp_implies_gap_littleo.eventually (eventually_lt_nhds hε)
  filter_upwards [hev, eventually_ge_atTop 1] with x hxlt hx1
  have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hx1)
  rw [div_lt_iff₀ hx_pos] at hxlt
  exact le_of_lt hxlt

/-- **Sharp-boundary strengthening.** For *every* exponent `θ` strictly above the
    Baker–Harman–Pintz exponent `0.525`, the normalised gap `maxPrimeGap x / x^θ`
    tends to `0`. The sublinearity result `bhp_implies_gap_littleo` is exactly the
    `θ = 1` case, and the threshold is the BHP exponent itself: the family of
    vanishing limits is available precisely for `θ > 0.525`.

    The proof is the same squeeze as `bhp_implies_gap_littleo`, with the envelope
    `x^0.525 / x^θ = x^(0.525 - θ) = x^(-(θ - 0.525)) → 0` (valid since `θ - 0.525 > 0`). -/
theorem bhp_gap_div_rpow_littleo (θ : ℝ) (hθ : (0.525 : ℝ) < θ) :
    Tendsto (fun x : ℕ => (maxPrimeGap x : ℝ) / (x : ℝ) ^ θ) atTop (𝓝 0) := by
  have hy : (0 : ℝ) < θ - 0.525 := by linarith
  -- Envelope: x^(-(θ - 0.525)) → 0 (compose the ℝ-limit with the ℕ-cast).
  have h_env : Tendsto (fun x : ℕ => (x : ℝ) ^ (-(θ - 0.525))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hy).comp tendsto_natCast_atTop_atTop
  -- Lower bound: 0 ≤ maxPrimeGap x / x^θ (the denominator is a nonneg rpow).
  have h_lo : ∀ x : ℕ, 0 ≤ (maxPrimeGap x : ℝ) / (x : ℝ) ^ θ := fun x =>
    div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  -- Upper bound: holds eventually (for x ≥ 25), via the BHP bound.
  have h_hi : ∀ᶠ x : ℕ in atTop,
      (maxPrimeGap x : ℝ) / (x : ℝ) ^ θ ≤ (x : ℝ) ^ (-(θ - 0.525)) := by
    filter_upwards [eventually_ge_atTop 25] with x hx
    have hx_pos : (0 : ℝ) < (x : ℝ) := by
      have : (0 : ℕ) < x := lt_of_lt_of_le (by norm_num) hx
      exact_mod_cast this
    have hdiv : (x : ℝ) ^ (0.525 : ℝ) / (x : ℝ) ^ θ = (x : ℝ) ^ (-(θ - 0.525)) := by
      rw [← Real.rpow_sub hx_pos]
      congr 1
      ring
    calc (maxPrimeGap x : ℝ) / (x : ℝ) ^ θ
        ≤ (x : ℝ) ^ (0.525 : ℝ) / (x : ℝ) ^ θ := by
          gcongr
          exact baker_harman_pintz x hx
      _ = (x : ℝ) ^ (-(θ - 0.525)) := hdiv
  exact squeeze_zero' (Eventually.of_forall h_lo) h_hi h_env

end Erdos1138OQ03
