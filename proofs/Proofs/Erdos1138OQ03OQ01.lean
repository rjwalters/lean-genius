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

open Filter Topology Asymptotics

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

/-- **BHP bound as a big-O statement.** The maximal prime gap is `O(x^0.525)`,
    the Baker–Harman–Pintz bound packaged in Mathlib's asymptotics idiom.

    This is a strengthening of `bhp_implies_gap_littleo`, which only records the
    corollary at exponent `1` (sublinearity); here the actual BHP exponent `0.525`
    is retained. -/
theorem gap_isBigO_rpow :
    (fun x : ℕ => (maxPrimeGap x : ℝ)) =O[atTop] (fun x : ℕ => (x : ℝ) ^ (0.525 : ℝ)) := by
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop 25] with x hx
  have hnn : (0 : ℝ) ≤ (x : ℝ) ^ (0.525 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg x) _
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (maxPrimeGap x)), abs_of_nonneg hnn]
  exact baker_harman_pintz x hx

/-- **Generalised sublinearity.** For every exponent `a > 0.525`, the normalised gap
    `maxPrimeGap x / x^a` tends to `0`. This uses the full strength of the BHP exponent:
    `bhp_implies_gap_littleo` is the `a = 1` case, but sublinearity in fact holds for any
    exponent strictly above `0.525` — the envelope `x^(0.525 - a)` vanishes as soon as
    `0.525 - a < 0`. -/
theorem bhp_gap_div_rpow_littleo (a : ℝ) (ha : (0.525 : ℝ) < a) :
    Tendsto (fun x : ℕ => (maxPrimeGap x : ℝ) / (x : ℝ) ^ a) atTop (𝓝 0) := by
  have hpos : 0 < a - 0.525 := by linarith
  -- Envelope: x^(-(a - 0.525)) → 0.
  have h_env : Tendsto (fun x : ℕ => (x : ℝ) ^ (-(a - 0.525))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hpos).comp tendsto_natCast_atTop_atTop
  -- Lower bound: the ratio is nonnegative everywhere.
  have h_lo : ∀ x : ℕ, 0 ≤ (maxPrimeGap x : ℝ) / (x : ℝ) ^ a := fun x =>
    div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  -- Upper bound: holds eventually (for x ≥ 25).
  have h_hi : ∀ᶠ x : ℕ in atTop,
      (maxPrimeGap x : ℝ) / (x : ℝ) ^ a ≤ (x : ℝ) ^ (-(a - 0.525)) := by
    filter_upwards [eventually_ge_atTop 25] with x hx
    have hx_pos : (0 : ℝ) < (x : ℝ) := by
      have : (0 : ℕ) < x := lt_of_lt_of_le (by norm_num) hx
      exact_mod_cast this
    -- x^0.525 / x^a = x^(0.525 - a) = x^(-(a - 0.525))
    have hdiv : (x : ℝ) ^ (0.525 : ℝ) / (x : ℝ) ^ a = (x : ℝ) ^ (-(a - 0.525)) := by
      rw [← Real.rpow_sub hx_pos]; congr 1; ring
    calc (maxPrimeGap x : ℝ) / (x : ℝ) ^ a
        ≤ (x : ℝ) ^ (0.525 : ℝ) / (x : ℝ) ^ a := by
          gcongr
          exact baker_harman_pintz x hx
      _ = (x : ℝ) ^ (-(a - 0.525)) := hdiv
  exact squeeze_zero' (Eventually.of_forall h_lo) h_hi h_env

/-- **Sublinearity in the little-o idiom.** The maximal prime gap is `o(x)`.

    This is the asymptotics-idiom repackaging of `bhp_implies_gap_littleo`: the entry's
    title claim ("sublinearity") is exactly the statement `maxPrimeGap =o[atTop] id`, which
    `bhp_implies_gap_littleo` records only as a `Tendsto (·/x) → 0`. The two are equivalent
    via `isLittleO_iff_tendsto'` (the denominator `x` is eventually nonzero). -/
theorem bhp_gap_isLittleO_id :
    (fun x : ℕ => (maxPrimeGap x : ℝ)) =o[atTop] (fun x : ℕ => (x : ℝ)) := by
  refine (isLittleO_iff_tendsto' ?_).mpr bhp_implies_gap_littleo
  filter_upwards [eventually_ge_atTop 1] with x hx h0
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hx
  rw [h0] at hxpos
  exact absurd hxpos (lt_irrefl 0)

/-- **Sharp little-o at every exponent above `0.525`.** For any `a > 0.525`,
    `maxPrimeGap =o[atTop] (x ↦ x^a)`. This is the little-o idiom form of
    `bhp_gap_div_rpow_littleo`, using the full BHP exponent: sublinearity holds not just at
    `a = 1` (`bhp_gap_isLittleO_id`) but for every exponent strictly above the BHP threshold. -/
theorem bhp_gap_isLittleO_rpow (a : ℝ) (ha : (0.525 : ℝ) < a) :
    (fun x : ℕ => (maxPrimeGap x : ℝ)) =o[atTop] (fun x : ℕ => (x : ℝ) ^ a) := by
  refine (isLittleO_iff_tendsto' ?_).mpr (bhp_gap_div_rpow_littleo a ha)
  filter_upwards [eventually_ge_atTop 1] with x hx h0
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hx
  have hrp : (0 : ℝ) < (x : ℝ) ^ a := Real.rpow_pos_of_pos hxpos a
  rw [h0] at hrp
  exact absurd hrp (lt_irrefl 0)

/-- **Effective (pointwise) sublinearity.** A concrete sufficient condition replacing the
    qualitative "eventually" of `bhp_gap_eventually_le_eps`: once `x ≥ 25` and
    the explicit threshold `1 ≤ ε · x^0.475` holds, we already have `maxPrimeGap x ≤ ε · x`.

    The threshold `1 ≤ ε · x^0.475` is exactly `x^(-0.475) ≤ ε`, i.e. the point at which the
    envelope `maxPrimeGap x / x ≤ x^(-0.475)` has dropped below `ε`; it holds for all
    sufficiently large `x` (since `x^0.475 → ∞`), recovering `bhp_gap_eventually_le_eps`.
    (Positivity of `ε` is not assumed — it is forced by the threshold, as `x^0.475 > 0`.) -/
theorem bhp_gap_le_eps_effective (ε : ℝ) (x : ℕ)
    (hx25 : 25 ≤ x) (hthr : 1 ≤ ε * (x : ℝ) ^ (0.475 : ℝ)) :
    (maxPrimeGap x : ℝ) ≤ ε * x := by
  have hx_pos : (0 : ℝ) < (x : ℝ) := by
    have : (0 : ℕ) < x := lt_of_lt_of_le (by norm_num) hx25
    exact_mod_cast this
  have hxneg_pos : (0 : ℝ) < (x : ℝ) ^ (-(0.475 : ℝ)) := Real.rpow_pos_of_pos hx_pos _
  -- x^(-0.475) · x^0.475 = x^0 = 1, so multiplying the threshold by x^(-0.475) gives the bound.
  have hmul : (x : ℝ) ^ (-(0.475 : ℝ)) * (x : ℝ) ^ (0.475 : ℝ) = 1 := by
    rw [← Real.rpow_add hx_pos]; norm_num
  have hneg : (x : ℝ) ^ (-(0.475 : ℝ)) ≤ ε := by
    calc (x : ℝ) ^ (-(0.475 : ℝ))
        = (x : ℝ) ^ (-(0.475 : ℝ)) * 1 := by ring
      _ ≤ (x : ℝ) ^ (-(0.475 : ℝ)) * (ε * (x : ℝ) ^ (0.475 : ℝ)) :=
          mul_le_mul_of_nonneg_left hthr (le_of_lt hxneg_pos)
      _ = ε * ((x : ℝ) ^ (-(0.475 : ℝ)) * (x : ℝ) ^ (0.475 : ℝ)) := by ring
      _ = ε := by rw [hmul]; ring
  have hfinal : (maxPrimeGap x : ℝ) / x ≤ ε := le_trans (gap_div_le_rpow_neg x hx25) hneg
  rwa [div_le_iff₀ hx_pos] at hfinal

/-- **Abstract sublinearity engine.** The specific Baker–Harman–Pintz exponent `0.525` plays no
role in the sublinearity conclusion: *any* eventual power envelope `maxPrimeGap x ≤ x^θ` with a
sub-linear exponent `θ < 1` already forces the normalised gap `maxPrimeGap x / x → 0`. The envelope
`x^θ / x = x^(θ - 1) = x^(-(1 - θ))` vanishes because `1 - θ > 0`.

This isolates the mathematical content of `bhp_implies_gap_littleo` — which is the instance
`θ = 0.525` — from the arithmetic input. Any future strengthening of the BHP bound (to `0.5 + ε`,
or a conjectural `θ → 1/2`) plugs straight into this engine without re-running the real-analysis
squeeze. The hypothesis is stated in `atTop`-eventual form, so it also subsumes bounds that hold
only past an unspecified threshold. -/
theorem gap_littleo_of_rpow_bound {θ : ℝ} (hθ : θ < 1)
    (H : ∀ᶠ x : ℕ in atTop, (maxPrimeGap x : ℝ) ≤ (x : ℝ) ^ θ) :
    Tendsto (fun x : ℕ => (maxPrimeGap x : ℝ) / x) atTop (𝓝 0) := by
  have hpos : 0 < 1 - θ := by linarith
  -- Envelope: x^(θ - 1) = x^(-(1 - θ)) → 0 (compose the ℝ-limit with the ℕ-cast).
  have h_env : Tendsto (fun x : ℕ => (x : ℝ) ^ (-(1 - θ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hpos).comp tendsto_natCast_atTop_atTop
  have h_lo : ∀ x : ℕ, 0 ≤ (maxPrimeGap x : ℝ) / x := fun x =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  -- Upper bound: divide the envelope hypothesis by `x` (valid once `x ≥ 1`).
  have h_hi : ∀ᶠ x : ℕ in atTop, (maxPrimeGap x : ℝ) / x ≤ (x : ℝ) ^ (-(1 - θ)) := by
    filter_upwards [H, eventually_ge_atTop 1] with x hx hx1
    have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hx1)
    have hdiv : (x : ℝ) ^ θ / x = (x : ℝ) ^ (-(1 - θ)) := by
      rw [show (-(1 - θ)) = θ - 1 by ring, Real.rpow_sub hx_pos, Real.rpow_one]
    calc (maxPrimeGap x : ℝ) / x
        ≤ (x : ℝ) ^ θ / x := by gcongr <;> exact hx
      _ = (x : ℝ) ^ (-(1 - θ)) := hdiv
  exact squeeze_zero' (Eventually.of_forall h_lo) h_hi h_env

/-- **Two-parameter master engine.** Both exponents are free: from *any* eventual power
envelope `maxPrimeGap x ≤ x^θ` and *any* target exponent `a` strictly above the source `θ`,
the normalised gap `maxPrimeGap x / x^a → 0`. The envelope `x^θ / x^a = x^(-(a - θ))` vanishes
because `a - θ > 0`.

This is the common generalisation of the two one-parameter engines in this file:
`gap_littleo_of_rpow_bound` is the target-fixed instance `a = 1` (with `hθa : θ < 1`), while
`bhp_gap_div_rpow_littleo` is the source-fixed instance `θ = 0.525` (with the BHP envelope
supplied by `baker_harman_pintz`). Decoupling source from target isolates the sole arithmetic
content — the strict gap `θ < a` between "how big the gaps provably are" and "what we divide by"
— from every particular pair of exponents. -/
theorem gap_div_rpow_littleo_of_rpow_bound {θ a : ℝ} (hθa : θ < a)
    (H : ∀ᶠ x : ℕ in atTop, (maxPrimeGap x : ℝ) ≤ (x : ℝ) ^ θ) :
    Tendsto (fun x : ℕ => (maxPrimeGap x : ℝ) / (x : ℝ) ^ a) atTop (𝓝 0) := by
  have hpos : 0 < a - θ := by linarith
  -- Envelope: x^(θ - a) = x^(-(a - θ)) → 0 (compose the ℝ-limit with the ℕ-cast).
  have h_env : Tendsto (fun x : ℕ => (x : ℝ) ^ (-(a - θ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hpos).comp tendsto_natCast_atTop_atTop
  have h_lo : ∀ x : ℕ, 0 ≤ (maxPrimeGap x : ℝ) / (x : ℝ) ^ a := fun x =>
    div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  -- Upper bound: divide the envelope hypothesis by `x^a` (valid once `x ≥ 1`).
  have h_hi : ∀ᶠ x : ℕ in atTop,
      (maxPrimeGap x : ℝ) / (x : ℝ) ^ a ≤ (x : ℝ) ^ (-(a - θ)) := by
    filter_upwards [H, eventually_ge_atTop 1] with x hx hx1
    have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hx1)
    have hdiv : (x : ℝ) ^ θ / (x : ℝ) ^ a = (x : ℝ) ^ (-(a - θ)) := by
      rw [← Real.rpow_sub hx_pos]; congr 1; ring
    calc (maxPrimeGap x : ℝ) / (x : ℝ) ^ a
        ≤ (x : ℝ) ^ θ / (x : ℝ) ^ a := by gcongr <;> exact hx
      _ = (x : ℝ) ^ (-(a - θ)) := hdiv
  exact squeeze_zero' (Eventually.of_forall h_lo) h_hi h_env

/-- **Master engine, little-o idiom.** The two-parameter engine restated in Mathlib's
asymptotics notation: any eventual envelope `maxPrimeGap x ≤ x^θ` gives `maxPrimeGap =o[atTop]
(x ↦ x^a)` for every target `a > θ`. This is the abstract counterpart of `bhp_gap_isLittleO_rpow`
(which fixes the source at the BHP exponent `0.525`) and generalises `bhp_gap_isLittleO_id`
(target `a = 1`). -/
theorem gap_isLittleO_rpow_of_rpow_bound {θ a : ℝ} (hθa : θ < a)
    (H : ∀ᶠ x : ℕ in atTop, (maxPrimeGap x : ℝ) ≤ (x : ℝ) ^ θ) :
    (fun x : ℕ => (maxPrimeGap x : ℝ)) =o[atTop] (fun x : ℕ => (x : ℝ) ^ a) := by
  refine (isLittleO_iff_tendsto' ?_).mpr (gap_div_rpow_littleo_of_rpow_bound hθa H)
  filter_upwards [eventually_ge_atTop 1] with x hx h0
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hx
  have hrp : (0 : ℝ) < (x : ℝ) ^ a := Real.rpow_pos_of_pos hxpos a
  rw [h0] at hrp
  exact absurd hrp (lt_irrefl 0)

end Erdos1138OQ03
