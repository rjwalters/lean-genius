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

/-- **Explicit decay rate of the normalised gap.** The normalised maximal prime gap not only
    tends to `0` (`bhp_implies_gap_littleo`) but does so at a concrete polynomial rate:
    `maxPrimeGap x / x = O(x^(-0.475))`. This sharpens the qualitative `Tendsto … (𝓝 0)` to a
    quantitative envelope with an explicit exponent `-(1 - 0.525) = -0.475`, packaged in Mathlib's
    asymptotics idiom (constant `1`, valid for `x ≥ 25`). It is the normalised counterpart of
    `gap_isBigO_rpow` (`maxPrimeGap = O(x^0.525)`), obtained by dividing that envelope by `x`. -/
theorem gap_div_isBigO_rpow_neg :
    (fun x : ℕ => (maxPrimeGap x : ℝ) / x) =O[atTop]
      (fun x : ℕ => (x : ℝ) ^ (-(0.475 : ℝ))) := by
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop 25] with x hx
  have hnn : (0 : ℝ) ≤ (x : ℝ) ^ (-(0.475 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg x) _
  have hlo : (0 : ℝ) ≤ (maxPrimeGap x : ℝ) / x :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlo, abs_of_nonneg hnn]
  exact gap_div_le_rpow_neg x hx

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
        ≤ (x : ℝ) ^ θ / x := by gcongr
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
        ≤ (x : ℝ) ^ θ / (x : ℝ) ^ a := by gcongr
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

/-- **Master engine, big-O idiom.** Any eventual power envelope `maxPrimeGap x ≤ x^θ`
already gives `maxPrimeGap =O[atTop] (x ↦ x^θ)` — the envelope *is* the big-O witness (constant
`1`), no sublinearity of `θ` required. This is the abstract counterpart of `gap_isBigO_rpow`
(which fixes `θ = 0.525` and uses `baker_harman_pintz`); together with the little-o and `Tendsto`
engines above it completes the abstract family, matching the concrete BHP family term for term. -/
theorem gap_isBigO_rpow_of_rpow_bound {θ : ℝ}
    (H : ∀ᶠ x : ℕ in atTop, (maxPrimeGap x : ℝ) ≤ (x : ℝ) ^ θ) :
    (fun x : ℕ => (maxPrimeGap x : ℝ)) =O[atTop] (fun x : ℕ => (x : ℝ) ^ θ) := by
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [H, eventually_ge_atTop 1] with x hx hx1
  have hnn : (0 : ℝ) ≤ (x : ℝ) ^ θ := Real.rpow_nonneg (Nat.cast_nonneg x) _
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (maxPrimeGap x)), abs_of_nonneg hnn]
  exact hx

/-- **Master engine, normalised decay rate.** From *any* eventual power envelope
`maxPrimeGap x ≤ x^θ`, the normalised gap decays at the explicit rate
`maxPrimeGap x / x = O(x^(θ - 1))` — the envelope divided by `x`. This is the abstract counterpart
of the concrete `gap_div_isBigO_rpow_neg` (the BHP instance `θ = 0.525`, giving `O(x^(-0.475))`),
and the big-O sharpening of the `Tendsto (·/x) → 0` engine `gap_littleo_of_rpow_bound`: no
sub-linearity of `θ` is needed for the big-O (the rate is negative exactly when `θ < 1`, which is
when it also gives sublinearity). -/
theorem gap_div_isBigO_rpow_sub_one_of_rpow_bound {θ : ℝ}
    (H : ∀ᶠ x : ℕ in atTop, (maxPrimeGap x : ℝ) ≤ (x : ℝ) ^ θ) :
    (fun x : ℕ => (maxPrimeGap x : ℝ) / x) =O[atTop] (fun x : ℕ => (x : ℝ) ^ (θ - 1)) := by
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [H, eventually_ge_atTop 1] with x hx hx1
  have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hx1)
  have hnn : (0 : ℝ) ≤ (x : ℝ) ^ (θ - 1) := Real.rpow_nonneg (Nat.cast_nonneg x) _
  have hlo : (0 : ℝ) ≤ (maxPrimeGap x : ℝ) / x :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlo, abs_of_nonneg hnn]
  have hdiv : (x : ℝ) ^ θ / x = (x : ℝ) ^ (θ - 1) := by
    rw [Real.rpow_sub hx_pos, Real.rpow_one]
  calc (maxPrimeGap x : ℝ) / x
      ≤ (x : ℝ) ^ θ / x := by gcongr
    _ = (x : ℝ) ^ (θ - 1) := hdiv

/-- **Master engine, little-o against `id`.** From *any* eventual power envelope
`maxPrimeGap x ≤ x^θ` with sub-linear exponent `θ < 1`, `maxPrimeGap =o[atTop] id`. This is the
abstract counterpart of `bhp_gap_isLittleO_id` (the BHP instance `θ = 0.525`), and the `=o id`
twin of the `Tendsto (·/x)` engine `gap_littleo_of_rpow_bound`. It is *not* subsumed by
`gap_isLittleO_rpow_of_rpow_bound` at `a = 1`, whose target `x^1` differs from `id`. -/
theorem gap_isLittleO_id_of_rpow_bound {θ : ℝ} (hθ : θ < 1)
    (H : ∀ᶠ x : ℕ in atTop, (maxPrimeGap x : ℝ) ≤ (x : ℝ) ^ θ) :
    (fun x : ℕ => (maxPrimeGap x : ℝ)) =o[atTop] (fun x : ℕ => (x : ℝ)) := by
  refine (isLittleO_iff_tendsto' ?_).mpr (gap_littleo_of_rpow_bound hθ H)
  filter_upwards [eventually_ge_atTop 1] with x hx h0
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hx
  rw [h0] at hxpos
  exact absurd hxpos (lt_irrefl 0)

/-- **Master engine, ε-form.** From *any* eventual power envelope `maxPrimeGap x ≤ x^θ` with
sub-linear exponent `θ < 1`, for every `ε > 0` eventually `maxPrimeGap x ≤ ε · x`. This is the
abstract counterpart of the concrete `bhp_gap_eventually_le_eps` (the BHP instance `θ = 0.525`):
the ε-form was the sole concrete BHP term without an engine twin, so this completes the abstract
family's term-for-term match. Like the other engines it takes the envelope in `atTop`-eventual
form, and it factors through the `Tendsto` engine `gap_littleo_of_rpow_bound` exactly as the
concrete `bhp_gap_eventually_le_eps` factors through `bhp_implies_gap_littleo`. -/
theorem gap_eventually_le_eps_of_rpow_bound {θ : ℝ} (hθ : θ < 1)
    (H : ∀ᶠ x : ℕ in atTop, (maxPrimeGap x : ℝ) ≤ (x : ℝ) ^ θ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, (maxPrimeGap x : ℝ) ≤ ε * x := by
  -- From the engine limit, `maxPrimeGap x / x < ε` eventually; clear the denominator.
  have hev : ∀ᶠ x : ℕ in atTop, (maxPrimeGap x : ℝ) / x < ε :=
    (gap_littleo_of_rpow_bound hθ H).eventually (eventually_lt_nhds hε)
  filter_upwards [hev, eventually_ge_atTop 1] with x hxlt hx1
  have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hx1)
  rw [div_lt_iff₀ hx_pos] at hxlt
  exact le_of_lt hxlt

/-! ### The fully general envelope engine: the power structure is genuinely irrelevant

Every engine above assumes the envelope is a *power* `x^θ`, yet the docstrings repeatedly
observe that "the exponent plays no role" in the sublinearity conclusion. This section
removes the power assumption altogether: sublinearity `maxPrimeGap x / x → 0` follows from
**any** eventual envelope `maxPrimeGap x ≤ f x` whose own normalisation `f x / x → 0`. The
power engine `gap_littleo_of_rpow_bound` is the instance `f x = x^θ` (with `θ < 1`), and the
parent's *conditional* Cramér branch — envelope `f x = C·(log x)²`, which is not a power of
`x` — plugs into the very same engine. This is the true mathematical content: only
sublinearity of the envelope matters, never its shape. -/

/-- **Fully general sublinearity engine.** From *any* eventual envelope
`maxPrimeGap x ≤ f x` whose normalisation `f x / x → 0`, the normalised maximal gap
`maxPrimeGap x / x → 0`. A real-analysis squeeze between `0` and `f x / x`; the envelope
need not be a power of `x` (subsuming both the `x^θ` and Cramér `(log x)²` branches). -/
theorem gap_littleo_of_littleo_envelope (f : ℕ → ℝ)
    (H : ∀ᶠ x : ℕ in atTop, (maxPrimeGap x : ℝ) ≤ f x)
    (hf : Tendsto (fun x : ℕ => f x / x) atTop (𝓝 0)) :
    Tendsto (fun x : ℕ => (maxPrimeGap x : ℝ) / x) atTop (𝓝 0) := by
  have h_lo : ∀ x : ℕ, 0 ≤ (maxPrimeGap x : ℝ) / x := fun x =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have h_hi : ∀ᶠ x : ℕ in atTop, (maxPrimeGap x : ℝ) / x ≤ f x / x := by
    filter_upwards [H, eventually_ge_atTop 1] with x hx hx1
    have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hx1)
    gcongr
  exact squeeze_zero' (Eventually.of_forall h_lo) h_hi hf

/-- **Fully general engine, little-o against `id`.** The `=o[atTop] id` idiom of
`gap_littleo_of_littleo_envelope`: any envelope `maxPrimeGap x ≤ f x` with `f x / x → 0`
gives `maxPrimeGap =o[atTop] id`. Generalises `gap_isLittleO_id_of_rpow_bound` off the
power family. -/
theorem gap_isLittleO_id_of_littleo_envelope (f : ℕ → ℝ)
    (H : ∀ᶠ x : ℕ in atTop, (maxPrimeGap x : ℝ) ≤ f x)
    (hf : Tendsto (fun x : ℕ => f x / x) atTop (𝓝 0)) :
    (fun x : ℕ => (maxPrimeGap x : ℝ)) =o[atTop] (fun x : ℕ => (x : ℝ)) := by
  refine (isLittleO_iff_tendsto' ?_).mpr (gap_littleo_of_littleo_envelope f H hf)
  filter_upwards [eventually_ge_atTop 1] with x hx h0
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hx
  rw [h0] at hxpos
  exact absurd hxpos (lt_irrefl 0)

/-- **The power engine is an instance of the general engine.**  Re-derives
`gap_littleo_of_rpow_bound` (envelope `x^θ`, `θ < 1`) from
`gap_littleo_of_littleo_envelope`, exhibiting the general engine as a strict generalisation:
the normalisation `x^θ / x = x^(θ-1) → 0` supplies the `hf` hypothesis. -/
theorem gap_littleo_of_rpow_bound_via_envelope {θ : ℝ} (hθ : θ < 1)
    (H : ∀ᶠ x : ℕ in atTop, (maxPrimeGap x : ℝ) ≤ (x : ℝ) ^ θ) :
    Tendsto (fun x : ℕ => (maxPrimeGap x : ℝ) / x) atTop (𝓝 0) := by
  refine gap_littleo_of_littleo_envelope (fun x => (x : ℝ) ^ θ) H ?_
  have h_env : Tendsto (fun x : ℕ => (x : ℝ) ^ (-(1 - θ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  refine h_env.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with x hx1
  have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hx1)
  rw [show (-(1 - θ)) = θ - 1 by ring, Real.rpow_sub hx_pos, Real.rpow_one]

-- ============================================================================
-- Individual-gap bridge: from the maximal gap `sSup` back to actual gaps
-- ============================================================================

/-- **Bridge: an individual consecutive-prime gap is at most the maximal gap.**

Every result above bounds the *maximal* gap `maxPrimeGap x = sSup (primeGapSet x)`. But the
object of Erdős #1138 is an *individual* gap `q - p` between consecutive primes `p < q ≤ x`.
This lemma connects the two: any such gap lies in `primeGapSet x`, hence is `≤` its supremum.
It is the `le_csSup` half complementing the parent's `csSup_le`-based upper bounds, and is what
lets the sup-level asymptotics below be read as statements about genuine prime gaps. -/
theorem consecutive_gap_le_maxPrimeGap {x p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q) (hqx : q ≤ x)
    (hcons : ∀ r, Nat.Prime r → p < r → q ≤ r) :
    q - p ≤ maxPrimeGap x := by
  unfold maxPrimeGap
  exact le_csSup (primeGapSet_bddAbove x) ⟨p, q, hp, hq, hpq, hqx, hcons, rfl⟩

/-- **Individual consecutive-prime gaps obey the Baker–Harman–Pintz bound.**

Composing the bridge `consecutive_gap_le_maxPrimeGap` with `baker_harman_pintz`: for `x ≥ 25`,
*every* gap `q - p` between consecutive primes with `q ≤ x` satisfies `q - p ≤ x^0.525`.
This is the concrete, gap-level statement of the BHP bound (the parent axiom is phrased for the
supremum only). -/
theorem consecutive_gap_le_rpow {x p q : ℕ} (hx : 25 ≤ x)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q) (hqx : q ≤ x)
    (hcons : ∀ r, Nat.Prime r → p < r → q ≤ r) :
    ((q - p : ℕ) : ℝ) ≤ (x : ℝ) ^ (0.525 : ℝ) := by
  calc ((q - p : ℕ) : ℝ)
      ≤ (maxPrimeGap x : ℝ) := by
        exact_mod_cast consecutive_gap_le_maxPrimeGap hp hq hpq hqx hcons
    _ ≤ (x : ℝ) ^ (0.525 : ℝ) := baker_harman_pintz x hx

/-- **Normalised individual gap bound.** The gap-level counterpart of `gap_div_le_rpow_neg`:
for `x ≥ 25` and any consecutive primes `p < q ≤ x`, the normalised gap `(q - p) / x` is at most
`x^(-0.475)`. As `x → ∞` this envelope vanishes, so every consecutive-prime gap below `x` is
eventually negligible compared with `x` — the sublinearity of `bhp_implies_gap_littleo` made
pointwise and gap-explicit. -/
theorem consecutive_gap_div_le_rpow_neg {x p q : ℕ} (hx : 25 ≤ x)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q) (hqx : q ≤ x)
    (hcons : ∀ r, Nat.Prime r → p < r → q ≤ r) :
    ((q - p : ℕ) : ℝ) / x ≤ (x : ℝ) ^ (-(0.475 : ℝ)) := by
  have hbridge : ((q - p : ℕ) : ℝ) ≤ (maxPrimeGap x : ℝ) := by
    exact_mod_cast consecutive_gap_le_maxPrimeGap hp hq hpq hqx hcons
  calc ((q - p : ℕ) : ℝ) / x
      ≤ (maxPrimeGap x : ℝ) / x := by gcongr
    _ ≤ (x : ℝ) ^ (-(0.475 : ℝ)) := gap_div_le_rpow_neg x hx

/-- **Effective individual-gap bound.** The gap-level counterpart of
`bhp_gap_le_eps_effective`: for any `ε` and `x ≥ 25` at which the explicit threshold
`1 ≤ ε · x^0.475` holds (equivalently `x^(-0.475) ≤ ε`, the point where the envelope has
dropped below `ε`), *every* consecutive-prime gap `q - p` with `q ≤ x` already satisfies
`q - p ≤ ε · x`.  Composes the bridge `consecutive_gap_le_maxPrimeGap` with the effective
sup-level bound, completing the gap-level trilogy alongside `consecutive_gap_le_rpow`
(`≤ x^0.525`) and `consecutive_gap_div_le_rpow_neg` (`/x ≤ x^(-0.475)`).  As with the
sup-level version, positivity of `ε` is forced by the threshold, not assumed. -/
theorem consecutive_gap_le_eps_effective {x p q : ℕ} (ε : ℝ)
    (hx25 : 25 ≤ x) (hthr : 1 ≤ ε * (x : ℝ) ^ (0.475 : ℝ))
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q) (hqx : q ≤ x)
    (hcons : ∀ r, Nat.Prime r → p < r → q ≤ r) :
    ((q - p : ℕ) : ℝ) ≤ ε * x := by
  have hbridge : ((q - p : ℕ) : ℝ) ≤ (maxPrimeGap x : ℝ) := by
    exact_mod_cast consecutive_gap_le_maxPrimeGap hp hq hpq hqx hcons
  exact le_trans hbridge (bhp_gap_le_eps_effective ε x hx25 hthr)

/-- **θ-generic bridge from a sup-level power bound to individual gaps.** Given *any*
power bound `maxPrimeGap x ≤ x^θ` at a point `x`, every consecutive-prime gap `q - p`
with `q ≤ x` already satisfies `q - p ≤ x^θ`.  This decouples the arithmetic input (the
exponent `θ` and the bound) from the sup→gap bridge exactly as the sup-level engines
`gap_littleo_of_rpow_bound` / `gap_div_rpow_littleo_of_rpow_bound` do for the asymptotics;
`consecutive_gap_le_rpow` is the instance `θ = 0.525` with the bound supplied by
`baker_harman_pintz`.  Any future strengthening of BHP plugs straight in. -/
theorem consecutive_gap_le_rpow_of_bound {θ : ℝ} {x p q : ℕ}
    (hbound : (maxPrimeGap x : ℝ) ≤ (x : ℝ) ^ θ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q) (hqx : q ≤ x)
    (hcons : ∀ r, Nat.Prime r → p < r → q ≤ r) :
    ((q - p : ℕ) : ℝ) ≤ (x : ℝ) ^ θ :=
  le_trans (by exact_mod_cast consecutive_gap_le_maxPrimeGap hp hq hpq hqx hcons) hbound

/-- **θ-generic normalised individual-gap bound.** The normalised counterpart of
`consecutive_gap_le_rpow_of_bound`: from a power bound `maxPrimeGap x ≤ x^θ` at `x > 0`,
every normalised consecutive gap `(q - p) / x` is at most `x^(θ-1)`.  This is the θ-generic
form of `consecutive_gap_div_le_rpow_neg` (whose exponent `-0.475 = 0.525 - 1`), and makes
the sublinearity envelope explicit for any envelope exponent: for `θ < 1` the bound
`x^(θ-1) → 0`.  Axiom input is only whatever supplies `hbound`. -/
theorem consecutive_gap_div_le_rpow_sub_one_of_bound {θ : ℝ} {x p q : ℕ}
    (hx : 0 < x) (hbound : (maxPrimeGap x : ℝ) ≤ (x : ℝ) ^ θ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q) (hqx : q ≤ x)
    (hcons : ∀ r, Nat.Prime r → p < r → q ≤ r) :
    ((q - p : ℕ) : ℝ) / x ≤ (x : ℝ) ^ (θ - 1) := by
  have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have h1 : ((q - p : ℕ) : ℝ) ≤ (x : ℝ) ^ θ :=
    consecutive_gap_le_rpow_of_bound hbound hp hq hpq hqx hcons
  have hdiv : (x : ℝ) ^ θ / x = (x : ℝ) ^ (θ - 1) := by
    rw [Real.rpow_sub hx_pos, Real.rpow_one]
  calc ((q - p : ℕ) : ℝ) / x
      ≤ (x : ℝ) ^ θ / x := by gcongr
    _ = (x : ℝ) ^ (θ - 1) := hdiv

/-- **θ-generic effective individual-gap bound.** The effective (pointwise) counterpart of
`consecutive_gap_le_rpow_of_bound`, and the θ-generic form of `consecutive_gap_le_eps_effective`
(whose exponent is `θ = 0.525`): from a power bound `maxPrimeGap x ≤ x^θ` at a point `x > 0`
that has passed the explicit threshold `1 ≤ ε · x^(1-θ)` (equivalently `x^(θ-1) ≤ ε`, the point
where the `θ`-envelope has dropped below `ε`), *every* consecutive-prime gap `q - p` with
`q ≤ x` already satisfies `q - p ≤ ε · x`.  Composes `consecutive_gap_le_rpow_of_bound` with the
threshold `x^θ = x^θ · 1 ≤ x^θ · (ε · x^(1-θ)) = ε · x`.  This completes the θ-generic
consecutive-gap trilogy — `_le_rpow_of_bound` (`≤ x^θ`), `_div_le_rpow_sub_one_of_bound`
(`/x ≤ x^(θ-1)`), and this effective `≤ ε·x` form — to exactly parallel the BHP-specific
trilogy, so any future BHP strengthening supplies all three at once.  As in the BHP-specific
version, positivity of `ε` is forced by the threshold, not assumed. -/
theorem consecutive_gap_le_eps_of_bound {θ : ℝ} {x p q : ℕ} (ε : ℝ)
    (hx : 0 < x) (hbound : (maxPrimeGap x : ℝ) ≤ (x : ℝ) ^ θ)
    (hthr : 1 ≤ ε * (x : ℝ) ^ (1 - θ))
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q) (hqx : q ≤ x)
    (hcons : ∀ r, Nat.Prime r → p < r → q ≤ r) :
    ((q - p : ℕ) : ℝ) ≤ ε * x := by
  have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hxθ : (0 : ℝ) < (x : ℝ) ^ θ := Real.rpow_pos_of_pos hx_pos θ
  have h1 : ((q - p : ℕ) : ℝ) ≤ (x : ℝ) ^ θ :=
    consecutive_gap_le_rpow_of_bound hbound hp hq hpq hqx hcons
  -- The threshold `1 ≤ ε·x^(1-θ)` lifts (scale by `x^θ > 0`) to `x^θ ≤ ε·x`.
  have h2 : (x : ℝ) ^ θ ≤ ε * x := by
    have hstep := mul_le_mul_of_nonneg_right hthr (le_of_lt hxθ)
    rwa [one_mul, mul_assoc, ← Real.rpow_add hx_pos,
      show (1 : ℝ) - θ + θ = 1 by ring, Real.rpow_one] at hstep
  exact le_trans h1 h2

/-! ### Multiplicative closeness: consecutive primes have ratio tending to `1`

The results above are all *additive* (`q - p = o(x)`).  Their multiplicative
shadow is that **consecutive primes are close in ratio**: applying the sup-level
bound at `x = q` (the pair `p < q ≤ q` always qualifies) gives
`(q - p) / q ≤ q^(-0.475)`, so

    (p : ℝ) / q  =  1 - (q - p)/q  ≥  1 - q^(-0.475)  →  1,

and, taking reciprocals, `q / p ≤ (1 - q^(-0.475))⁻¹ → 1`.  Thus consecutive
primes satisfy `p / q → 1`; this is the multiplicative form of sublinearity,
orthogonal to the additive `o(x)` layer. -/

/-- **Lower ratio bound for consecutive primes.**  For consecutive primes
`p < q` with `q ≥ 25`, the smaller prime is at least `(1 - q^(-0.475))` times the
larger: `1 - q^(-0.475) ≤ p / q`.  Obtained by applying
`consecutive_gap_div_le_rpow_neg` at `x = q` (so `(q - p)/q ≤ q^(-0.475)`) and
rewriting `(q - p)/q = 1 - p/q`.  As `q → ∞` the envelope `q^(-0.475) → 0`, so
`p / q → 1`. -/
theorem consecutive_ratio_ge {p q : ℕ} (hq25 : 25 ≤ q)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q)
    (hcons : ∀ r, Nat.Prime r → p < r → q ≤ r) :
    1 - (q : ℝ) ^ (-(0.475 : ℝ)) ≤ (p : ℝ) / q := by
  have hqR : (0 : ℝ) < (q : ℝ) := by
    have : (0 : ℕ) < q := lt_of_lt_of_le (by norm_num) hq25
    exact_mod_cast this
  have hgap : ((q - p : ℕ) : ℝ) / q ≤ (q : ℝ) ^ (-(0.475 : ℝ)) :=
    consecutive_gap_div_le_rpow_neg hq25 hp hq hpq (le_refl q) hcons
  have hcast : ((q - p : ℕ) : ℝ) = (q : ℝ) - (p : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hpq)]
  rw [hcast, sub_div, div_self (ne_of_gt hqR)] at hgap
  linarith

/-- **Upper ratio bound for consecutive primes.**  Reciprocal companion of
`consecutive_ratio_ge`: for consecutive primes `p < q` with `q ≥ 25`,
`q / p ≤ (1 - q^(-0.475))⁻¹`.  Since `q ≥ 25 > 1` the base satisfies
`q^(-0.475) < 1`, so `1 - q^(-0.475) > 0` and reciprocals reverse the lower
bound `1 - q^(-0.475) ≤ p/q`.  As `q → ∞` the right-hand side `→ 1`, giving the
matching upper half of `p/q → 1`. -/
theorem consecutive_ratio_le {p q : ℕ} (hq25 : 25 ≤ q)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q)
    (hcons : ∀ r, Nat.Prime r → p < r → q ≤ r) :
    (q : ℝ) / p ≤ (1 - (q : ℝ) ^ (-(0.475 : ℝ)))⁻¹ := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < (q : ℝ) := by
    have : (0 : ℕ) < q := lt_of_lt_of_le (by norm_num) hq25
    exact_mod_cast this
  have hlow : 1 - (q : ℝ) ^ (-(0.475 : ℝ)) ≤ (p : ℝ) / q :=
    consecutive_ratio_ge hq25 hp hq hpq hcons
  have hbase : (q : ℝ) ^ (-(0.475 : ℝ)) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · have : (1 : ℕ) < q := lt_of_lt_of_le (by norm_num) hq25
      exact_mod_cast this
    · norm_num
  have hpos : (0 : ℝ) < 1 - (q : ℝ) ^ (-(0.475 : ℝ)) := by linarith
  have hinv : (q : ℝ) / p = 1 / ((p : ℝ) / q) := by rw [one_div, inv_div]
  rw [hinv, ← one_div ((1 : ℝ) - (q : ℝ) ^ (-(0.475 : ℝ)))]
  exact one_div_le_one_div_of_le hpos hlow

/-- **θ-generic lower ratio bound.**  The exponent-parametric form of
`consecutive_ratio_ge`: from *any* sup-level power bound `maxPrimeGap q ≤ q^θ`
at `q > 0`, consecutive primes `p < q` satisfy `1 - q^(θ-1) ≤ p / q`.  For
`θ < 1` the envelope `q^(θ-1) → 0`, so `p/q → 1`; the BHP instance
`consecutive_ratio_ge` is `θ = 0.525` (with `θ - 1 = -0.475`).  Any future
strengthening of BHP plugs straight in. -/
theorem consecutive_ratio_ge_of_bound {θ : ℝ} {p q : ℕ}
    (hqpos : 0 < q) (hbound : (maxPrimeGap q : ℝ) ≤ (q : ℝ) ^ θ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q)
    (hcons : ∀ r, Nat.Prime r → p < r → q ≤ r) :
    1 - (q : ℝ) ^ (θ - 1) ≤ (p : ℝ) / q := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hgap : ((q - p : ℕ) : ℝ) / q ≤ (q : ℝ) ^ (θ - 1) :=
    consecutive_gap_div_le_rpow_sub_one_of_bound hqpos hbound hp hq hpq (le_refl q) hcons
  have hcast : ((q - p : ℕ) : ℝ) = (q : ℝ) - (p : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hpq)]
  rw [hcast, sub_div, div_self (ne_of_gt hqR)] at hgap
  linarith


-- ============================================================================
-- The orthogonal LOWER-bound direction: prime gaps are unbounded
--
-- Everything above is upper-bound driven (the BHP squeeze forces
-- `maxPrimeGap x / x → 0`). The complementary fact is a *lower* bound with a
-- completely different, axiom-free mechanism: consecutive-prime gaps are
-- arbitrarily large, so `maxPrimeGap x → ∞`. The classical construction is the
-- run of composites `(N+1)! + 2, …, (N+1)! + (N+1)`, none of which is prime.
-- Combined with the sublinearity above, this pins the true two-sided asymptotic
-- character of the maximal gap: it grows without bound, yet sublinearly.
-- This direction does NOT use `baker_harman_pintz`.
-- ============================================================================

/-- **Composite run around `(N+1)!`.** For `2 ≤ k ≤ N+1` the number `(N+1)! + k`
is composite (`k ∣ (N+1)!` by `Nat.dvd_factorial`, hence `k ∣ (N+1)! + k` with
`1 < k < (N+1)! + k`), so it is not prime. This is the engine behind arbitrarily
large prime gaps. -/
theorem factorial_succ_add_not_prime {N k : ℕ} (hk2 : 2 ≤ k) (hkN : k ≤ N + 1) :
    ¬ Nat.Prime (Nat.factorial (N + 1) + k) := by
  intro hp
  have hkdvd : k ∣ Nat.factorial (N + 1) := Nat.dvd_factorial (by omega) hkN
  have hdvd : k ∣ Nat.factorial (N + 1) + k := Dvd.dvd.add hkdvd (dvd_refl k)
  have hfac_pos : 0 < Nat.factorial (N + 1) := Nat.factorial_pos _
  rcases hp.eq_one_or_self_of_dvd k hdvd with h1 | hself
  · omega
  · omega

/-- **Arbitrarily large prime gaps (axiom-free).** For every `N` there exist
consecutive primes `p < q` with gap `q - p ≥ N`.

Construction: with `M = (N+1)!`, take `p` = the largest prime `≤ M+1`
(`Nat.findGreatest`) and `q` = the least prime `> M+1` (`Nat.find`). The
composite run `M+2, …, M+(N+1)` (`factorial_succ_add_not_prime`) forces
`q ≥ M+N+2`, while `p ≤ M+1`, so `q - p ≥ N+1`. Consecutiveness holds because
`p` is the greatest prime `≤ M+1` and `q` the least prime `> M+1`, leaving no
prime strictly between them. Uses only Euclid's theorem and `Nat.dvd_factorial`
— no BHP input. -/
theorem exists_consecutive_prime_gap_ge (N : ℕ) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧
      (∀ r, Nat.Prime r → p < r → q ≤ r) ∧ N ≤ q - p := by
  classical
  have hMpos : 0 < Nat.factorial (N + 1) := Nat.factorial_pos _
  -- p := largest prime ≤ (N+1)! + 1
  set p := Nat.findGreatest Nat.Prime (Nat.factorial (N + 1) + 1) with hp_def
  have hp_prime : Nat.Prime p :=
    Nat.findGreatest_spec (m := 2) (by omega) Nat.prime_two
  have hp_le : p ≤ Nat.factorial (N + 1) + 1 := Nat.findGreatest_le _
  -- q := least prime > (N+1)! + 1
  have hqex : ∃ m, Nat.factorial (N + 1) + 1 < m ∧ Nat.Prime m := by
    obtain ⟨r, hr_ge, hr_prime⟩ := Nat.exists_infinite_primes (Nat.factorial (N + 1) + 2)
    exact ⟨r, by omega, hr_prime⟩
  set q := Nat.find hqex with hq_def
  obtain ⟨hMq, hq_prime⟩ := Nat.find_spec hqex
  -- p < q since p ≤ M+1 < q
  have hpq : p < q := by omega
  -- consecutiveness: no prime strictly between p and q
  have hcons : ∀ r, Nat.Prime r → p < r → q ≤ r := by
    intro r hr hpr
    by_contra hlt
    push_neg at hlt
    have hmin := Nat.find_min hqex hlt
    have hrle : r ≤ Nat.factorial (N + 1) + 1 := by
      by_contra hc; push_neg at hc; exact hmin ⟨hc, hr⟩
    exact (Nat.findGreatest_is_greatest hpr hrle) hr
  -- gap lower bound: the composite run forces q ≥ M + N + 2
  have hq_big : Nat.factorial (N + 1) + N + 2 ≤ q := by
    by_contra hc
    push_neg at hc
    set k := q - Nat.factorial (N + 1) with hk
    have hk2 : 2 ≤ k := by omega
    have hkN : k ≤ N + 1 := by omega
    have hqk : q = Nat.factorial (N + 1) + k := by omega
    have hnp := factorial_succ_add_not_prime hk2 hkN
    rw [← hqk] at hnp
    exact hnp hq_prime
  exact ⟨p, q, hp_prime, hq_prime, hpq, hcons, by omega⟩

/-- **`maxPrimeGap` is unbounded (pointwise).** For every `N` there is an `x`
with `maxPrimeGap x ≥ N`: take `x = q` from `exists_consecutive_prime_gap_ge`;
the gap `q - p` lies in `primeGapSet q`, so it is `≤ maxPrimeGap q`. Axiom-free. -/
theorem exists_maxPrimeGap_ge (N : ℕ) : ∃ x : ℕ, N ≤ maxPrimeGap x := by
  obtain ⟨p, q, hp, hq, hpq, hcons, hgap⟩ := exists_consecutive_prime_gap_ge N
  refine ⟨q, ?_⟩
  have hmem : (q - p) ∈ primeGapSet q :=
    ⟨p, q, hp, hq, hpq, le_refl q, hcons, rfl⟩
  have hle : (q - p) ≤ maxPrimeGap q := le_csSup (primeGapSet_bddAbove q) hmem
  omega

/-- **The maximal prime gap tends to infinity.** `maxPrimeGap` is monotone
(`maxPrimeGap_mono`) and unbounded (`exists_maxPrimeGap_ge`), hence
`maxPrimeGap x → ∞`. This is the axiom-free lower-bound counterpart of the
BHP-driven sublinearity `bhp_implies_gap_littleo`. -/
theorem maxPrimeGap_tendsto_atTop :
    Tendsto (fun x : ℕ => maxPrimeGap x) atTop atTop :=
  tendsto_atTop_atTop_of_monotone (fun _ _ h => maxPrimeGap_mono h) exists_maxPrimeGap_ge

/-- **Real-valued form.** `(maxPrimeGap x : ℝ) → ∞`, obtained by composing the
`ℕ`-valued divergence with the cast `ℕ ↪ ℝ`. -/
theorem maxPrimeGap_cast_tendsto_atTop :
    Tendsto (fun x : ℕ => (maxPrimeGap x : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp maxPrimeGap_tendsto_atTop

/-- **Two-sided asymptotic character of the maximal prime gap.** Packaging the
two orthogonal directions of this entry: the maximal prime gap grows *without
bound* (`maxPrimeGap x → ∞`, axiom-free, via arbitrarily large gaps) yet remains
*sublinear* (`maxPrimeGap x / x → 0`, from Baker–Harman–Pintz). Neither half
follows from the other: unboundedness is a lower bound with an elementary
mechanism, sublinearity an upper bound needing the deep BHP input. -/
theorem maxPrimeGap_unbounded_and_sublinear :
    Tendsto (fun x : ℕ => (maxPrimeGap x : ℝ)) atTop atTop ∧
      Tendsto (fun x : ℕ => (maxPrimeGap x : ℝ) / x) atTop (𝓝 0) :=
  ⟨maxPrimeGap_cast_tendsto_atTop, bhp_implies_gap_littleo⟩

-- ============================================================================
-- Part: Primes in short intervals (localisation consequence of BHP)
-- ============================================================================

/-- **Primes in short intervals, from Baker–Harman–Pintz.** For every `ε > 0`,
every sufficiently large `x` contains a prime in the half-open interval
`(x, (1 + ε)·x]`.

This is a genuinely new *localisation* consequence of BHP-sublinearity, not a
repackaging of the `maxPrimeGap` asymptotics: those record the *size* of the
largest gap below `x`, whereas this asserts a prime exists in a *specific short
window* above `x`. The proof pairs the largest prime `p ≤ x` (`Nat.findGreatest`)
with the next prime `q` (`Nat.find`); consecutiveness plus Bertrand's postulate
(`prime_gap_le_prev_prime`) give `q ≤ 2x`, so the gap `q - p` lies in
`primeGapSet (2x)` and is bounded by `maxPrimeGap (2x)`. BHP-sublinearity applied
at scale `2x` (the `ε/2` envelope pulled back along `x ↦ 2x`) forces
`maxPrimeGap (2x) ≤ ε·x` eventually, whence `q - x ≤ q - p ≤ ε·x`, i.e.
`q ≤ (1 + ε)·x`. Depends only on the parent `baker_harman_pintz` axiom. -/
theorem bhp_prime_in_short_interval (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      ∃ q : ℕ, Nat.Prime q ∧ (x : ℝ) < q ∧ (q : ℝ) ≤ (1 + ε) * x := by
  classical
  -- `maxPrimeGap` at scale `2x` is eventually `≤ ε·x` (BHP-sublinearity, ε/2 form).
  have hhalf : (0 : ℝ) < ε / 2 := by positivity
  have hgap := bhp_gap_eventually_le_eps (ε / 2) hhalf
  have hmap : Tendsto (fun x : ℕ => 2 * x) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun a b h => by omega) (fun n => ⟨n, by omega⟩)
  have htwo := hmap.eventually hgap
  filter_upwards [htwo, eventually_ge_atTop 2] with x hbound hx2
  -- `p` := largest prime `≤ x`.
  set p := Nat.findGreatest Nat.Prime x with hp_def
  have hp_prime : Nat.Prime p := Nat.findGreatest_spec (m := 2) hx2 Nat.prime_two
  have hp_le : p ≤ x := Nat.findGreatest_le _
  -- `q` := least prime `> x`.
  have hqex : ∃ m, x < m ∧ Nat.Prime m := by
    obtain ⟨r, hr_ge, hr_prime⟩ := Nat.exists_infinite_primes (x + 1)
    exact ⟨r, by omega, hr_prime⟩
  set q := Nat.find hqex with hq_def
  obtain ⟨hxq, hq_prime⟩ := Nat.find_spec hqex
  have hpq : p < q := by omega
  -- Consecutiveness: no prime lies strictly between `p` and `q`.
  have hcons : ∀ r, Nat.Prime r → p < r → q ≤ r := by
    intro r hr hpr
    have hxr : x < r := by
      by_contra hc
      exact (Nat.findGreatest_is_greatest hpr (not_lt.mp hc)) hr
    exact Nat.find_le ⟨hxr, hr⟩
  -- Gap `≤ p` (Bertrand), hence `q ≤ 2x`.
  have hgap_le : q - p ≤ p := prime_gap_le_prev_prime p q hp_prime hq_prime hpq hcons
  have hq2x : q ≤ 2 * x := by omega
  -- The gap lies in `primeGapSet (2x)`, so is `≤ maxPrimeGap (2x)`.
  have hmem : (q - p) ∈ primeGapSet (2 * x) :=
    ⟨p, q, hp_prime, hq_prime, hpq, hq2x, hcons, rfl⟩
  have hle : (q - p) ≤ maxPrimeGap (2 * x) := le_csSup (primeGapSet_bddAbove _) hmem
  -- Cast to `ℝ` and finish: `q - x ≤ q - p ≤ maxPrimeGap (2x) ≤ ε·x`.
  refine ⟨q, hq_prime, by exact_mod_cast hxq, ?_⟩
  have hcastgap : ((q - p : ℕ) : ℝ) = (q : ℝ) - p := by
    rw [Nat.cast_sub (le_of_lt hpq)]
  have hle_real : (q : ℝ) - p ≤ (maxPrimeGap (2 * x) : ℝ) := by
    rw [← hcastgap]; exact_mod_cast hle
  have hbound' : (maxPrimeGap (2 * x) : ℝ) ≤ ε * x := by
    have hcast : (ε / 2) * ((2 * x : ℕ) : ℝ) = ε * x := by push_cast; ring
    rw [hcast] at hbound; exact hbound
  have hp_le_real : (p : ℝ) ≤ x := by exact_mod_cast hp_le
  have expand : (1 + ε) * x = x + ε * x := by ring
  rw [expand]; linarith [hle_real, hbound', hp_le_real]

end Erdos1138OQ03
