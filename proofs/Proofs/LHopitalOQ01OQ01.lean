/-
# Monotone Quotients and the Converse of L'Hôpital (OQ-01 / OQ-01)

## The Question

The parent entry (`lhopital-oq-01`, namespace `LHopitalConverse`) exhibits the classic
failure of the *converse* of L'Hôpital's rule: with `f(x) = x + sin x`, `g(x) = x`,

    lim_{x→∞} f(x)/g(x) = 1,   but   lim_{x→∞} f'(x)/g'(x) = lim_{x→∞}(1 + cos x)

does **not exist**. The follow-up question asked here is:

  *Can the converse be rescued by a monotonicity hypothesis? If `f/g` is monotone and the
  indeterminate-form conditions hold, must `lim f/g = lim f'/g'` whenever both limits exist?*

## The Answer

**Yes — but the monotonicity hypothesis is entirely superfluous.** Whenever `lim f'/g'`
exists (under the standard 0/0 indeterminate-form hypotheses), L'Hôpital's rule in its
*forward* direction already forces

    lim f/g = lim f'/g'.

So if *both* limits exist they cannot differ, irrespective of whether `f/g` is monotone.
The qualifier "whenever both limits exist" does all the work: the only way the converse
can fail (as in the parent example) is for `lim f'/g'` to fail to *exist*. Monotonicity of
`f/g` neither helps nor is required.

This file makes that precise in two ways:

* `converse_holds_when_both_limits_exist` — no monotonicity hypothesis appears at all; the
  two existing limits are proved equal by combining forward L'Hôpital with uniqueness of
  limits.
* `monotone_quotient_converse` — the literal statement from the question, carrying an
  explicit `MonotoneOn` hypothesis `_hmono`. The underscore in its name records that the
  hypothesis is **discharged without ever being used**: the proof is the previous theorem
  applied verbatim.

The mathematical content is therefore a sharpening of the parent counterexample: the
converse of L'Hôpital fails *only* through non-existence of `lim f'/g'`, never through a
genuine disagreement of two existing limits — and no order/monotonicity assumption changes
that.

Self-contained: imports only Mathlib. The single analytic input is Mathlib's forward
L'Hôpital rule at infinity, `HasDerivAt.lhopital_zero_atTop_on_Ioi`.
-/

import Mathlib

namespace LHopitalOQ01OQ01

open Filter Topology Set

/-- **Forward L'Hôpital at infinity (0/0 form).** Repackaged from Mathlib for readability:
if `f, g` are differentiable on `(a, ∞)` with `f, g → 0`, `g' ≠ 0` there, and the derivative
quotient `f'/g'` tends to `c`, then the quotient `f/g` also tends to `c`. -/
theorem lhopital_atTop {f g f' g' : ℝ → ℝ} {a c : ℝ}
    (hff' : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioi a, g' x ≠ 0)
    (hf0 : Tendsto f atTop (𝓝 0))
    (hg0 : Tendsto g atTop (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) atTop (𝓝 c)) :
    Tendsto (fun x => f x / g x) atTop (𝓝 c) :=
  HasDerivAt.lhopital_zero_atTop_on_Ioi hff' hgg' hg' hf0 hg0 hdiv

/-- **Main theorem: when both limits exist they coincide — monotonicity is not needed.**

Under the standard 0/0 indeterminate-form hypotheses at infinity, if the quotient `f/g`
tends to `l` *and* the derivative quotient `f'/g'` tends to `L`, then `l = L`.

Notice the hypothesis list: there is **no** monotonicity assumption on `f/g`. The forward
direction of L'Hôpital already produces `Tendsto (f/g) atTop (𝓝 L)` from the existence of
`L`, and uniqueness of limits in a Hausdorff space then forces `l = L`. This is the precise
sense in which "must `lim f/g = lim f'/g'` whenever both limits exist?" is answered *yes,
unconditionally*. -/
theorem converse_holds_when_both_limits_exist
    {f g f' g' : ℝ → ℝ} {a l L : ℝ}
    (hff' : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioi a, g' x ≠ 0)
    (hf0 : Tendsto f atTop (𝓝 0))
    (hg0 : Tendsto g atTop (𝓝 0))
    (hfg : Tendsto (fun x => f x / g x) atTop (𝓝 l))
    (hfg' : Tendsto (fun x => f' x / g' x) atTop (𝓝 L)) :
    l = L := by
  have hL : Tendsto (fun x => f x / g x) atTop (𝓝 L) :=
    lhopital_atTop hff' hgg' hg' hf0 hg0 hfg'
  exact tendsto_nhds_unique hfg hL

/-- **The question, stated literally — with the monotonicity hypothesis shown to be unused.**

This is exactly the proposition posed by the open question: assume in addition that the
quotient `f/g` is monotone on `(a, ∞)`. The conclusion `l = L` follows. The hypothesis
`_hmono` is named with a leading underscore precisely because it is *discharged without
being referenced* — the proof is `converse_holds_when_both_limits_exist` applied verbatim.
Thus monotonicity is a red herring: it can be assumed, but it contributes nothing. -/
theorem monotone_quotient_converse
    {f g f' g' : ℝ → ℝ} {a l L : ℝ}
    (_hmono : MonotoneOn (fun x => f x / g x) (Ioi a))
    (hff' : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioi a, g' x ≠ 0)
    (hf0 : Tendsto f atTop (𝓝 0))
    (hg0 : Tendsto g atTop (𝓝 0))
    (hfg : Tendsto (fun x => f x / g x) atTop (𝓝 l))
    (hfg' : Tendsto (fun x => f' x / g' x) atTop (𝓝 L)) :
    l = L :=
  converse_holds_when_both_limits_exist hff' hgg' hg' hf0 hg0 hfg hfg'

/-- **The failure mode is exactly non-existence.** Contrapositive packaging of the main
theorem: if the derivative quotient `f'/g'` *converges* to some `L`, then the original
quotient `f/g` converges to the *same* value. Hence the only route to a "converse failure"
(as realised by the parent example `f = x + sin x`, `g = x`) is for `lim f'/g'` to fail to
exist — never for two existing limits to disagree. -/
theorem converse_failure_only_via_nonexistence
    {f g f' g' : ℝ → ℝ} {a L : ℝ}
    (hff' : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioi a, g' x ≠ 0)
    (hf0 : Tendsto f atTop (𝓝 0))
    (hg0 : Tendsto g atTop (𝓝 0))
    (hfg' : Tendsto (fun x => f' x / g' x) atTop (𝓝 L)) :
    Tendsto (fun x => f x / g x) atTop (𝓝 L) :=
  lhopital_atTop hff' hgg' hg' hf0 hg0 hfg'

end LHopitalOQ01OQ01
