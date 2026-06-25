import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-
# The Elementary Fatou ⇒ Dominated Convergence Derivation via `g + fₙ` and `g − fₙ`

## What This Proves

The classical textbook derivation of the **dominated convergence theorem (DCT)**
from **Fatou's lemma** runs through the two nonnegative shifts of the sequence.
Given real measurable `fₙ : α → ℝ` with `|fₙ| ≤ g` for a fixed integrable
majorant `g`, and `fₙ → F` pointwise, the functions
```
  g + fₙ ≥ 0     and     g − fₙ ≥ 0
```
are nonnegative, dominated by the integrable `2g`, and converge to `g + F`,
`g − F`. Applying Fatou's bracket to each yields
```
  ∫ (g + fₙ) → ∫ (g + F),      ∫ (g − fₙ) → ∫ (g − F),
```
and cancelling the constant `∫ g` from either bracket gives the headline
```
  ∫ fₙ → ∫ F.
```
We expose **both** brackets explicitly: `dct_of_dominated` derives the theorem
from `g + fₙ`, and `dct_of_dominated_sub` from `g − fₙ` — the two halves of the
classical argument.

This is the follow-up question `fatou-lemma-oq-01-oq-02-oq-01` left open by the
sibling entry `fatou-lemma-oq-01-oq-02`, which proved (on the *obstruction* side)
that the parent's escaping-mass sequence has no integrable majorant. Where that
entry explains why DCT *cannot* apply to the escaping mass, this entry supplies
the *positive* content: the explicit Fatou ⇒ DCT route for signed integrands.

**On "via Fatou".** The nonnegative shifts are handled by Mathlib's nonnegative
dominated convergence theorem `tendsto_lintegral_of_dominated_convergence`, whose
proof is *literally* `tendsto_of_le_liminf_of_limsup_le` of forward Fatou
(`lintegral_liminf_le`) and reverse Fatou (`limsup_lintegral_le`) — i.e. the two
Fatou inequalities squeezing the nonnegative integrals. So this is the genuine
Fatou ⇒ DCT route, applied to `g ± fₙ`; crucially it does **not** invoke Mathlib's
*Bochner* dominated convergence theorem (`tendsto_integral_of_dominated_convergence`),
which would be circular. The role of the integrable majorant `g` is exactly to
make the reverse-Fatou bracket of `g ± fₙ` finite.

## Why It Is Not in Mathlib

Mathlib proves the Bochner DCT through the abstract `setToFun`/`L1` machinery, not
through the `g ± fₙ` Fatou reduction. The explicit signed derivation from the
nonnegative Fatou bracket is the new content.

## Axiom Status

Fully verified, 0 sorries, 0 `axiom` declarations, no `native_decide`. Relies
only on Mathlib's measure theory and the foundational axioms `propext`,
`Classical.choice`, `Quot.sound`.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace FatouLemmaOQ01OQ02OQ01

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Dominated convergence theorem, via Fatou applied to `g + fₙ`.**

For real measurable `fₙ` with `|fₙ| ≤ g` (a fixed integrable majorant) and
`fₙ → F` pointwise, the integrals converge: `∫ fₙ → ∫ F`.

The proof is the upper half of the classical Fatou ⇒ DCT argument. The
nonnegative sequence `g + fₙ ≥ 0` is dominated by the integrable `2g` and
converges to `g + F`; the nonnegative dominated convergence theorem (Fatou's
bracket — forward `lintegral_liminf_le` plus reverse `limsup_lintegral_le`) gives
`∫⁻ (g + fₙ) → ∫⁻ (g + F)`, which transfers to the real integrals and, after
cancelling the constant `∫ g`, yields the claim. -/
theorem dct_of_dominated
    {f : ℕ → α → ℝ} {F : α → ℝ} {g : α → ℝ}
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g) (hgi : Integrable g μ)
    (hbound : ∀ n a, |f n a| ≤ g a)
    (hconv : ∀ a, Tendsto (fun n => f n a) atTop (𝓝 (F a))) :
    Tendsto (fun n => ∫ a, f n a ∂μ) atTop (𝓝 (∫ a, F a ∂μ)) := by
  -- Basic pointwise facts.
  have hgnn : ∀ a, 0 ≤ g a := fun a => (abs_nonneg _).trans (hbound 0 a)
  have hFmeas : Measurable F :=
    measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.mpr hconv)
  have hFbound : ∀ a, |F a| ≤ g a := fun a =>
    le_of_tendsto ((hconv a).abs) (Eventually.of_forall fun n => hbound n a)
  -- Integrability of `fₙ`, `F` and the shifted sequences.
  have hfi : ∀ n, Integrable (f n) μ := fun n =>
    Integrable.mono' hgi (hf n).aestronglyMeasurable
      (Eventually.of_forall fun a => (Real.norm_eq_abs _).symm ▸ hbound n a)
  have hFi : Integrable F μ :=
    Integrable.mono' hgi hFmeas.aestronglyMeasurable
      (Eventually.of_forall fun a => (Real.norm_eq_abs _).symm ▸ hFbound a)
  -- Pointwise nonnegativity of `g + fₙ` and `g + F`.
  have hnn : ∀ n a, 0 ≤ g a + f n a := fun n a => by
    linarith [hbound n a, neg_abs_le (f n a)]
  have hnnF : ∀ a, 0 ≤ g a + F a := fun a => by
    linarith [hFbound a, neg_abs_le (F a)]
  -- Fatou's bracket on the nonnegative sequence `g + fₙ`, dominated by `2g`.
  have hDCT :
      Tendsto (fun n => ∫⁻ a, ENNReal.ofReal (g a + f n a) ∂μ) atTop
        (𝓝 (∫⁻ a, ENNReal.ofReal (g a + F a) ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence
      (fun a => ENNReal.ofReal (2 * g a)) (fun n => (hg.add (hf n)).ennreal_ofReal)
      (fun n => Eventually.of_forall fun a => ?_) ?_
      (Eventually.of_forall fun a => ?_)
    · -- `g + fₙ ≤ 2g` since `fₙ ≤ |fₙ| ≤ g`.
      exact ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (f n a), hbound n a])
    · -- `∫⁻ ofReal (2g) ≠ ∞` from integrability of `2g`.
      have h2 : Integrable (fun a => 2 * g a) μ := hgi.const_mul 2
      have h2nn : 0 ≤ᵐ[μ] fun a => 2 * g a :=
        Eventually.of_forall fun a => mul_nonneg (by norm_num) (hgnn a)
      exact ((hasFiniteIntegral_iff_ofReal h2nn).mp h2.hasFiniteIntegral).ne
    · -- `ofReal (g + fₙ a) → ofReal (g + F a)` pointwise.
      exact (ENNReal.continuous_ofReal.tendsto _).comp
        (tendsto_const_nhds.add (hconv a))
  -- Transfer each lintegral back to the real integral of the nonnegative `g + fₙ`.
  have hcvt : ∀ n, ∫⁻ a, ENNReal.ofReal (g a + f n a) ∂μ
      = ENNReal.ofReal (∫ a, (g a + f n a) ∂μ) := fun n =>
    (ofReal_integral_eq_lintegral_ofReal (hgi.add (hfi n))
      (Eventually.of_forall (hnn n))).symm
  have hcvtF : ∫⁻ a, ENNReal.ofReal (g a + F a) ∂μ
      = ENNReal.ofReal (∫ a, (g a + F a) ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (hgi.add hFi)
      (Eventually.of_forall hnnF)).symm
  rw [hcvtF] at hDCT
  simp_rw [hcvt] at hDCT
  -- Apply `toReal` (finite everywhere) to recover convergence of the real integrals.
  have hToReal := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hDCT
  simp only [Function.comp_def] at hToReal
  rw [ENNReal.toReal_ofReal (integral_nonneg hnnF)] at hToReal
  simp_rw [ENNReal.toReal_ofReal (integral_nonneg (hnn _))] at hToReal
  -- Split `∫ (g + fₙ) = ∫ g + ∫ fₙ` and cancel the constant `∫ g`.
  simp_rw [integral_add hgi (hfi _)] at hToReal
  rw [integral_add hgi hFi] at hToReal
  have := hToReal.sub tendsto_const_nhds (b := ∫ a, g a ∂μ)
  simpa only [add_sub_cancel_left] using this

/-- **Dominated convergence theorem, via Fatou applied to `g − fₙ`.**

The lower half of the classical argument, symmetric to `dct_of_dominated`. The
nonnegative sequence `g − fₙ ≥ 0` is dominated by `2g` and converges to `g − F`;
Fatou's bracket gives `∫ (g − fₙ) → ∫ (g − F)`, and cancelling `∫ g` yields the
same conclusion `∫ fₙ → ∫ F`. Exposing this second bracket completes the explicit
`g ± fₙ` route. -/
theorem dct_of_dominated_sub
    {f : ℕ → α → ℝ} {F : α → ℝ} {g : α → ℝ}
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g) (hgi : Integrable g μ)
    (hbound : ∀ n a, |f n a| ≤ g a)
    (hconv : ∀ a, Tendsto (fun n => f n a) atTop (𝓝 (F a))) :
    Tendsto (fun n => ∫ a, f n a ∂μ) atTop (𝓝 (∫ a, F a ∂μ)) := by
  -- Reduce to `dct_of_dominated` applied to `-fₙ` (still dominated by `g`,
  -- converging to `-F`); the lower bracket `g - fₙ = g + (-fₙ)` is precisely the
  -- upper bracket of the negated sequence.
  have hneg : Tendsto (fun n => ∫ a, (-f n a) ∂μ) atTop (𝓝 (∫ a, (-F a) ∂μ)) :=
    dct_of_dominated (f := fun n a => -f n a) (F := fun a => -F a) (g := g)
      (fun n => (hf n).neg) hg hgi
      (fun n a => by simpa [abs_neg] using hbound n a)
      (fun a => (hconv a).neg)
  simp_rw [integral_neg] at hneg
  simpa using hneg.neg

end FatouLemmaOQ01OQ02OQ01
