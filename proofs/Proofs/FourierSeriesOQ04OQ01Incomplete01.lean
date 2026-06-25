/-
# Fourier Series OQ-04-OQ-01-incomplete-01: Spherical Parseval / energy convergence on 𝕋²

## Research question (this entry)

The parent entry `FourierSeriesOQ04OQ01` axiomatises the **2D Carleson
spherical-summation conjecture** (the open a.e.-convergence statement
`carleson_2d_sph`) and proves, sorry-free, the unconditional **L²-norm**
companion `sphPartialSum_L2_norm_converge`. That norm statement says the
spherical partial sums `S_R^{sph} f` converge *to f* in `L²`.

This child entry proves the **Parseval / energy** companions of the *same*
spherical exhaustion — the statements about the coefficients themselves rather
than the reconstructed function. Concretely, for `f, g ∈ L²(𝕋²)` and the disc
exhaustion `latticeDisc R = {k ∈ ℤ² : k₀² + k₁² ≤ R²}`:

1. **Spherical Bessel inequality** — for every `R`,
   `∑_{|k| ≤ R} |f̂(k)|² ≤ ∫ |f|²` (the disc energy never exceeds total energy).
2. **Spherical Parseval (norm form)** — `∑_{|k| ≤ R} |f̂(k)|² → ∫ |f|²` as
   `R → ∞` (the disc energy *exhausts* the total energy).
3. **Spherical Parseval (inner-product form)** —
   `∑_{|k| ≤ R} conj(f̂(k)) ĝ(k) → ∫ conj(f) g` as `R → ∞`.

## Why this is genuine, not a restatement of Mathlib

Mathlib's `UnitAddTorus.hasSum_sq_mFourierCoeff` /
`hasSum_prod_mFourierCoeff` give Parseval over the **abstract `Finset`-directed**
filter `atTop : Filter (Finset (ℤ²))` — a `HasSum` over arbitrary finite
sub-collections of frequencies. They say *nothing* about the **geometric
real-parameter** exhaustion by Euclidean discs `|k| ≤ R`, which is the object
the Bochner–Riesz / Carleson problem is actually about.

The bridge is the parent's cofinality lemma `latticeDisc_eventually_supset`
(every finite frequency set is eventually swallowed by some disc), which
upgrades `Tendsto latticeDisc atTop atTop`; composing the `Finset`-directed
`HasSum` with this gives the `R → ∞` spherical limit. The Bessel inequality is
the finite-`R` truncation of the same `HasSum` (partial sum ≤ total, since the
summands are nonnegative).

These are the natural quantitative invariants that any *positive* resolution of
`carleson_2d_sph` must respect, and they hold unconditionally.

## Architecture

Imports the parent file and reuses its `multiFourierCoeff`, `latticeDisc`,
`mFourierCoeff_eq_multiFourierCoeff` bridge, and `latticeDisc_eventually_supset`
cofinality. No new axioms; no sorries.

## References
- Parent: `Proofs/FourierSeriesOQ04OQ01.lean`.
- Mathlib: `Mathlib.Analysis.Fourier.AddCircleMulti`
  (`hasSum_sq_mFourierCoeff`, `hasSum_prod_mFourierCoeff`).
-/

import Mathlib
import Proofs.FourierSeriesOQ04OQ01

namespace FourierSeriesOQ04OQ01Incomplete01

open MeasureTheory Complex Filter Topology
open scoped ENNReal NNReal Real ComplexConjugate
open FourierSeriesOQ04OQ01

noncomputable section

set_option maxHeartbeats 400000

/-- The disc energy `∑_{|k| ≤ R} |f̂(k)|²` agrees with the same finset sum of
    the engine's coefficient functional, for the `Lp` representative `fhat`. A
    convenience repackaging of the parent bridge `mFourierCoeff_eq_multiFourierCoeff`
    applied termwise. -/
theorem sq_coeff_funext
    (f : T2 → ℂ) (fhat : Lp ℂ 2 haarT2) (hfhat : (fhat : T2 → ℂ) =ᵐ[haarT2] f) :
    (fun k : Fin 2 → ℤ => ‖UnitAddTorus.mFourierCoeff (fhat : T2 → ℂ) k‖ ^ 2)
      = fun k => ‖multiFourierCoeff f k‖ ^ 2 := by
  funext k
  rw [mFourierCoeff_eq_multiFourierCoeff f fhat hfhat k]

/-- **Parseval `HasSum` for `multiFourierCoeff`** (norm form), on the `Finset`
    filter. The engine's `hasSum_sq_mFourierCoeff` transported across the
    coefficient bridge and the `fhat =ᵐ f` integral identification. This is the
    common engine for both the spherical Bessel inequality and the spherical
    Parseval limit below. -/
theorem hasSum_sq_multiFourierCoeff (f : T2 → ℂ) (hf : MemLp f 2 haarT2) :
    HasSum (fun k : Fin 2 → ℤ => ‖multiFourierCoeff f k‖ ^ 2)
      (∫ x, ‖f x‖ ^ 2 ∂haarT2) := by
  classical
  set fhat : Lp ℂ 2 haarT2 := hf.toLp f with hfhatdef
  have hfhat : (fhat : T2 → ℂ) =ᵐ[haarT2] f := hf.coeFn_toLp
  -- Mathlib Parseval (norm form) for the `Lp` representative `fhat`.
  have hHS : HasSum (fun k : Fin 2 → ℤ =>
      ‖UnitAddTorus.mFourierCoeff (fhat : T2 → ℂ) k‖ ^ 2)
      (∫ t, ‖(fhat : T2 → ℂ) t‖ ^ 2 ∂haarT2) :=
    UnitAddTorus.hasSum_sq_mFourierCoeff fhat
  -- Bridge the total energy integral from `fhat` to `f`.
  have hintegral : (∫ t, ‖(fhat : T2 → ℂ) t‖ ^ 2 ∂haarT2)
      = ∫ x, ‖f x‖ ^ 2 ∂haarT2 := by
    refine integral_congr_ae ?_
    filter_upwards [hfhat] with t ht
    rw [ht]
  -- Bridge the summand from the engine functional to `multiFourierCoeff f`.
  rw [sq_coeff_funext f fhat hfhat, hintegral] at hHS
  exact hHS

/-- **Spherical Bessel inequality** on `𝕋²`. For `f ∈ L²(𝕋²)` and every radius
    `R`, the energy carried by the frequencies inside the disc `|k| ≤ R` never
    exceeds the total energy `∫ |f|²`:
    `∑_{|k| ≤ R} |f̂(k)|² ≤ ∫ |f|²`. -/
theorem sphPartialSum_energy_le
    (f : T2 → ℂ) (hf : MemLp f 2 haarT2) (R : ℝ) :
    ∑ k ∈ latticeDisc R, ‖multiFourierCoeff f k‖ ^ 2
      ≤ ∫ x, ‖f x‖ ^ 2 ∂haarT2 :=
  sum_le_hasSum (latticeDisc R) (fun k _ => sq_nonneg _)
    (hasSum_sq_multiFourierCoeff f hf)

/-- **Spherical Parseval, norm form**, on `𝕋²`. For `f ∈ L²(𝕋²)`, the disc
    energy `∑_{|k| ≤ R} |f̂(k)|²` converges to the total energy `∫ |f|²` as
    `R → ∞`. This is the energy companion of the parent's
    `sphPartialSum_L2_norm_converge`: where that says the *function* is
    recovered in `L²`, this says the *coefficient energy* is exhausted by the
    geometric disc summation. -/
theorem sphPartialSum_energy_converge
    (f : T2 → ℂ) (hf : MemLp f 2 haarT2) :
    Tendsto (fun R : ℝ => ∑ k ∈ latticeDisc R, ‖multiFourierCoeff f k‖ ^ 2)
      atTop (𝓝 (∫ x, ‖f x‖ ^ 2 ∂haarT2)) := by
  -- The disc exhaustion is cofinal in the `Finset` filter (parent S9 cofinality).
  have htend : Tendsto latticeDisc (atTop : Filter ℝ) atTop := by
    rw [tendsto_atTop_atTop]
    intro S
    obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp (latticeDisc_eventually_supset S)
    exact ⟨R₀, fun R hR => Finset.le_iff_subset.mpr (hR₀ R hR)⟩
  -- View the `Finset`-directed Parseval `HasSum` as a `Tendsto` and compose.
  have hHS : Tendsto
      (fun s : Finset (Fin 2 → ℤ) => ∑ k ∈ s, ‖multiFourierCoeff f k‖ ^ 2)
      atTop (𝓝 (∫ x, ‖f x‖ ^ 2 ∂haarT2)) :=
    hasSum_sq_multiFourierCoeff f hf
  exact hHS.comp htend

/-- **Spherical Parseval, inner-product form**, on `𝕋²`. For `f, g ∈ L²(𝕋²)`,
    the disc-truncated Hermitian pairing of Fourier coefficients converges to
    the `L²` inner product `∫ conj(f) g` as `R → ∞`:
    `∑_{|k| ≤ R} conj(f̂(k)) ĝ(k) → ∫ conj(f) g`. -/
theorem sphPartialSum_inner_parseval
    (f g : T2 → ℂ) (hf : MemLp f 2 haarT2) (hg : MemLp g 2 haarT2) :
    Tendsto (fun R : ℝ => ∑ k ∈ latticeDisc R,
        conj (multiFourierCoeff f k) * multiFourierCoeff g k)
      atTop (𝓝 (∫ x, conj (f x) * g x ∂haarT2)) := by
  classical
  set fhat : Lp ℂ 2 haarT2 := hf.toLp f with hfhatdef
  set ghat : Lp ℂ 2 haarT2 := hg.toLp g with hghatdef
  have hfhat : (fhat : T2 → ℂ) =ᵐ[haarT2] f := hf.coeFn_toLp
  have hghat : (ghat : T2 → ℂ) =ᵐ[haarT2] g := hg.coeFn_toLp
  -- Mathlib Parseval (inner-product form) for the `Lp` representatives.
  have hHS0 : HasSum (fun k : Fin 2 → ℤ =>
      conj (UnitAddTorus.mFourierCoeff (fhat : T2 → ℂ) k)
        * UnitAddTorus.mFourierCoeff (ghat : T2 → ℂ) k)
      (∫ t, conj ((fhat : T2 → ℂ) t) * (ghat : T2 → ℂ) t ∂haarT2) :=
    UnitAddTorus.hasSum_prod_mFourierCoeff fhat ghat
  -- Bridge each coefficient functional to `multiFourierCoeff`.
  have hfun : (fun k : Fin 2 → ℤ =>
      conj (UnitAddTorus.mFourierCoeff (fhat : T2 → ℂ) k)
        * UnitAddTorus.mFourierCoeff (ghat : T2 → ℂ) k)
      = fun k => conj (multiFourierCoeff f k) * multiFourierCoeff g k := by
    funext k
    rw [mFourierCoeff_eq_multiFourierCoeff f fhat hfhat k,
        mFourierCoeff_eq_multiFourierCoeff g ghat hghat k]
  -- Bridge the inner-product integral from `(fhat, ghat)` to `(f, g)`.
  have hintegral : (∫ t, conj ((fhat : T2 → ℂ) t) * (ghat : T2 → ℂ) t ∂haarT2)
      = ∫ x, conj (f x) * g x ∂haarT2 := by
    refine integral_congr_ae ?_
    filter_upwards [hfhat, hghat] with t htf htg
    rw [htf, htg]
  rw [hfun, hintegral] at hHS0
  -- Disc cofinality, then compose the `Finset`-directed limit to `R → ∞`.
  have htend : Tendsto latticeDisc (atTop : Filter ℝ) atTop := by
    rw [tendsto_atTop_atTop]
    intro S
    obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp (latticeDisc_eventually_supset S)
    exact ⟨R₀, fun R hR => Finset.le_iff_subset.mpr (hR₀ R hR)⟩
  have hHS : Tendsto
      (fun s : Finset (Fin 2 → ℤ) =>
        ∑ k ∈ s, conj (multiFourierCoeff f k) * multiFourierCoeff g k)
      atTop (𝓝 (∫ x, conj (f x) * g x ∂haarT2)) := hHS0
  exact hHS.comp htend

/-- Sanity check: the spherical energy of the zero function is zero (and the
    limit statement is consistent — total energy `∫ ‖0‖² = 0`). -/
theorem energy_zero (R : ℝ) :
    ∑ k ∈ latticeDisc R, ‖multiFourierCoeff (fun _ : T2 => (0 : ℂ)) k‖ ^ 2 = 0 := by
  simp [multiFourierCoeff_zero]

end

end FourierSeriesOQ04OQ01Incomplete01
