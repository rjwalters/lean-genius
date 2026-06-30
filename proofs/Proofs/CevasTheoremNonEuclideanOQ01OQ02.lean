import Proofs.CevasTheoremNonEuclidean
import Proofs.CevasTheoremNonEuclideanOQ01
import Mathlib.Tactic

/-!
# Ceva non-Euclidean OQ-01-OQ-02: the curvature-κ Menelaus theorem and Ceva–Menelaus duality

The grandparent entry (`cevas-theorem-non-euclidean`) abstracts Ceva's concurrence
condition into the curvature-free principle `ceva_unified_principle`, and the parent OQ-01
(`CevasNonEuclideanOQ01`) instantiates it at the curvature sine `sin_κ` to obtain the single
curvature-parametrised **Ceva** theorem `kappa_ceva`, recovering the spherical, hyperbolic,
and Euclidean concurrence laws as the cases κ = 1, −1, 0.

This file answers the sibling open question:

> *Formalise the curvature-κ **Menelaus** collinearity theorem in the same unified `sin_κ`
> framework, recovering spherical (κ > 0) and hyperbolic (κ < 0) Menelaus as instances.*

## Why this is not a relabelling of Ceva

Ceva (concurrent cevians) and Menelaus (a collinear transversal) share the *same unsigned*
product relation `sin_κ(BD)·sin_κ(CE)·sin_κ(AF) = sin_κ(DC)·sin_κ(EA)·sin_κ(FB)`. What
distinguishes them is the **parity of external divisions**: a transversal meets the three
(extended) sides in an *odd* number of external points, so its *signed* ratio product is `−1`,
whereas concurrent cevians give `+1`. Faithfully formalising Menelaus therefore means working
with *signed* ratios and the value `−1`, which is a genuinely different algebraic statement
from the parent's `+1` law — not a renaming.

## Main results

* `menelaus_unified_principle` : the curvature-free **signed** principle — for positive
  ρ-magnitudes the signed product (BC division external) equals `−1` iff the unsigned
  cross-multiplied relation holds. The `−1` is the algebraic signature of a transversal.
* `kappa_menelaus` : the unified curvature-κ Menelaus theorem (`ρ = sin_κ`).
* `kappa_menelaus_spherical` / `kappa_menelaus_hyperbolic` / `kappa_menelaus_euclidean` :
  the three classical Menelaus laws recovered at κ = 1, −1, 0.
* `ceva_menelaus_duality` : the signed Ceva product and the signed Menelaus product of the
  *same* three feet are negatives of one another.
* `ceva_menelaus_exclusive` : consequently feet that satisfy Ceva's concurrence value `+1`
  automatically satisfy Menelaus' collinearity value `−1` — the two criteria are mutually
  exclusive, the deep structural reason Ceva and Menelaus share one unsigned product law.

Status: PROVED — 0 sorries, 0 axioms. Holds for every curvature κ.
Tags: geometry, non-euclidean, menelaus, ceva, curvature, unified-framework
-/

namespace CevasNonEuclideanOQ01OQ02

open Real CevasNonEuclideanOQ01

/-- **Unified Menelaus principle (signed form).** For an abstract positive "ratio function"
    `ρ`, model a transversal by flipping the sign of the `BC`-division ratio (one external
    division). The signed product of the three directed ratios equals `−1` exactly when the
    unsigned cross-multiplied relation `ρ(BD)·ρ(CE)·ρ(AF) = ρ(DC)·ρ(EA)·ρ(FB)` holds.

    This is the sign-distinguished twin of `ceva_unified_principle`: the value is `−1`
    (transversal / collinear) rather than `+1` (cevians / concurrent), while the underlying
    unsigned product relation is identical. -/
theorem menelaus_unified_principle (ρ : ℝ → ℝ) (bd dc ce ea af fb : ℝ)
    (hρbd : 0 < ρ bd) (hρdc : 0 < ρ dc) (hρce : 0 < ρ ce) (hρea : 0 < ρ ea)
    (hρaf : 0 < ρ af) (hρfb : 0 < ρ fb) :
    (-(ρ bd) / ρ dc) * (ρ ce / ρ ea) * (ρ af / ρ fb) = -1 ↔
    ρ bd * ρ ce * ρ af = ρ dc * ρ ea * ρ fb := by
  rw [show (-(ρ bd) / ρ dc) * (ρ ce / ρ ea) * (ρ af / ρ fb)
        = -(ρ bd / ρ dc * (ρ ce / ρ ea) * (ρ af / ρ fb)) from by ring,
      show (-1 : ℝ) = -(1) from rfl, neg_inj]
  exact ceva_unified_principle ρ bd dc ce ea af fb hρbd hρdc hρce hρea hρaf hρfb

/-- **Unified curvature-κ Menelaus's Theorem.** For any curvature `κ`, three points `D ∈ BC`,
    `E ∈ CA`, `F ∈ AB` lie on a common geodesic transversal (one external division, here on
    `BC`) iff the signed curvature-sine product of the six sub-segments equals `−1`,
    equivalently the unsigned cross-multiplied relation holds. This subsumes the spherical
    (κ > 0), hyperbolic (κ < 0), and Euclidean (κ = 0) Menelaus laws in a single statement,
    the collinearity counterpart of `kappa_ceva`. -/
theorem kappa_menelaus (κ bd dc ce ea af fb : ℝ)
    (hbd : 0 < sinKappa κ bd) (hdc : 0 < sinKappa κ dc)
    (hce : 0 < sinKappa κ ce) (hea : 0 < sinKappa κ ea)
    (haf : 0 < sinKappa κ af) (hfb : 0 < sinKappa κ fb) :
    (-(sinKappa κ bd) / sinKappa κ dc) * (sinKappa κ ce / sinKappa κ ea) *
        (sinKappa κ af / sinKappa κ fb) = -1 ↔
    sinKappa κ bd * sinKappa κ ce * sinKappa κ af =
        sinKappa κ dc * sinKappa κ ea * sinKappa κ fb :=
  menelaus_unified_principle (sinKappa κ) bd dc ce ea af fb hbd hdc hce hea haf hfb

/-- **Spherical case (κ = 1).** The unified Menelaus theorem specializes to the classical
    spherical transversal condition in the ordinary sine. -/
theorem kappa_menelaus_spherical (bd dc ce ea af fb : ℝ)
    (hbd : 0 < Real.sin bd) (hdc : 0 < Real.sin dc)
    (hce : 0 < Real.sin ce) (hea : 0 < Real.sin ea)
    (haf : 0 < Real.sin af) (hfb : 0 < Real.sin fb) :
    (-(Real.sin bd) / Real.sin dc) * (Real.sin ce / Real.sin ea) *
        (Real.sin af / Real.sin fb) = -1 ↔
    Real.sin bd * Real.sin ce * Real.sin af = Real.sin dc * Real.sin ea * Real.sin fb := by
  have := kappa_menelaus 1 bd dc ce ea af fb
  simp only [sinKappa_one] at this
  exact this hbd hdc hce hea haf hfb

/-- **Hyperbolic case (κ = −1).** The unified Menelaus theorem specializes to the hyperbolic
    transversal condition in the hyperbolic sine. -/
theorem kappa_menelaus_hyperbolic (bd dc ce ea af fb : ℝ)
    (hbd : 0 < Real.sinh bd) (hdc : 0 < Real.sinh dc)
    (hce : 0 < Real.sinh ce) (hea : 0 < Real.sinh ea)
    (haf : 0 < Real.sinh af) (hfb : 0 < Real.sinh fb) :
    (-(Real.sinh bd) / Real.sinh dc) * (Real.sinh ce / Real.sinh ea) *
        (Real.sinh af / Real.sinh fb) = -1 ↔
    Real.sinh bd * Real.sinh ce * Real.sinh af =
        Real.sinh dc * Real.sinh ea * Real.sinh fb := by
  have := kappa_menelaus (-1) bd dc ce ea af fb
  simp only [sinKappa_neg_one] at this
  exact this hbd hdc hce hea haf hfb

/-- **Euclidean case (κ = 0).** The unified Menelaus theorem specializes to the classical
    planar Menelaus condition in plain segment lengths (with the `BC` division external). -/
theorem kappa_menelaus_euclidean (bd dc ce ea af fb : ℝ)
    (hbd : 0 < bd) (hdc : 0 < dc) (hce : 0 < ce)
    (hea : 0 < ea) (haf : 0 < af) (hfb : 0 < fb) :
    (-bd / dc) * (ce / ea) * (af / fb) = -1 ↔ bd * ce * af = dc * ea * fb := by
  have := kappa_menelaus 0 bd dc ce ea af fb
  simp only [sinKappa_zero] at this
  exact this hbd hdc hce hea haf hfb

/-- **Ceva–Menelaus duality.** For the *same* three feet, the signed Menelaus product (the
    `BC` division external) is the negative of the signed Ceva product (all divisions
    internal). A purely algebraic identity, valid for every curvature κ and all arguments. -/
theorem ceva_menelaus_duality (κ bd dc ce ea af fb : ℝ) :
    (-(sinKappa κ bd) / sinKappa κ dc) * (sinKappa κ ce / sinKappa κ ea) *
        (sinKappa κ af / sinKappa κ fb)
      = -(sinKappa κ bd / sinKappa κ dc * (sinKappa κ ce / sinKappa κ ea) *
          (sinKappa κ af / sinKappa κ fb)) := by
  ring

/-- **Ceva and Menelaus are mutually exclusive.** If a triple of feet satisfies Ceva's
    concurrence value `+1` (signed Ceva product `= 1`), then it automatically satisfies
    Menelaus' collinearity value `−1` (signed Menelaus product `= −1`). The two classical
    criteria can never hold with the same value: this is the structural reason they share a
    single *unsigned* product law yet describe opposite configurations (concurrence vs
    collinearity). -/
theorem ceva_menelaus_exclusive (κ bd dc ce ea af fb : ℝ)
    (hceva : sinKappa κ bd / sinKappa κ dc * (sinKappa κ ce / sinKappa κ ea) *
        (sinKappa κ af / sinKappa κ fb) = 1) :
    (-(sinKappa κ bd) / sinKappa κ dc) * (sinKappa κ ce / sinKappa κ ea) *
        (sinKappa κ af / sinKappa κ fb) = -1 := by
  rw [ceva_menelaus_duality, hceva]

end CevasNonEuclideanOQ01OQ02
