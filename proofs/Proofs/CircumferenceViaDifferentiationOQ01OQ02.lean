/-
  OQ-01-OQ-02: L^p unit ball volume and the surface-derivative identity
  (circumference-via-differentiation-oq-01-oq-02)

  Open question (extension of the parent gallery entry
  `circumference-via-differentiation-oq-01`, "n-Dimensional Surface Area via
  Differentiation of Volume"):

    The unit ball in L^p has volume
        V_n(p) = 2^n · Γ(1/p + 1)^n / Γ(n/p + 1)               (Dirichlet)
    Does the "volume-derivative-equals-surface" identity dV/dr = surface area
    still hold for the L^p surface area when p ≠ 2?

  ── ANSWER (this session, ORIENT) ─────────────────────────────────────────────

  It depends on *which* surface measure is meant.

  1. VOLUME + SCALING (fully tractable in Mathlib v4.26).
     Mathlib already proves the closed form **and** the radial scaling in one
     lemma: `MeasureTheory.volume_sum_rpow_le` gives, for `1 ≤ p` and the closed
     L^p ball of radius `r` in `ι → ℝ` (`card ι = n`),

       volume {x | (∑ i, |x i|^p)^(1/p) ≤ r}
         = ofReal r ^ n * ofReal ((2 * Γ(1/p + 1))^n / Γ(n/p + 1)).

     At `r = 1` this is exactly the Dirichlet `V_n(p)` above, and the `r^n`
     factor is the scaling `Vol{‖x‖_p ≤ r} = V_n(p) · r^n`.  Hence
       dV/dr = n · V_n(p) · r^(n-1)                                          (★)
     by the power rule — proved below as `lpBallVolumeFn_hasDerivAt`, mirroring
     the parent's Euclidean `nBallVolumeFn_hasDerivAt`.

  2. WHICH "SURFACE AREA" DOES (★) EQUAL?  By the coarea formula for the radial
     function `ρ(x) = ‖x‖_p`,

       dV/dr = ∫_{‖x‖_p = r} 1 / |∇ρ(x)|  dℋ^{n-1}(x),                   (coarea)

     where `|∇ρ|` is the *Euclidean* gradient norm of the L^p norm.  On the unit
     sphere `∑ |x_i|^p = 1` one computes `∂ρ/∂x_i = sgn(x_i) |x_i|^{p-1}`, so

       |∇ρ|^2 = ∑ |x_i|^{2p-2},

     which is identically `1` on the sphere **iff p = 2** (then `2p-2 = p = 2`
     and `∑|x_i|^2 = 1`).  Therefore:

       • p = 2 : the coarea weight is `1`, so (★) equals the genuine Euclidean
                 Hausdorff `(n-1)`-surface measure of the sphere.  This is the
                 parent theorem.
       • p ≠ 2 : the weight `1/|∇ρ|` varies over the sphere, so (★) is a
                 `|∇ρ|^{-1}`-WEIGHTED surface integral, **not** the Euclidean
                 Hausdorff surface measure of `{‖x‖_p = r}`.

     Concrete witness (n = 2, p = 1, the L^1 "diamond"):
       V_2(1) = 2,  dV/dr|_{r=1} = 4,  but the Euclidean perimeter is `4·√2`.
       The coarea-weighted surface is `(4√2)/√2 = 4 = dV/dr`. ✔

     So the naive identity `dV/dr = Euclidean surface area` is **FALSE for every
     finite p ≠ 2** (it holds for p = 2, and degenerately a.e. for p = ∞, where
     `|∇‖·‖_∞| = 1` on the open faces of the cube).

  All three numeric claims are checked independently (stdlib, ALL PASS) in
  `research/problems/circumference-via-differentiation-oq-01-oq-02/verify_lp_ball.py`.

  ── Lean scope of this file ───────────────────────────────────────────────────

  • `lpUnitBallVolume`, `lpBallVolumeFn` are defined to match the closed form in
    `MeasureTheory.volume_sum_rpow_le` *verbatim*, so a future (Docker-enabled)
    session can discharge a `volume = lpBallVolumeFn` bridge by `rw` on that
    lemma plus `ENNReal.toReal` bookkeeping.
  • `lpBallVolumeFn_hasDerivAt` / `deriv_lpBallVolume` prove (★) — the power-rule
    derivative of the closed form — mirroring the verified parent OQ-01.
  • The SURFACE side is **blocked in Mathlib v4.26**: there is no coarea formula
    (no `Coarea` file; only `MeasureTheory/Measure/Hausdorff.lean`), so the
    weighted identity (coarea) cannot yet be stated faithfully in Lean.  The
    false Euclidean identity is recorded only as documentation, not as a theorem.

  Status: 0 axioms; the derivative theorem is the proven content.  Build-pending
  (authored under a Docker/Aristotle verification blackout) and intentionally
  UNREGISTERED in `Proofs/Proofs.lean` until it compiles in a live session.
-/

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic

open Real MeasureTheory

noncomputable section

namespace CircumferenceViaDifferentiationOQ01OQ02

-- ============================================================
-- L^p unit ball volume (matches `MeasureTheory.volume_sum_rpow_le`)
-- ============================================================

/-- The Lebesgue volume of the L^p unit ball in `ℝ^n` (Dirichlet closed form):
    `V_n(p) = (2 · Γ(1/p + 1))^n / Γ(n/p + 1)`.

    Written to match the constant in `MeasureTheory.volume_sum_rpow_le`
    (which states `volume {x | (∑ |x i|^p)^(1/p) ≤ r} =
    ofReal r ^ n * ofReal ((2 * Γ(1/p + 1))^n / Γ(n/p + 1))`). -/
def lpUnitBallVolume (n : ℕ) (p : ℝ) : ℝ :=
  (2 * Gamma (1 / p + 1)) ^ n / Gamma ((n : ℝ) / p + 1)

/-- The L^p ball volume as a function of radius: `V(r) = V_n(p) · r^n`,
    matching the `r^n` scaling factor of `MeasureTheory.volume_sum_rpow_le`. -/
def lpBallVolumeFn (n : ℕ) (p : ℝ) (r : ℝ) : ℝ := lpUnitBallVolume n p * r ^ n

/-- The L^p "surface constant" appearing in the derivative: `n · V_n(p)`. -/
def lpSurfaceConst (n : ℕ) (p : ℝ) : ℝ := (n : ℝ) * lpUnitBallVolume n p

/-- The L^p surface-derivative function `n · V_n(p) · r^(n-1)`. -/
def lpSurfaceFn (n : ℕ) (p : ℝ) (r : ℝ) : ℝ := lpSurfaceConst n p * r ^ (n - 1)

-- ============================================================
-- (★) The derivative identity dV/dr = n · V_n(p) · r^(n-1)
--      (power rule on the closed form; mirrors verified parent OQ-01)
-- ============================================================

/-- **Main theorem (★).** The L^p ball-volume function has derivative
    `n · V_n(p) · r^(n-1)` at every radius `r`.  This is `d/dr (V_n(p)·r^n)`,
    the same power-rule computation as the parent's Euclidean
    `nBallVolumeFn_hasDerivAt`; only the leading constant differs. -/
theorem lpBallVolumeFn_hasDerivAt (n : ℕ) (p : ℝ) (r : ℝ) :
    HasDerivAt (lpBallVolumeFn n p) (lpSurfaceFn n p r) r := by
  unfold lpBallVolumeFn lpSurfaceFn lpSurfaceConst
  have h := (hasDerivAt_pow n r).const_mul (lpUnitBallVolume n p)
  have heq : lpUnitBallVolume n p * (↑n * r ^ (n - 1)) =
             ↑n * lpUnitBallVolume n p * r ^ (n - 1) := by ring
  rwa [heq] at h

/-- The L^p ball-volume function is differentiable everywhere. -/
theorem lpBallVolumeFn_differentiable (n : ℕ) (p : ℝ) :
    Differentiable ℝ (lpBallVolumeFn n p) :=
  fun r => (lpBallVolumeFn_hasDerivAt n p r).differentiableAt

/-- The `deriv` of the L^p ball volume equals the surface-derivative function. -/
theorem deriv_lpBallVolume (n : ℕ) (p : ℝ) (r : ℝ) :
    deriv (lpBallVolumeFn n p) r = lpSurfaceFn n p r :=
  (lpBallVolumeFn_hasDerivAt n p r).deriv

/-- At the unit radius the derivative is exactly the surface constant `n·V_n(p)`. -/
theorem lpSurfaceFn_one (n : ℕ) (p : ℝ) :
    lpSurfaceFn n p 1 = lpSurfaceConst n p := by
  unfold lpSurfaceFn
  rw [one_pow, mul_one]

end CircumferenceViaDifferentiationOQ01OQ02
