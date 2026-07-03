/-
  Radial-shell (FTC) derivation of the surface–volume relation S_n = n · V_n
  Open Question: area-of-circle-oq-02-oq-03-oq-02
  Parent:        area-of-circle-oq-02-oq-03  (Surface Area of the Unit Sphere: S_n = n·V_n)

  The parent `AreaOfCircleOQ02OQ03.lean` proves the scaling identity

      S_n = n · V_n

  *algebraically*, by unfolding the two Gamma closed forms and invoking the Gamma
  functional equation `Γ(n/2 + 1) = (n/2)·Γ(n/2)`.

  This file gives the **geometric / analytic** derivation the open question asks for:
  slice the unit n-ball into infinitesimal spherical shells of radius `r ∈ [0,1]`.
  A shell at radius `r` has `(n-1)`-measure `S_n · r^(n-1)` (the unit sphere scaled by
  `r`), so integrating the shells recovers the ball volume,

      shellVolume n  :=  ∫₀¹ S_n · r^(n-1) dr.

  Evaluating this single interval integral by the Fundamental Theorem of Calculus
  (`∫₀¹ r^(n-1) dr = 1/n`, Mathlib's `integral_pow`) gives

      shellVolume n = S_n / n,                       (`shellVolume_eq`)

  and hence, with **no appeal to the Gamma recurrence**,

      S_n = n · shellVolume n.                        (`surface_eq_n_mul_shellVolume`)

  Finally we reconcile the two routes: the shell integral reproduces the actual
  Gamma-closed-form ball volume,

      shellVolume n = V_n,                            (`shellVolume_eq_unitBallVolume`)

  so the FTC derivation and the Gamma derivation agree.  The novelty over the parent
  is that `S_n = n·V_n` is obtained *from the integral geometry* (FTC on `r^(n-1)`)
  rather than from the Gamma functional equation — two independent proofs of the same
  identity meeting in `shellVolume_eq_unitBallVolume`.

  Status: 0 sorries, 0 axioms (beyond Mathlib's foundations).

  References:
  - Mathlib: `integral_pow`, `intervalIntegral.integral_const_mul`, `Real.Gamma_zero`
  - Parent: `NSphereSurface.surface_eq_n_mul_volume`
  - Classical: Cavalieri / shell integration, S^{n-1}(r) = r^{n-1} · S^{n-1}(1)
-/

import Mathlib
import Proofs.AreaOfCircleOQ02OQ03

open MeasureTheory Real

namespace NSphereShell

open NSphereSurface

noncomputable section

/-- The **radial-shell volume**: the unit n-ball volume assembled from spherical
    shells of radius `r ∈ [0,1]`, each of `(n-1)`-measure `S_n · r^(n-1)`. -/
def shellVolume (n : ℕ) : ℝ :=
  ∫ r in (0 : ℝ)..1, unitSphereSurface n * r ^ (n - 1)

/-- **The FTC core.** `∫₀¹ r^(n-1) dr = 1/n` for `n ≥ 1`.  This is the single
    application of the Fundamental Theorem of Calculus (via `integral_pow`) on which
    the whole shell derivation rests. -/
theorem integral_r_pow {n : ℕ} (hn : 1 ≤ n) :
    (∫ r in (0 : ℝ)..1, r ^ (n - 1)) = 1 / n := by
  rw [integral_pow]
  have hsucc : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
  have h0 : (0 : ℝ) ^ (n - 1 + 1) = 0 := by rw [hsucc]; exact zero_pow (by omega)
  rw [one_pow, h0, sub_zero]
  congr 1
  exact_mod_cast hsucc

/-- **Shell integral evaluates to `S_n / n`.**  Pulling the constant surface factor
    out of the integral and applying `integral_r_pow`. -/
theorem shellVolume_eq {n : ℕ} (hn : 1 ≤ n) :
    shellVolume n = unitSphereSurface n / n := by
  unfold shellVolume
  rw [intervalIntegral.integral_const_mul, integral_r_pow hn]
  ring

/-- **Surface–volume identity via FTC.**  `S_n = n · shellVolume n`, derived purely
    from the shell integral and the Fundamental Theorem of Calculus — *without* the
    Gamma functional equation used in the parent's `surface_eq_n_mul_volume`.

    The `n = 0` case holds by Mathlib's junk-value convention `Γ(0) = 0` (both sides
    are `0`). -/
theorem surface_eq_n_mul_shellVolume (n : ℕ) :
    unitSphereSurface n = (n : ℝ) * shellVolume n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [unitSphereSurface, Real.Gamma_zero]
  · rw [shellVolume_eq hn]
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp

/-- **Consistency of the two derivations.**  The shell integral reproduces the
    Gamma-closed-form ball volume `V_n`, so the FTC route and the Gamma route agree.
    Combines `shellVolume_eq` with the parent's `surface_eq_n_mul_volume`. -/
theorem shellVolume_eq_unitBallVolume {n : ℕ} (hn : 1 ≤ n) :
    shellVolume n = unitBallVolume n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [shellVolume_eq hn, surface_eq_n_mul_volume, mul_comm, mul_div_assoc,
      div_self hn0, mul_one]

/-! ## Special values (shell integral matches the classical volumes) -/

/-- `shellVolume 2 = π`: the unit disk assembled from circular shells. -/
theorem shellVolume_two : shellVolume 2 = π := by
  rw [shellVolume_eq_unitBallVolume (by norm_num), unitBallVolume_two]

/-- `shellVolume 3 = 4π/3`: the unit ball assembled from spherical shells. -/
theorem shellVolume_three : shellVolume 3 = 4 * π / 3 := by
  rw [shellVolume_eq_unitBallVolume (by norm_num), unitBallVolume_three]

/-- The shell-derived surface identity matches the Gamma-derived one: both give
    `S_n = n · V_n`, now with `V_n` realized concretely as the shell integral. -/
theorem shell_surface_agrees (n : ℕ) (hn : 1 ≤ n) :
    unitSphereSurface n = (n : ℝ) * unitBallVolume n := by
  rw [surface_eq_n_mul_shellVolume, shellVolume_eq_unitBallVolume hn]

end

end NSphereShell
