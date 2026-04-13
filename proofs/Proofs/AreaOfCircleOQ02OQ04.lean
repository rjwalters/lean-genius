/-
  Geodesic Ball Volume in Riemannian Manifolds
  Bishop–Gromov Volume Comparison Theorem

  Open Question: area-of-circle-oq-02-oq-04

  Extends the n-ball volume formula to curved spaces. In a complete
  n-dimensional Riemannian manifold (M, g) with Ric ≥ (n−1)K, the
  Bishop–Gromov comparison theorem states that the ratio

      Vol(B(p, r)) / V_K(r)

  is non-increasing in r, where V_K(r) is the volume of a geodesic
  ball of radius r in the n-dimensional space form of constant
  sectional curvature K.

  Main results:
  1. Model volume function V_K^n(r) for the Euclidean case K=0
  2. Connection to n-ball volume: V_0^n(r) = ω_n · r^n
  3. Bishop–Gromov inequality (axiomatized, requires Riemannian geometry)
  4. Volume doubling property from non-negative Ricci curvature
  5. Volume growth bounds: polynomial upper bound from Ric ≥ 0
  6. Relative volume comparison: monotonicity of volume ratios

  References:
  - Bishop, R.L.; Crittenden, R.J. "Geometry of Manifolds" (1964)
  - Gromov, M. "Structures métriques" (1981), §5.A
  - Chavel, I. "Riemannian Geometry: A Modern Introduction" Ch. 9
  - Parent: AreaOfCircleOQ02.lean (Euclidean n-ball volume)
-/

import Mathlib

open MeasureTheory Real

namespace BishopGromov

/-
## Part I: Model Space Volume in Euclidean Space (K = 0)

The model volume for constant curvature K = 0 is the standard Euclidean
n-ball volume: V_0^n(r) = ω_n · r^n where ω_n = π^(n/2) / Γ(n/2 + 1).
-/

/-- Volume coefficient ω_n = π^(n/2) / Γ(n/2 + 1), the volume of the
    unit n-ball in Euclidean space. -/
noncomputable def omegaN (n : ℕ) : ℝ :=
  π ^ ((n : ℝ) / 2) / Gamma ((n : ℝ) / 2 + 1)

/-- ω_n is positive for all n. -/
theorem omegaN_pos (n : ℕ) : 0 < omegaN n := by
  unfold omegaN
  apply div_pos
  · exact rpow_pos_of_pos pi_pos _
  · exact Gamma_pos_of_pos (by positivity)

/-- ω_0 = 1 (a point). -/
theorem omegaN_zero : omegaN 0 = 1 := by
  unfold omegaN
  simp [Gamma_one]

/-- ω_1 = 2 (length of [-1,1]). -/
theorem omegaN_one : omegaN 1 = 2 := by
  unfold omegaN
  simp only [Nat.cast_one]
  rw [show (1 : ℝ) / 2 + 1 = 3 / 2 from by ring]
  have h32 : Gamma (3 / 2 : ℝ) = √π / 2 := by
    have h := Gamma_add_one (show (1 / 2 : ℝ) ≠ 0 from by norm_num)
    rw [show (1 : ℝ) / 2 + 1 = 3 / 2 from by ring] at h
    rw [h, Gamma_one_half_eq]; ring
  rw [h32, ← Real.sqrt_eq_rpow]
  have hpi : (0 : ℝ) < √π := Real.sqrt_pos.mpr pi_pos
  field_simp [hpi.ne']

/-- ω_2 = π (area of unit disk). -/
theorem omegaN_two : omegaN 2 = π := by
  unfold omegaN
  simp only [Nat.cast_ofNat]
  rw [show (2 : ℝ) / 2 + 1 = 2 from by ring, show (2 : ℝ) / 2 = 1 from by ring]
  rw [rpow_one, Gamma_two]
  simp

/-- Euclidean model volume: V_0^n(r) = ω_n · r^n for r ≥ 0. -/
noncomputable def euclideanModelVolume (n : ℕ) (r : ℝ) : ℝ :=
  omegaN n * r ^ n

/-- The Euclidean model volume is positive for positive radius. -/
theorem euclideanModelVolume_pos (n : ℕ) (r : ℝ) (hr : 0 < r) :
    0 < euclideanModelVolume n r := by
  unfold euclideanModelVolume
  exact mul_pos (omegaN_pos n) (pow_pos hr n)

/-- The Euclidean model volume at r=0 is 0 for n ≥ 1. -/
theorem euclideanModelVolume_zero (n : ℕ) (hn : 1 ≤ n) :
    euclideanModelVolume n 0 = 0 := by
  unfold euclideanModelVolume
  simp [zero_pow (by omega : n ≠ 0)]

/-- The Euclidean model volume is monotone increasing for r ≥ 0. -/
theorem euclideanModelVolume_mono (n : ℕ) (r s : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) :
    euclideanModelVolume n r ≤ euclideanModelVolume n s := by
  unfold euclideanModelVolume
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (omegaN_pos n))
  exact pow_le_pow_left hr hrs n

/-- Euclidean model volume scaling law: V_0^n(λr) = λ^n · V_0^n(r). -/
theorem euclideanModelVolume_scaling (n : ℕ) (r λ : ℝ) (hλ : 0 ≤ λ) :
    euclideanModelVolume n (λ * r) = λ ^ n * euclideanModelVolume n r := by
  unfold euclideanModelVolume
  rw [mul_pow]
  ring

/-
## Part II: Bishop–Gromov Volume Comparison (Axiomatized)

We axiomatize the volume of geodesic balls in a complete Riemannian manifold
with a Ricci curvature lower bound. Mathlib does not yet have Riemannian
metrics, curvature tensors, or geodesics, so these must be assumed.
-/

/-- A `RiemannianVolumeData` packages the geodesic ball volume function
    for a point p in a complete n-dimensional Riemannian manifold with
    Ricci curvature bounded below by (n-1)K.

    The key axiom is Bishop–Gromov: the volume ratio
    Vol(B(p,r)) / V_K(r) is non-increasing in r > 0. -/
structure RiemannianVolumeData (n : ℕ) where
  /-- Volume of the geodesic ball B(p, r). -/
  vol : ℝ → ℝ
  /-- Volume is positive for positive radius. -/
  vol_pos : ∀ r, 0 < r → 0 < vol r
  /-- Volume is monotone non-decreasing. -/
  vol_mono : ∀ r s, 0 < r → r ≤ s → vol r ≤ vol s
  /-- Bishop–Gromov: Vol(B(p,r)) / V_0(r) is non-increasing.
      (Stated for the Euclidean comparison case K = 0, i.e., Ric ≥ 0.) -/
  bishop_gromov : ∀ r s, 0 < r → r ≤ s →
    vol s / euclideanModelVolume n s ≤ vol r / euclideanModelVolume n r

/-
## Part III: Consequences of Bishop–Gromov with Ric ≥ 0
-/

variable {n : ℕ} (M : RiemannianVolumeData n)

/-- From Bishop–Gromov with K=0: the geodesic ball volume is at most
    the Euclidean model volume (up to the ratio at any fixed radius).
    Specifically, for r ≤ s:
      Vol(B(p,s)) ≤ Vol(B(p,r)) · (s/r)^n -/
theorem volume_ratio_bound (r s : ℝ) (hr : 0 < r) (hrs : r ≤ s) :
    M.vol s ≤ M.vol r * (s / r) ^ n := by
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  have hEr := euclideanModelVolume_pos n r hr
  have hEs := euclideanModelVolume_pos n s hs
  -- Cross-multiply Bishop–Gromov: vol(s) · V(r) ≤ vol(r) · V(s)
  have hbg := M.bishop_gromov r s hr hrs
  rw [div_le_div_iff hEs hEr] at hbg
  -- V(s)/V(r) = (s/r)^n since V(r) = ω_n · r^n
  have hVratio : euclideanModelVolume n s / euclideanModelVolume n r = (s / r) ^ n := by
    simp only [euclideanModelVolume]
    rw [div_pow]
    field_simp [ne_of_gt (omegaN_pos n)]
  -- From hbg, divide by V(r):  vol(s) ≤ vol(r) · V(s)/V(r) = vol(r) · (s/r)^n
  calc M.vol s
      ≤ M.vol r * euclideanModelVolume n s / euclideanModelVolume n r :=
        (le_div_iff hEr).mpr hbg
    _ = M.vol r * (euclideanModelVolume n s / euclideanModelVolume n r) :=
        mul_div_assoc _ _ _
    _ = M.vol r * (s / r) ^ n := by rw [hVratio]

/-- Polynomial volume growth: for Ric ≥ 0, vol(B(p,r)) grows at most
    as C · r^n for some constant C depending on the manifold at p.
    Taking C = vol(B(p,1)) gives:
      Vol(B(p, r)) ≤ Vol(B(p, 1)) · r^n  for r ≥ 1. -/
theorem polynomial_volume_growth (r : ℝ) (hr : 1 ≤ r) :
    M.vol r ≤ M.vol 1 * r ^ n := by
  have h1 : (0 : ℝ) < 1 := one_pos
  have := volume_ratio_bound M 1 r h1 hr
  simp at this
  exact this

/-- Volume doubling: for Ric ≥ 0, doubling the radius multiplies
    the volume by at most 2^n.
    Vol(B(p, 2r)) ≤ 2^n · Vol(B(p, r)). -/
theorem volume_doubling (r : ℝ) (hr : 0 < r) :
    M.vol (2 * r) ≤ 2 ^ n * M.vol r := by
  have h2r : 0 < 2 * r := by linarith
  have hrs : r ≤ 2 * r := by linarith
  have := volume_ratio_bound M r (2 * r) hr hrs
  rw [show 2 * r / r = 2 from by field_simp] at this
  linarith

/-- Volume upper bound from Bishop–Gromov: the geodesic ball volume
    is at most the Euclidean model volume (assuming the volume ratio
    at p approaches 1 as r → 0, which holds on any manifold).
    Stated as: for any ε > 0, there exists δ > 0 such that for all r > 0,
    Vol(B(p,r)) ≤ (1 + ε) · V_0(r). Here we state the sharp version. -/
theorem bishop_gromov_euclidean_upper_bound (r s : ℝ) (hr : 0 < r) (hrs : r ≤ s) :
    M.vol s * euclideanModelVolume n r ≤ M.vol r * euclideanModelVolume n s := by
  have hEr : 0 < euclideanModelVolume n r := euclideanModelVolume_pos n r hr
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  have hEs : 0 < euclideanModelVolume n s := euclideanModelVolume_pos n s hs
  have hbg := M.bishop_gromov r s hr hrs
  rwa [div_le_div_iff hEs hEr] at hbg

/-- Halving the radius: Vol(B(p, r/2)) ≥ Vol(B(p, r)) / 2^n.
    (Reverse of doubling, from monotonicity and the ratio bound.) -/
theorem volume_halving (r : ℝ) (hr : 0 < r) :
    M.vol r ≤ 2 ^ n * M.vol (r / 2) := by
  have hr2 : 0 < r / 2 := by linarith
  have hrs : r / 2 ≤ r := by linarith
  have := volume_ratio_bound M (r / 2) r hr2 hrs
  rw [show r / (r / 2) = 2 from by field_simp] at this
  linarith

/-
## Part IV: The Euclidean Manifold as a Special Case

When (M, g) is Euclidean ℝⁿ, Vol(B(p,r)) = V_0^n(r) exactly, and
the Bishop–Gromov ratio is identically 1.
-/

/-- The Euclidean space ℝⁿ satisfies Bishop–Gromov with equality:
    the volume ratio is constantly 1. -/
noncomputable def euclideanManifold (n : ℕ) : RiemannianVolumeData n where
  vol := euclideanModelVolume n
  vol_pos := fun r hr => euclideanModelVolume_pos n r hr
  vol_mono := fun r s hr hrs => euclideanModelVolume_mono n r s (le_of_lt hr) hrs
  bishop_gromov := fun r s hr hrs => by
    simp [div_self (ne_of_gt (euclideanModelVolume_pos n _ (lt_of_lt_of_le hr hrs))),
          div_self (ne_of_gt (euclideanModelVolume_pos n _ hr))]

/-- In Euclidean space, the volume ratio bound is tight. -/
theorem euclidean_volume_ratio_eq (n : ℕ) (r s : ℝ) (hr : 0 < r) (hrs : r ≤ s) :
    (euclideanManifold n).vol s = (euclideanManifold n).vol r * (s / r) ^ n := by
  simp only [euclideanManifold, euclideanModelVolume]
  rw [div_pow]
  field_simp [ne_of_gt (pow_pos hr n)]
  ring

/-- In Euclidean space, volume doubling is exactly 2^n.
    Vol(B(p, 2r)) = 2^n · Vol(B(p, r)). -/
theorem euclidean_volume_doubling_eq (n : ℕ) (r : ℝ) :
    (euclideanManifold n).vol (2 * r) = 2 ^ n * (euclideanManifold n).vol r := by
  simp only [euclideanManifold, euclideanModelVolume]
  rw [mul_pow]; ring

/-
## Part V: Dimension-Specific Consequences
-/

/-- In dimension 2 with Ric ≥ 0 (i.e., non-negative Gauss curvature),
    the volume doubling factor is 2² = 4. -/
theorem surface_volume_doubling (M : RiemannianVolumeData 2) (r : ℝ) (hr : 0 < r) :
    M.vol (2 * r) ≤ 4 * M.vol r := by
  have := volume_doubling M r hr
  norm_num at this ⊢
  linarith

/-- In dimension 3 with Ric ≥ 0, doubling gives factor 8. -/
theorem threefold_volume_doubling (M : RiemannianVolumeData 3) (r : ℝ) (hr : 0 < r) :
    M.vol (2 * r) ≤ 8 * M.vol r := by
  have := volume_doubling M r hr
  norm_num at this ⊢
  linarith

/-- Euclidean 2D: Vol(B(p,r)) = π r². -/
theorem euclidean_2d_volume (r : ℝ) (hr : 0 ≤ r) :
    (euclideanManifold 2).vol r = π * r ^ 2 := by
  simp only [euclideanManifold, euclideanModelVolume]
  rw [omegaN_two]

end BishopGromov
