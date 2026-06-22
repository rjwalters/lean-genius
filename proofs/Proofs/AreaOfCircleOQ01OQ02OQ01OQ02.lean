/-
  The Isoperimetric Ratio of the n-Ball
  Open Question: area-of-circle-oq-01-oq-02-oq-01-oq-02

  This entry formalizes the second open question of the parent
  "N-Dimensional Volume from Surface Area Integration":

    "Can the isoperimetric inequality be formalized using these
     volume/surface area definitions?"

  The classical isoperimetric inequality in dimension n states that for any
  reasonable body with surface area S and volume V,

        Sⁿ  ≥  (nⁿ · ω_n) · V^(n-1),

  with equality **if and only if** the body is a ball. Here
  ω_n = π^(n/2)/Γ(n/2+1) is the unit-ball volume and the optimal constant
  nⁿ·ω_n is the *isoperimetric constant* of n-dimensional space.

  The "≥, with equality iff ball" direction is a deep theorem of geometric
  measure theory (Brunn–Minkowski / spherical symmetrization) and is well
  beyond the scope of these elementary monomial definitions. What IS fully
  formalizable here — and what this file proves with 0 axioms / 0 sorries —
  is the *equality case* and the *scale invariance* that make the constant
  meaningful:

    • The n-ball SATURATES the bound:  S_n(r)ⁿ = (nⁿ·ω_n) · V_n(r)^(n-1)
      for every radius r (the isoperimetric deficit of a ball is 0).
    • The dimensionless isoperimetric quotient  Q_n(r) = S_n(r)ⁿ / V_n(r)^(n-1)
      is independent of the radius r and equals the constant nⁿ·ω_n.
    • The low-dimensional constants recover the textbook inequalities:
        n=2:  Q₂ = 4π   (the planar  L² ≥ 4π·A),
        n=3:  Q₃ = 36π  (the spatial A³ ≥ 36π·V²).

  Definitions match the parent file AreaOfCircleOQ01OQ02OQ01.lean and are
  reproduced here so the file is self-contained:
      V_n(r) = ω_n · r^n            (n-ball volume)
      S_n(r) = n · ω_n · r^(n-1)    ((n-1)-sphere surface area)

  Chain: area-of-circle → OQ01 (C = dA/dr) → OQ02 (A = ∫C)
         → OQ01 (V_n = ∫S_n) → OQ02 (isoperimetric ratio of the n-ball)
-/

import Mathlib

open Real

noncomputable section

namespace NBallIsoperimetric

/- ## Part I: Volume, Surface Area, and the Isoperimetric Constant -/

/-- The unit ball volume ω_n = π^(n/2) / Γ(n/2 + 1).
    Self-contained; matches AreaOfCircleOQ01OQ02OQ01.unitBallVolume. -/
def unitBallVolume (n : ℕ) : ℝ :=
  π ^ ((n : ℝ) / 2) / Gamma ((n : ℝ) / 2 + 1)

/-- The n-ball volume function V_n(r) = ω_n · r^n. -/
def nBallVol (n : ℕ) (r : ℝ) : ℝ :=
  unitBallVolume n * r ^ n

/-- The (n-1)-sphere surface area function S_n(r) = n · ω_n · r^(n-1). -/
def nSphereArea (n : ℕ) (r : ℝ) : ℝ :=
  n * unitBallVolume n * r ^ (n - 1)

/-- The isoperimetric constant of n-dimensional space: c_n = nⁿ · ω_n.
    This is the optimal constant in the inequality Sⁿ ≥ c_n · V^(n-1). -/
def isoperimetricConst (n : ℕ) : ℝ :=
  (n : ℝ) ^ n * unitBallVolume n

/-- The dimensionless isoperimetric quotient Q_n(r) = S_n(r)ⁿ / V_n(r)^(n-1). -/
def isoperimetricQuotient (n : ℕ) (r : ℝ) : ℝ :=
  nSphereArea n r ^ n / nBallVol n r ^ (n - 1)

/- ## Part II: Positivity -/

/-- ω_n > 0 for all n (positive numerator, positive Gamma value). -/
theorem unitBallVolume_pos (n : ℕ) : 0 < unitBallVolume n := by
  unfold unitBallVolume
  apply div_pos
  · exact rpow_pos_of_pos pi_pos _
  · exact Gamma_pos_of_pos (by positivity)

/-- The isoperimetric constant is positive (for n ≥ 1). -/
theorem isoperimetricConst_pos (n : ℕ) (hn : 1 ≤ n) : 0 < isoperimetricConst n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n from hn)
  exact mul_pos (pow_pos hnpos n) (unitBallVolume_pos n)

/-- V_n(r) > 0 for r > 0. -/
theorem nBallVol_pos (n : ℕ) {r : ℝ} (hr : 0 < r) : 0 < nBallVol n r :=
  mul_pos (unitBallVolume_pos n) (pow_pos hr n)

/- ## Part III: The n-Ball Saturates the Isoperimetric Inequality -/

/-- **KEY EQUALITY CASE.** The n-ball of radius r achieves equality in the
    isoperimetric inequality:  S_n(r)ⁿ = (nⁿ · ω_n) · V_n(r)^(n-1).

    The powers of r cancel exactly: S_n(r)ⁿ carries r^((n-1)·n) and
    V_n(r)^(n-1) carries r^(n·(n-1)). This holds for *every* radius — the
    defining feature of the optimal isoperimetric constant. -/
theorem ball_saturates_isoperimetric (n : ℕ) (hn : 1 ≤ n) (r : ℝ) :
    nSphereArea n r ^ n = isoperimetricConst n * nBallVol n r ^ (n - 1) := by
  unfold nSphereArea isoperimetricConst nBallVol
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
  ring

/-- The isoperimetric deficit of an n-ball is identically zero. -/
theorem ball_isoperimetric_deficit_zero (n : ℕ) (hn : 1 ≤ n) (r : ℝ) :
    nSphereArea n r ^ n - isoperimetricConst n * nBallVol n r ^ (n - 1) = 0 := by
  rw [ball_saturates_isoperimetric n hn r]; ring

/-- The n-ball meets the isoperimetric lower bound (trivially, with equality). -/
theorem ball_meets_isoperimetric_bound (n : ℕ) (hn : 1 ≤ n) (r : ℝ) :
    isoperimetricConst n * nBallVol n r ^ (n - 1) ≤ nSphereArea n r ^ n :=
  le_of_eq (ball_saturates_isoperimetric n hn r).symm

/- ## Part IV: Scale Invariance of the Isoperimetric Quotient -/

/-- **SCALE INVARIANCE.** For r > 0 the isoperimetric quotient
    Q_n(r) = S_n(r)ⁿ / V_n(r)^(n-1) equals the constant nⁿ · ω_n,
    independent of the radius r. -/
theorem isoperimetricQuotient_eq_const (n : ℕ) (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    isoperimetricQuotient n r = isoperimetricConst n := by
  unfold isoperimetricQuotient
  have hV : nBallVol n r ^ (n - 1) ≠ 0 := (pow_pos (nBallVol_pos n hr) _).ne'
  rw [div_eq_iff hV]
  exact ball_saturates_isoperimetric n hn r

/-- The isoperimetric quotient takes the same value at any two positive radii:
    Q_n(r₁) = Q_n(r₂). The ratio is genuinely a dimensionless invariant. -/
theorem isoperimetricQuotient_scale_invariant (n : ℕ) (hn : 1 ≤ n)
    {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    isoperimetricQuotient n r₁ = isoperimetricQuotient n r₂ := by
  rw [isoperimetricQuotient_eq_const n hn h₁, isoperimetricQuotient_eq_const n hn h₂]

/- ## Part V: Low-Dimensional Constants — Recovering the Classical Inequalities -/

/-- ω_1 = 2 (the interval [-1,1]). -/
theorem unitBallVolume_one : unitBallVolume 1 = 2 := by
  unfold unitBallVolume
  simp only [Nat.cast_one]
  rw [show (1 : ℝ)/2 + 1 = 3/2 from by ring]
  have h32 : Gamma (3/2 : ℝ) = √π / 2 := by
    have h := Gamma_add_one (show (1/2 : ℝ) ≠ 0 from by norm_num)
    rw [show (1 : ℝ)/2 + 1 = 3/2 from by ring] at h
    rw [h, Gamma_one_half_eq]; ring
  rw [h32, ← Real.sqrt_eq_rpow]
  have h : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  field_simp [h.ne']

/-- ω_2 = π (area of the unit disk). -/
theorem unitBallVolume_two : unitBallVolume 2 = π := by
  unfold unitBallVolume
  simp only [Nat.cast_ofNat]
  rw [show (2 : ℝ)/2 + 1 = 2 from by ring, show (2 : ℝ)/2 = 1 from by ring]
  rw [rpow_one, Gamma_two]
  simp

/-- ω_3 = 4π/3 (volume of the unit 3-ball). -/
theorem unitBallVolume_three : unitBallVolume 3 = 4 * π / 3 := by
  unfold unitBallVolume
  simp only [Nat.cast_ofNat]
  have h32 : Gamma (3/2 : ℝ) = √π / 2 := by
    have h := Gamma_add_one (show (1/2 : ℝ) ≠ 0 from by norm_num)
    rw [show (1 : ℝ)/2 + 1 = 3/2 from by ring] at h
    rw [h, Gamma_one_half_eq]; ring
  have h52 : Gamma (5/2 : ℝ) = 3 * √π / 4 := by
    have h := Gamma_add_one (show (3/2 : ℝ) ≠ 0 from by norm_num)
    rw [show (3 : ℝ)/2 + 1 = 5/2 from by ring] at h
    rw [h, h32]; ring
  rw [show (3 : ℝ)/2 + 1 = 5/2 from by ring, h52]
  rw [show (3 : ℝ)/2 = (1 : ℝ) + 1/2 from by ring]
  rw [rpow_add pi_pos, rpow_one, ← Real.sqrt_eq_rpow]
  have hpi : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  field_simp [hpi.ne']

/-- The 1-dimensional isoperimetric constant c₁ = 2. -/
theorem isoperimetricConst_one : isoperimetricConst 1 = 2 := by
  unfold isoperimetricConst
  rw [unitBallVolume_one]; norm_num

/-- The **planar** isoperimetric constant c₂ = 4π.
    This is the optimal constant in the classical inequality L² ≥ 4π·A
    relating the length L of a closed curve to the enclosed area A. -/
theorem isoperimetricConst_two : isoperimetricConst 2 = 4 * π := by
  unfold isoperimetricConst
  rw [unitBallVolume_two]; norm_num

/-- The **spatial** isoperimetric constant c₃ = 36π.
    This is the optimal constant in the classical inequality A³ ≥ 36π·V²
    relating the surface area A of a body to its volume V. -/
theorem isoperimetricConst_three : isoperimetricConst 3 = 36 * π := by
  unfold isoperimetricConst
  rw [unitBallVolume_three]; ring

/- ## Part VI: Worked Equalities in Low Dimensions -/

/-- Planar equality case: for the disk of radius r, (2πr)² = 4π·(πr²),
    i.e. circumference² = 4π · area. -/
theorem disk_saturates_planar (r : ℝ) :
    nSphereArea 2 r ^ 2 = 4 * π * nBallVol 2 r := by
  have h := ball_saturates_isoperimetric 2 (by norm_num) r
  rw [isoperimetricConst_two] at h
  simpa using h

/-- Spatial equality case: for the ball of radius r, (4πr²)³ = 36π·(4πr³/3)²,
    i.e. surface area³ = 36π · volume². -/
theorem ball_saturates_spatial (r : ℝ) :
    nSphereArea 3 r ^ 3 = 36 * π * nBallVol 3 r ^ 2 := by
  have h := ball_saturates_isoperimetric 3 (by norm_num) r
  rw [isoperimetricConst_three] at h
  simpa using h

end NBallIsoperimetric
