import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-
# Hilbert metric, Birkhoff contraction, and Perron–Frobenius power iteration (2×2)

This file realizes openQuestions[3] of the gallery entry `hilbert-4`
(*Hilbert's 4th problem*): the bridge between the **Hilbert projective metric**
and **Perron–Frobenius theory**.  Birkhoff's theorem says a positive matrix
contracts the Hilbert (projective) metric, so by the Banach contraction-mapping
theorem its normalized power iteration converges geometrically to the
(positive, dominant) Perron eigenvector.

We formalize the **2×2 case**, where the geometry is one–dimensional: a positive
matrix `A = !![a, b; c, d]` (all entries `> 0`) acts on the projective coordinate
`t = x / y ∈ (0, ∞)` by the increasing **Möbius map**

  `φ(t) = (a·t + b) / (c·t + d)`.

The Hilbert metric on the positive ray is `d_H(t₁, t₂) = |log t₁ − log t₂|`, and
Birkhoff's theorem is the statement that `φ` strictly contracts `d_H`.  Instead of
the analytic (logistic-derivative) proof of the optimal contraction constant
`tanh(Δ/4)`, we use the **exact projective-dynamics identity** that is the
algebraic heart of the matter: a real Möbius map with two distinct real fixed
points is conjugate, via the cross-ratio coordinate, to multiplication by a
constant — its **multiplier** `ρ`.  For a positive matrix this multiplier is
exactly the eigenvalue ratio `ρ = λ₂ / λ₁`, with `|ρ| < 1`.

Concretely, the two fixed points of `φ` are the roots `t⋆ > 0 > t†` of
`c·t² + (d − a)·t − b = 0` (the two eigenvector ratios; `t⋆` is the Perron one,
since it is positive).  With the cross-ratio coordinate `g(t) = (t − t⋆)/(t − t†)`
we prove the **semiconjugacy**

  `g(φ(t)) = ρ · g(t)`,            `ρ = (a + d − √Δ)/(a + d + √Δ) = λ₂/λ₁`,

whence `g(φⁿ(t)) = ρⁿ · g(t) → 0`, and solving back for `φⁿ(t)` gives geometric
convergence `φⁿ(t) → t⋆`.  This is precisely Birkhoff's "the power iteration
converges to the Perron direction", with the contraction rate identified in
closed form.

Everything below is over `ℝ` and fully verified: 0 axioms, 0 sorries, no
`native_decide`.

References:
* Birkhoff, G. (1957). *Extensions of Jentzsch's theorem.* Trans. AMS 85.
* Bushell, P. (1973). *Hilbert's metric and positive contraction mappings.*
  Arch. Rational Mech. Anal. 52.
-/

namespace Hilbert4Birkhoff

open Filter Topology

/-- The Möbius action of `A = !![a,b;c,d]` on the projective coordinate `t`. -/
noncomputable def mobius (a b c d t : ℝ) : ℝ := (a * t + b) / (c * t + d)

/-- Discriminant of the fixed-point quadratic `c·t² + (d−a)·t − b`. -/
noncomputable def fpDisc (a b c d : ℝ) : ℝ := (d - a) ^ 2 + 4 * b * c

/-- The Perron (positive) fixed point of `φ`: the dominant eigenvector ratio. -/
noncomputable def perronRatio (a b c d : ℝ) : ℝ :=
  (a - d + Real.sqrt (fpDisc a b c d)) / (2 * c)

/-- The subdominant (negative) fixed point of `φ`: the other eigenvector ratio. -/
noncomputable def subRatio (a b c d : ℝ) : ℝ :=
  (a - d - Real.sqrt (fpDisc a b c d)) / (2 * c)

/-- The Möbius multiplier `ρ = λ₂/λ₁` — the contraction ratio of the iteration. -/
noncomputable def contractionRatio (a b c d : ℝ) : ℝ :=
  (a + d - Real.sqrt (fpDisc a b c d)) / (a + d + Real.sqrt (fpDisc a b c d))

/-- Cross-ratio coordinate straightening `φ` to multiplication by `ρ`. -/
noncomputable def cross (a b c d t : ℝ) : ℝ :=
  (t - perronRatio a b c d) / (t - subRatio a b c d)

section Positive
variable {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
include ha hb hc hd

/-- The discriminant is strictly positive (so the two fixed points are real and
distinct): `(d−a)² ≥ 0` and `4bc > 0`. -/
theorem fpDisc_pos : 0 < fpDisc a b c d := by
  unfold fpDisc; nlinarith [sq_nonneg (d - a), mul_pos hb hc]

/-- `√Δ ^ 2 = Δ`. -/
theorem sq_sqrt_fpDisc : Real.sqrt (fpDisc a b c d) ^ 2 = fpDisc a b c d :=
  Real.sq_sqrt (fpDisc_pos ha hb hc hd).le

/-- `√Δ > 0`. -/
theorem sqrt_fpDisc_pos : 0 < Real.sqrt (fpDisc a b c d) :=
  Real.sqrt_pos.mpr (fpDisc_pos ha hb hc hd)

/-- `√Δ > |a − d|`, since `Δ = (a−d)² + 4bc > (a−d)²`. -/
theorem abs_lt_sqrt_fpDisc : |a - d| < Real.sqrt (fpDisc a b c d) := by
  have h1 : |a - d| ^ 2 < Real.sqrt (fpDisc a b c d) ^ 2 := by
    rw [sq_abs, sq_sqrt_fpDisc ha hb hc hd]; unfold fpDisc
    nlinarith [mul_pos hb hc, sq_nonneg (a - d)]
  exact lt_of_pow_lt_pow_left₀ 2 (sqrt_fpDisc_pos ha hb hc hd).le h1

/-- Key linear relation: `2c · t⋆ = a − d + √Δ`. -/
theorem two_c_perron : 2 * c * perronRatio a b c d = a - d + Real.sqrt (fpDisc a b c d) := by
  have h2c : (2 * c : ℝ) ≠ 0 := by positivity
  rw [perronRatio, mul_comm (2 * c) _, div_mul_cancel₀ _ h2c]

/-- Key linear relation: `2c · t† = a − d − √Δ`. -/
theorem two_c_sub : 2 * c * subRatio a b c d = a - d - Real.sqrt (fpDisc a b c d) := by
  have h2c : (2 * c : ℝ) ≠ 0 := by positivity
  rw [subRatio, mul_comm (2 * c) _, div_mul_cancel₀ _ h2c]

/-- The Perron fixed point is positive: `t⋆ > 0`. -/
theorem perronRatio_pos : 0 < perronRatio a b c d := by
  have h := abs_lt_sqrt_fpDisc ha hb hc hd
  have hnum : 0 < a - d + Real.sqrt (fpDisc a b c d) := by
    have := neg_abs_le (a - d); linarith
  rw [perronRatio]; exact div_pos hnum (by positivity)

/-- The subdominant fixed point is negative: `t† < 0`. -/
theorem subRatio_neg : subRatio a b c d < 0 := by
  have h := abs_lt_sqrt_fpDisc ha hb hc hd
  have hnum : a - d - Real.sqrt (fpDisc a b c d) < 0 := by
    have := le_abs_self (a - d); linarith
  rw [subRatio]; exact div_neg_of_neg_of_pos hnum (by positivity)

/-- `t⋆ > t†` (distinct fixed points). -/
theorem sub_lt_perron : subRatio a b c d < perronRatio a b c d :=
  lt_trans (subRatio_neg ha hb hc hd) (perronRatio_pos ha hb hc hd)

/-- `2·(a − c·t⋆) = a + d − √Δ = 2λ₂`. -/
theorem two_a_sub_c_perron :
    2 * (a - c * perronRatio a b c d) = a + d - Real.sqrt (fpDisc a b c d) := by
  linear_combination -(two_c_perron ha hb hc hd)

/-- `2·(a − c·t†) = a + d + √Δ = 2λ₁ > 0`. -/
theorem two_a_sub_c_sub :
    2 * (a - c * subRatio a b c d) = a + d + Real.sqrt (fpDisc a b c d) := by
  linear_combination -(two_c_sub ha hb hc hd)

/-- `a − c·t† > 0` (`= λ₁`, the dominant eigenvalue). -/
theorem a_sub_c_sub_pos : 0 < a - c * subRatio a b c d := by
  have h := two_a_sub_c_sub ha hb hc hd
  have hS := sqrt_fpDisc_pos ha hb hc hd
  linarith

/-- The fixed-point quadratic holds at `t⋆`: `b = c·t⋆² + (d−a)·t⋆`. -/
theorem perron_quadratic : b = c * perronRatio a b c d ^ 2 + (d - a) * perronRatio a b c d := by
  have hc' : (4 * c) ≠ 0 := by positivity
  have hsq : (2 * c * perronRatio a b c d - (a - d)) ^ 2 = (d - a) ^ 2 + 4 * b * c := by
    rw [show 2 * c * perronRatio a b c d - (a - d) = Real.sqrt (fpDisc a b c d) by
          have := two_c_perron ha hb hc hd; linarith]
    rw [sq_sqrt_fpDisc ha hb hc hd]; unfold fpDisc; ring
  have h4 : 4 * c * (c * perronRatio a b c d ^ 2 + (d - a) * perronRatio a b c d - b) = 0 := by
    linear_combination hsq
  have := (mul_eq_zero.mp h4).resolve_left hc'
  linarith [this]

/-- The fixed-point quadratic holds at `t†`: `b = c·t†² + (d−a)·t†`. -/
theorem sub_quadratic : b = c * subRatio a b c d ^ 2 + (d - a) * subRatio a b c d := by
  have hc' : (4 * c) ≠ 0 := by positivity
  have hsq : (2 * c * subRatio a b c d - (a - d)) ^ 2 = (d - a) ^ 2 + 4 * b * c := by
    rw [show 2 * c * subRatio a b c d - (a - d) = -Real.sqrt (fpDisc a b c d) by
          have := two_c_sub ha hb hc hd; linarith]
    rw [neg_sq, sq_sqrt_fpDisc ha hb hc hd]; unfold fpDisc; ring
  have h4 : 4 * c * (c * subRatio a b c d ^ 2 + (d - a) * subRatio a b c d - b) = 0 := by
    linear_combination hsq
  have := (mul_eq_zero.mp h4).resolve_left hc'
  linarith [this]

/-- For `t > 0` the denominator `c·t + d` is positive. -/
theorem den_pos {t : ℝ} (ht : 0 < t) : 0 < c * t + d := by positivity

/-- `φ` maps the positive ray to itself: `t > 0 → φ(t) > 0`. -/
theorem mobius_pos {t : ℝ} (ht : 0 < t) : 0 < mobius a b c d t := by
  unfold mobius; apply div_pos <;> positivity

/-- The Perron ratio is a fixed point of `φ`: `φ(t⋆) = t⋆`. -/
theorem mobius_perron : mobius a b c d (perronRatio a b c d) = perronRatio a b c d := by
  have hden : c * perronRatio a b c d + d ≠ 0 :=
    ne_of_gt (den_pos ha hb hc hd (perronRatio_pos ha hb hc hd))
  unfold mobius
  rw [div_eq_iff hden]
  linear_combination perron_quadratic ha hb hc hd

/-- The factorization at `t⋆`: `φ(t) − t⋆ = (a − c·t⋆)·(t − t⋆)/(c·t + d)`. -/
theorem mobius_factor_perron {t : ℝ} (ht : 0 < t) :
    mobius a b c d t - perronRatio a b c d
      = (a - c * perronRatio a b c d) * (t - perronRatio a b c d) / (c * t + d) := by
  have hden : c * t + d ≠ 0 := ne_of_gt (den_pos ha hb hc hd ht)
  rw [mobius, div_sub' hden, div_eq_div_iff hden hden]
  linear_combination (c * t + d) * (perron_quadratic ha hb hc hd)

/-- The factorization at `t†`: `φ(t) − t† = (a − c·t†)·(t − t†)/(c·t + d)`. -/
theorem mobius_factor_sub {t : ℝ} (ht : 0 < t) :
    mobius a b c d t - subRatio a b c d
      = (a - c * subRatio a b c d) * (t - subRatio a b c d) / (c * t + d) := by
  have hden : c * t + d ≠ 0 := ne_of_gt (den_pos ha hb hc hd ht)
  rw [mobius, div_sub' hden, div_eq_div_iff hden hden]
  linear_combination (c * t + d) * (sub_quadratic ha hb hc hd)

/-- The eigenvalue identity `a − c·t⋆ = ρ·(a − c·t†)`, i.e. `λ₂ = ρ·λ₁`. -/
theorem a_sub_c_perron_eq :
    a - c * perronRatio a b c d = contractionRatio a b c d * (a - c * subRatio a b c d) := by
  have e1 := two_a_sub_c_perron ha hb hc hd
  have e2 := two_a_sub_c_sub ha hb hc hd
  have hsum : a + d + Real.sqrt (fpDisc a b c d) ≠ 0 := by
    have := sqrt_fpDisc_pos ha hb hc hd; positivity
  unfold contractionRatio
  rw [div_mul_eq_mul_div, eq_div_iff hsum]
  linear_combination (a - c * subRatio a b c d) * e1 - (a - c * perronRatio a b c d) * e2

/-- **Semiconjugacy (the Birkhoff/Perron heart).** In the cross-ratio coordinate
`g`, the Möbius map `φ` is multiplication by the constant `ρ`:
`g(φ(t)) = ρ · g(t)`.  Here `ρ = (a+d−√Δ)/(a+d+√Δ) = λ₂/λ₁`. -/
theorem cross_mobius {t : ℝ} (ht : 0 < t) :
    cross a b c d (mobius a b c d t) = contractionRatio a b c d * cross a b c d t := by
  have hden : c * t + d ≠ 0 := ne_of_gt (den_pos ha hb hc hd ht)
  have hts : t - subRatio a b c d ≠ 0 :=
    ne_of_gt (by have := subRatio_neg ha hb hc hd; linarith)
  have hacs : a - c * subRatio a b c d ≠ 0 := ne_of_gt (a_sub_c_sub_pos ha hb hc hd)
  have key := a_sub_c_perron_eq ha hb hc hd
  unfold cross
  rw [mobius_factor_perron ha hb hc hd ht, mobius_factor_sub ha hb hc hd ht,
    div_div_div_cancel_right₀ hden, key]
  field_simp

/-- `g` never takes the value `1` on the positive ray (since `t⋆ ≠ t†`). -/
theorem cross_ne_one {t : ℝ} (ht : 0 < t) : cross a b c d t ≠ 1 := by
  have hts : t - subRatio a b c d ≠ 0 :=
    ne_of_gt (by have := subRatio_neg ha hb hc hd; linarith)
  intro h
  unfold cross at h
  rw [div_eq_one_iff_eq hts] at h
  have : perronRatio a b c d = subRatio a b c d := by linarith
  exact absurd this (ne_of_gt (sub_lt_perron ha hb hc hd))

/-- The contraction ratio is a genuine contraction: `|ρ| < 1`. -/
theorem abs_contractionRatio_lt_one : |contractionRatio a b c d| < 1 := by
  have hS := sqrt_fpDisc_pos ha hb hc hd
  have hden : 0 < a + d + Real.sqrt (fpDisc a b c d) := by linarith
  unfold contractionRatio
  rw [abs_div, abs_of_pos hden, div_lt_one hden, abs_lt]
  constructor <;> linarith

end Positive

section Iteration
variable {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
include ha hb hc hd

/-- Iterates of `φ` stay on the positive ray. -/
theorem iterate_pos (n : ℕ) {t : ℝ} (ht : 0 < t) : 0 < (mobius a b c d)^[n] t := by
  induction n with
  | zero => simpa using ht
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact mobius_pos ha hb hc hd ih

/-- **Geometric straightening.** `g(φⁿ(t)) = ρⁿ · g(t)`: the cross-ratio coordinate
of the `n`-th power iterate decays like the `n`-th power of the multiplier `ρ`. -/
theorem cross_iterate (n : ℕ) {t : ℝ} (ht : 0 < t) :
    cross a b c d ((mobius a b c d)^[n] t)
      = contractionRatio a b c d ^ n * cross a b c d t := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', cross_mobius ha hb hc hd (iterate_pos ha hb hc hd k ht),
        ih, pow_succ]
      ring

/-- **Closed form of the power iteration.**
`φⁿ(t) = t⋆ + wₙ·(t⋆ − t†)/(1 − wₙ)` with `wₙ = ρⁿ·g(t)`. -/
theorem iterate_closed_form (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (mobius a b c d)^[n] t
      = perronRatio a b c d
        + contractionRatio a b c d ^ n * cross a b c d t * (perronRatio a b c d - subRatio a b c d)
            / (1 - contractionRatio a b c d ^ n * cross a b c d t) := by
  set s := (mobius a b c d)^[n] t with hs
  have hspos : 0 < s := iterate_pos ha hb hc hd n ht
  set w := contractionRatio a b c d ^ n * cross a b c d t with hw
  have hgs : cross a b c d s = w := by rw [hs, hw, cross_iterate ha hb hc hd n ht]
  have hts : s - subRatio a b c d ≠ 0 :=
    ne_of_gt (by have := subRatio_neg ha hb hc hd; linarith)
  have hwne : w ≠ 1 := by rw [← hgs]; exact cross_ne_one ha hb hc hd hspos
  have h1mw : (1 - w) ≠ 0 := sub_ne_zero.mpr (Ne.symm hwne)
  have hrel : s - perronRatio a b c d = w * (s - subRatio a b c d) := by
    have h := hgs; unfold cross at h; rwa [div_eq_iff hts] at h
  have h2 : s * (1 - w) = perronRatio a b c d - w * subRatio a b c d := by
    linear_combination hrel
  have hsval : s = (perronRatio a b c d - w * subRatio a b c d) / (1 - w) :=
    (eq_div_iff h1mw).mpr h2
  rw [hsval]
  field_simp
  ring

/-- **Main theorem (Birkhoff → Perron–Frobenius power iteration, 2×2).**
For a positive `2×2` matrix `A = !![a,b;c,d]`, the normalized power iteration on
the projective ray — `t ↦ φ(t) = (a·t+b)/(c·t+d)` — converges, from any positive
start `t`, to the Perron eigenvector ratio `t⋆`.  Convergence is geometric: the
cross-ratio coordinate decays like `ρⁿ` with `|ρ| < 1` (`cross_iterate`,
`abs_contractionRatio_lt_one`). -/
theorem power_iteration_tendsto {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => (mobius a b c d)^[n] t) atTop (nhds (perronRatio a b c d)) := by
  -- ρⁿ → 0
  have hpow : Tendsto (fun n => contractionRatio a b c d ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (abs_contractionRatio_lt_one ha hb hc hd)
  -- wₙ = ρⁿ·g(t) → 0
  have hw : Tendsto (fun n => contractionRatio a b c d ^ n * cross a b c d t) atTop (nhds 0) := by
    have h := hpow.mul_const (cross a b c d t)
    rwa [zero_mul] at h
  -- numerator wₙ·(t⋆ − t†) → 0
  have hnum : Tendsto
      (fun n => contractionRatio a b c d ^ n * cross a b c d t
        * (perronRatio a b c d - subRatio a b c d)) atTop (nhds 0) := by
    have h := hw.mul_const (perronRatio a b c d - subRatio a b c d)
    rwa [zero_mul] at h
  -- denominator 1 − wₙ → 1
  have hden1 : Tendsto (fun n => 1 - contractionRatio a b c d ^ n * cross a b c d t)
      atTop (nhds 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hw
    rwa [sub_zero] at h
  -- the quotient → 0
  have hfrac : Tendsto
      (fun n => contractionRatio a b c d ^ n * cross a b c d t
        * (perronRatio a b c d - subRatio a b c d)
        / (1 - contractionRatio a b c d ^ n * cross a b c d t)) atTop (nhds 0) := by
    have h := hnum.div hden1 one_ne_zero
    rwa [zero_div] at h
  have hmain := hfrac.const_add (perronRatio a b c d)
  rw [add_zero] at hmain
  exact hmain.congr (fun n => (iterate_closed_form ha hb hc hd n ht).symm)

end Iteration

section Eigen
variable {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
include ha hb hc hd

/-- The dominant (Perron) eigenvalue equals `c·t⋆ + d = (a + d + √Δ)/2 = λ₁`. -/
theorem perron_eigenvalue :
    c * perronRatio a b c d + d = (a + d + Real.sqrt (fpDisc a b c d)) / 2 := by
  linear_combination (two_c_perron ha hb hc hd) / 2

/-- `(t⋆, 1)` is a genuine eigenvector of `A = !![a,b;c,d]` with eigenvalue
`λ₁ = c·t⋆ + d`: applying `A` scales the vector by `λ₁`.  This pins `t⋆` as the
Perron eigenvector direction. -/
theorem perron_eigenvector :
    a * perronRatio a b c d + b = (c * perronRatio a b c d + d) * perronRatio a b c d := by
  linear_combination perron_quadratic ha hb hc hd

/-- The multiplier is the eigenvalue ratio: `ρ · λ₁ = λ₂`, i.e.
`ρ = λ₂ / λ₁` with `λ₁ = (a+d+√Δ)/2`, `λ₂ = (a+d−√Δ)/2`. -/
theorem contractionRatio_eq_eigenvalue_ratio :
    contractionRatio a b c d * ((a + d + Real.sqrt (fpDisc a b c d)) / 2)
      = (a + d - Real.sqrt (fpDisc a b c d)) / 2 := by
  have hden : a + d + Real.sqrt (fpDisc a b c d) ≠ 0 := by
    have := sqrt_fpDisc_pos ha hb hc hd; positivity
  unfold contractionRatio
  field_simp

end Eigen

end Hilbert4Birkhoff
