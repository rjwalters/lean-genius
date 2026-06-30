import Proofs.JensenInequalityOQ01OQ01OQ01OQ01OQ01
import Proofs.JensenInequalityOQ01OQ01

/-
# The equality case of Lyapunov's inequality

The parent file `JensenInequalityOQ01OQ01OQ01OQ01OQ01` proves **Lyapunov's inequality**: the
weighted moment function `A(t) = ∑ i, w i · (x i)^t` of a strictly positive family is log-convex,
equivalently
`A(a·p + b·r) ≤ A(p)^a · A(r)^b`  for convex weights `a, b > 0`, `a + b = 1`.

This file pins down its **equality case**. For *distinct* exponents `p ≠ r`, equality holds in the
Lyapunov interpolation inequality **iff the data `x` is constant**:
`A(a·p + b·r) = A(p)^a · A(r)^b  ↔  ∀ i j, x i = x j`.

In other words the moment curve `t ↦ log A(t)` is *strictly* convex exactly off the degenerate
locus where all the `x i` coincide (where `A(t) = (∑ w i) · c^t` is genuinely log-affine). This is
the second-order sharpening of the equality case of the power-mean inequality
(`JensenInequalityOQ01OQ01OQ01OQ04OQ01`, where `M_r = M_t ↔ x` constant): there we compared two
points of the moment curve, here we characterise when a chord touches the curve.

## Engine

The whole result is a one-application consequence of the **two-variable weighted AM–GM equality
case** `amgm_two_weighted_eq_iff` (from the grandparent file `JensenInequalityOQ01OQ01`), summed
pointwise. Normalise the two moment families to probability vectors,
`S i = w i · x i^p / A(p)` and `T i = w i · x i^r / A(r)` (so `∑ S = ∑ T = 1`). The pointwise
weighted AM–GM `S i^a · T i^b ≤ a·S i + b·T i` summed over `i` gives exactly Lyapunov's inequality
(after the interpolation identity `(w x^p)^a (w x^r)^b = w · x^{a p + b r}`), and a sum of `≤`'s is
an equality iff it is termwise an equality. Termwise equality `S i = T i` says
`x i^{p-r} = A(p)/A(r)` is the same constant for every `i`, which for `p ≠ r` forces all `x i`
equal by injectivity of `t ↦ t^{p-r}`.

This avoids the (unformalised) general Hölder equality case entirely: the only equality input is the
two-variable AM–GM, and the global step is `Finset.sum_eq_sum_iff_of_le`.

## Main results

* `moment_interp_eq_iff` — equality `A(a·p+b·r) = A(p)^a · A(r)^b ↔ x` constant (for `p ≠ r`).
* `moment_interp_lt_of_not_const` — strict Lyapunov inequality when `x` is non-constant.
* `moment_lyapunov_eq_iff` — the symmetric three-exponent equality
  `A(q)^(r-p) = A(p)^(r-q) · A(r)^(q-p) ↔ x` constant (for `p < q < r`).
-/

open Finset Real

namespace JensenLyapunovEq

open JensenLyapunov

variable {ι : Type*} [Fintype ι]

/-- **Normalised pointwise AM–GM, summed.** For nonnegative families `u v : ι → ℝ` that are both
probability vectors (`∑ u = ∑ v = 1`) and convex weights `a, b > 0` with `a + b = 1`, the weighted
geometric average `∑ i, u i^a · v i^b` equals `1` **iff** `u i = v i` for every `i`.

This is the abstract core of Lyapunov's equality case: the pointwise two-variable AM–GM
`u i^a v i^b ≤ a·u i + b·v i` sums to `≤ 1`, and equality of a sum of `≤`'s is termwise equality
(`Finset.sum_eq_sum_iff_of_le`), each term resolved by `amgm_two_weighted_eq_iff`. -/
lemma normalized_amgm_sum_eq_one_iff {u v : ι → ℝ}
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (husum : ∑ i, u i = 1) (hvsum : ∑ i, v i = 1)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (∑ i, u i ^ a * v i ^ b = 1) ↔ ∀ i, u i = v i := by
  have hle : ∀ i ∈ (univ : Finset ι), u i ^ a * v i ^ b ≤ a * u i + b * v i := fun i _ =>
    Real.geom_mean_le_arith_mean2_weighted ha.le hb.le (hu i) (hv i) hab
  have hgsum : ∑ i, (a * u i + b * v i) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, husum, hvsum,
      mul_one, mul_one, hab]
  constructor
  · intro h
    have hsumeq : ∑ i, u i ^ a * v i ^ b = ∑ i, (a * u i + b * v i) := by rw [h, hgsum]
    have hpoint := (Finset.sum_eq_sum_iff_of_le hle).mp hsumeq
    intro i
    exact (amgm_two_weighted_eq_iff ha hb hab (hu i) (hv i)).mp (hpoint i (mem_univ i))
  · intro h
    have hsumeq : ∑ i, u i ^ a * v i ^ b = ∑ i, (a * u i + b * v i) :=
      Finset.sum_congr rfl fun i _ =>
        (amgm_two_weighted_eq_iff ha hb hab (hu i) (hv i)).mpr (h i)
    rw [hsumeq, hgsum]

/-- **Equality case of Lyapunov's interpolation inequality.** For strictly positive families
`w x : ι → ℝ` on a nonempty finite index type, *distinct* exponents `p ≠ r`, and convex weights
`a, b > 0` with `a + b = 1`, equality
`A(a·p + b·r) = A(p)^a · A(r)^b` (where `A(t) = ∑ i, w i · (x i)^t`) holds **iff** the data `x` is
constant. -/
theorem moment_interp_eq_iff (w x : ι → ℝ) [Nonempty ι]
    (hw : ∀ i, 0 < w i) (hx : ∀ i, 0 < x i)
    (p r a b : ℝ) (hpr : p ≠ r) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    moment w x (a * p + b * r) = (moment w x p) ^ a * (moment w x r) ^ b
      ↔ ∀ i j, x i = x j := by
  have hAppos : 0 < moment w x p := moment_pos w x hw hx p
  have hArpos : 0 < moment w x r := moment_pos w x hw hx r
  have hDpos : 0 < (moment w x p) ^ a * (moment w x r) ^ b :=
    mul_pos (Real.rpow_pos_of_pos hAppos a) (Real.rpow_pos_of_pos hArpos b)
  -- the pointwise interpolation identity `(w x^p)^a (w x^r)^b = w · x^{a p + b r}`
  have term : ∀ i, (w i * x i ^ p) ^ a * (w i * x i ^ r) ^ b = w i * x i ^ (a * p + b * r) := by
    intro i
    rw [Real.mul_rpow (hw i).le (Real.rpow_nonneg (hx i).le _),
      Real.mul_rpow (hw i).le (Real.rpow_nonneg (hx i).le _),
      ← Real.rpow_mul (hx i).le, ← Real.rpow_mul (hx i).le,
      mul_mul_mul_comm, ← Real.rpow_add (hw i), ← Real.rpow_add (hx i), hab, Real.rpow_one,
      show p * a + r * b = a * p + b * r from by ring]
  -- normalised probability vectors
  set S : ι → ℝ := fun i => w i * x i ^ p / moment w x p with hS_def
  set T : ι → ℝ := fun i => w i * x i ^ r / moment w x r with hT_def
  have hSnn : ∀ i, 0 ≤ S i := fun i =>
    div_nonneg (mul_nonneg (hw i).le (Real.rpow_nonneg (hx i).le _)) hAppos.le
  have hTnn : ∀ i, 0 ≤ T i := fun i =>
    div_nonneg (mul_nonneg (hw i).le (Real.rpow_nonneg (hx i).le _)) hArpos.le
  have hSsum : ∑ i, S i = 1 := by
    simp only [hS_def]; rw [← Finset.sum_div]; exact div_self hAppos.ne'
  have hTsum : ∑ i, T i = 1 := by
    simp only [hT_def]; rw [← Finset.sum_div]; exact div_self hArpos.ne'
  have hterm : ∀ i, S i ^ a * T i ^ b
      = w i * x i ^ (a * p + b * r) / ((moment w x p) ^ a * (moment w x r) ^ b) := by
    intro i
    simp only [hS_def, hT_def]
    rw [Real.div_rpow (mul_nonneg (hw i).le (Real.rpow_nonneg (hx i).le _)) hAppos.le,
      Real.div_rpow (mul_nonneg (hw i).le (Real.rpow_nonneg (hx i).le _)) hArpos.le,
      div_mul_div_comm, term i]
  constructor
  · -- forward: equality forces the data to be constant
    intro heq
    have hsum1 : ∑ i, S i ^ a * T i ^ b = 1 := by
      have he : ∑ i, S i ^ a * T i ^ b
          = (∑ i, w i * x i ^ (a * p + b * r)) / ((moment w x p) ^ a * (moment w x r) ^ b) := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => hterm i
      rw [he, show (∑ i, w i * x i ^ (a * p + b * r)) = moment w x (a * p + b * r) from rfl,
        heq, div_self hDpos.ne']
    have hST_eq : ∀ i, S i = T i :=
      (normalized_amgm_sum_eq_one_iff hSnn hTnn hSsum hTsum a b ha hb hab).mp hsum1
    -- termwise equality says `x i^p · A(r) = x i^r · A(p)`
    have hkey : ∀ i, x i ^ p * moment w x r = x i ^ r * moment w x p := by
      intro i
      have h := hST_eq i
      simp only [hS_def, hT_def] at h
      rw [div_eq_div_iff hAppos.ne' hArpos.ne', mul_assoc, mul_assoc] at h
      exact mul_left_cancel₀ (hw i).ne' h
    intro i j
    have hi : x i ^ (p - r) = moment w x p / moment w x r := by
      rw [Real.rpow_sub (hx i), div_eq_div_iff (Real.rpow_pos_of_pos (hx i) r).ne' hArpos.ne']
      linear_combination hkey i
    have hj : x j ^ (p - r) = moment w x p / moment w x r := by
      rw [Real.rpow_sub (hx j), div_eq_div_iff (Real.rpow_pos_of_pos (hx j) r).ne' hArpos.ne']
      linear_combination hkey j
    exact (Real.rpow_left_inj (hx i).le (hx j).le (sub_ne_zero.mpr hpr)).mp (hi.trans hj.symm)
  · -- backward: constant data saturates Lyapunov's inequality
    intro hconst
    obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
    have hmoment : ∀ t, moment w x t = (∑ i, w i) * (x i0) ^ t := by
      intro t
      simp only [moment]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [hconst i i0]
    have hWpos : 0 < ∑ i, w i := Finset.sum_pos (fun i _ => hw i) univ_nonempty
    have hc : 0 < x i0 := hx i0
    rw [hmoment (a * p + b * r), hmoment p, hmoment r,
      Real.mul_rpow hWpos.le (Real.rpow_nonneg hc.le _),
      Real.mul_rpow hWpos.le (Real.rpow_nonneg hc.le _),
      ← Real.rpow_mul hc.le, ← Real.rpow_mul hc.le,
      mul_mul_mul_comm, ← Real.rpow_add hWpos, ← Real.rpow_add hc, hab, Real.rpow_one,
      show p * a + r * b = a * p + b * r from by ring]

/-- **Strict Lyapunov interpolation inequality.** For strictly positive families `w x` and *distinct*
exponents `p ≠ r`, if the data `x` is non-constant then the Lyapunov inequality is strict:
`A(a·p + b·r) < A(p)^a · A(r)^b`. -/
theorem moment_interp_lt_of_not_const (w x : ι → ℝ) [Nonempty ι]
    (hw : ∀ i, 0 < w i) (hx : ∀ i, 0 < x i)
    (p r a b : ℝ) (hpr : p ≠ r) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hne : ∃ i j, x i ≠ x j) :
    moment w x (a * p + b * r) < (moment w x p) ^ a * (moment w x r) ^ b := by
  rcases lt_or_eq_of_le (moment_interp_le w x hw hx p r a b ha hb hab) with hlt | heq
  · exact hlt
  · obtain ⟨i, j, hij⟩ := hne
    exact absurd ((moment_interp_eq_iff w x hw hx p r a b hpr ha hb hab).mp heq i j) hij

/-- **Equality case of Lyapunov's inequality (symmetric three-exponent form).** For strictly positive
families `w x` and exponents `p < q < r`, equality
`A(q)^(r-p) = A(p)^(r-q) · A(r)^(q-p)` holds **iff** the data `x` is constant. -/
theorem moment_lyapunov_eq_iff (w x : ι → ℝ) [Nonempty ι]
    (hw : ∀ i, 0 < w i) (hx : ∀ i, 0 < x i)
    (p q r : ℝ) (hpq : p < q) (hqr : q < r) :
    (moment w x q) ^ (r - p) = (moment w x p) ^ (r - q) * (moment w x r) ^ (q - p)
      ↔ ∀ i j, x i = x j := by
  have hAppos : 0 < moment w x p := moment_pos w x hw hx p
  have hArpos : 0 < moment w x r := moment_pos w x hw hx r
  have hrp : 0 < r - p := by linarith
  set a := (r - q) / (r - p) with ha_def
  set b := (q - p) / (r - p) with hb_def
  have ha : 0 < a := div_pos (by linarith) hrp
  have hb : 0 < b := div_pos (by linarith) hrp
  have hab : a + b = 1 := by
    rw [ha_def, hb_def, ← add_div, div_eq_one_iff_eq hrp.ne']; ring
  have hq_eq : a * p + b * r = q := by rw [ha_def, hb_def]; field_simp; ring
  have hexp1 : a * (r - p) = r - q := by rw [ha_def, div_mul_cancel₀ _ hrp.ne']
  have hexp2 : b * (r - p) = q - p := by rw [hb_def, div_mul_cancel₀ _ hrp.ne']
  rw [← moment_interp_eq_iff w x hw hx p r a b (ne_of_lt (by linarith)) ha hb hab, hq_eq]
  constructor
  · intro h
    have h2 : (moment w x q) ^ (r - p)
        = ((moment w x p) ^ a * (moment w x r) ^ b) ^ (r - p) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hAppos.le a) (Real.rpow_nonneg hArpos.le b),
        ← Real.rpow_mul hAppos.le, ← Real.rpow_mul hArpos.le, hexp1, hexp2]
      exact h
    exact (Real.rpow_left_inj (moment_pos w x hw hx q).le
      (mul_pos (Real.rpow_pos_of_pos hAppos a) (Real.rpow_pos_of_pos hArpos b)).le hrp.ne').mp h2
  · intro h
    rw [h, Real.mul_rpow (Real.rpow_nonneg hAppos.le a) (Real.rpow_nonneg hArpos.le b),
      ← Real.rpow_mul hAppos.le, ← Real.rpow_mul hArpos.le, hexp1, hexp2]

end JensenLyapunovEq

-- #print axioms JensenLyapunovEq.moment_interp_eq_iff
-- #print axioms JensenLyapunovEq.moment_interp_lt_of_not_const
-- #print axioms JensenLyapunovEq.moment_lyapunov_eq_iff
