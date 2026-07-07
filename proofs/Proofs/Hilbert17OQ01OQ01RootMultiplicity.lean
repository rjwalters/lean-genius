/-
  Hilbert's 17th problem, univariate case — ROOT-MULTIPLICITY structure of a real
  sum of two squares.

  The sharpness file `Proofs/Hilbert17OQ01OQ01OQ01.lean` pins down the *degree* of
  the summands in a representation `p = u² + v²`.  This file pins down the
  *root-multiplicity* structure: how the real zeros of `p` are distributed, and how
  their multiplicities are forced by the multiplicities in the two summands.  This
  answers the parent entry's remaining open question linking the smaller summand to
  the root multiplicity.

  The governing principle is again real non-cancellation, now at a *point* instead
  of at top degree: for a real number `t`,

      u(t)² + v(t)² = 0  ⟺  u(t) = 0  ∧  v(t) = 0.

  So the real roots of `p = u² + v²` are *exactly* the common real roots of `u` and
  `v`.  Tracking multiplicities through the local factorisation gives the exact
  formula

      rootMultiplicity r (u² + v²) = 2 · min (rootMultiplicity r u) (rootMultiplicity r v)

  (for `u, v ≠ 0`).  In particular **every real root of a real 2-SOS has even
  multiplicity** — a structural obstruction: a polynomial with any simple real root
  is never a sum of two squares.  Combined with the PSD ⟹ 2-SOS existence theorem of
  the parent, this recovers the classical fact that a nonnegative univariate
  polynomial touches the axis only with even order of contact.

  Results:

    * `eval_sq_add_sq_eq_zero_iff` — real roots of `u² + v²` are the common roots.
    * `rootMultiplicity_sq_add_sq` — the exact `2·min` multiplicity formula.
    * `even_rootMultiplicity_sq_add_sq` — every real root of a nonzero 2-SOS has
      even multiplicity (also covers the degenerate `u = 0` / `v = 0` cases).
    * `IsPSD.even_rootMultiplicity` — every real root of a nonzero PSD univariate
      polynomial has even multiplicity.

  Fully elementary and 0-axiom, like the parent.
-/
import Mathlib
import Proofs.Hilbert17OQ01OQ01

namespace Hilbert17OQ01OQ01RootMult

open Polynomial
open Hilbert17UnivariatePSDSOS (IsPSD)

/-- A real sum of two squares is the zero polynomial only if a summand forces it:
if `u ≠ 0` then `u² + v² ≠ 0`.  (A nonzero `u` evaluates to something nonzero
somewhere, and there `u² + v² ≥ u² > 0`, so the polynomial is not identically `0`.) -/
theorem sq_add_sq_ne_zero {u v : ℝ[X]} (h : u ≠ 0) : u ^ 2 + v ^ 2 ≠ 0 := by
  intro hc
  apply h
  apply Polynomial.funext
  intro x
  have hx : (u ^ 2 + v ^ 2).eval x = 0 := by rw [hc]; simp
  simp only [eval_add, eval_pow, eval_zero] at hx ⊢
  nlinarith [sq_nonneg (u.eval x), sq_nonneg (v.eval x)]

/-- **Real roots of a 2-SOS are the common roots.**  Since a sum of two real
squares vanishes only when both vanish, `t` is a root of `u² + v²` iff it is a
common root of `u` and `v`. -/
theorem eval_sq_add_sq_eq_zero_iff {u v : ℝ[X]} {t : ℝ} :
    (u ^ 2 + v ^ 2).eval t = 0 ↔ u.eval t = 0 ∧ v.eval t = 0 := by
  constructor
  · intro h
    simp only [eval_add, eval_pow] at h
    exact ⟨by nlinarith [sq_nonneg (u.eval t), sq_nonneg (v.eval t)],
           by nlinarith [sq_nonneg (u.eval t), sq_nonneg (v.eval t)]⟩
  · rintro ⟨hu, hv⟩
    simp only [eval_add, eval_pow, hu, hv]; ring

/-- Extract the local factorisation at a root: `u = (X - r)^(mult) · u₁` with
`u₁(r) ≠ 0`, where `mult = rootMultiplicity r u`. -/
private theorem factor_at_root (r : ℝ) (u : ℝ[X]) (hu0 : u ≠ 0) :
    ∃ u₁ : ℝ[X], u = (X - C r) ^ (rootMultiplicity r u) * u₁ ∧ u₁.eval r ≠ 0 := by
  obtain ⟨u₁, hu₁⟩ := pow_rootMultiplicity_dvd u r
  refine ⟨u₁, hu₁, ?_⟩
  intro hev
  obtain ⟨w, hw⟩ := dvd_iff_isRoot.mpr hev
  have huw : u = (X - C r) ^ (rootMultiplicity r u + 1) * w := by
    rw [pow_succ, mul_assoc, ← hw]; exact hu₁
  exact pow_rootMultiplicity_not_dvd hu0 r ⟨w, huw⟩

/-- Helper for the multiplicity formula assuming the multiplicities are ordered:
when `rootMultiplicity r u ≤ rootMultiplicity r v`, the smaller one dominates and
`rootMultiplicity r (u² + v²) = 2 · rootMultiplicity r u`. -/
private theorem rootMultiplicity_sq_add_sq_of_le (r : ℝ) {u v : ℝ[X]}
    (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hab : rootMultiplicity r u ≤ rootMultiplicity r v) :
    rootMultiplicity r (u ^ 2 + v ^ 2) = 2 * rootMultiplicity r u := by
  set a := rootMultiplicity r u with ha
  set b := rootMultiplicity r v with hb
  obtain ⟨u₁, hu₁, hu₁r⟩ := factor_at_root r u hu0
  obtain ⟨v₁, hv₁, hv₁r⟩ := factor_at_root r v hv0
  -- factor out `(X - r)^(2a)`
  set q : ℝ[X] := u₁ ^ 2 + (X - C r) ^ (2 * (b - a)) * v₁ ^ 2 with hq
  have key : u ^ 2 + v ^ 2 = (X - C r) ^ (2 * a) * q := by
    have hbexp : (X - C r) ^ (2 * b)
        = (X - C r) ^ (2 * a) * (X - C r) ^ (2 * (b - a)) := by
      rw [← pow_add]; congr 1; omega
    have e1 : ((X - C r) ^ a * u₁) ^ 2 = (X - C r) ^ (2 * a) * u₁ ^ 2 := by
      rw [mul_pow, ← pow_mul]; ring_nf
    have e2 : ((X - C r) ^ b * v₁) ^ 2 = (X - C r) ^ (2 * b) * v₁ ^ 2 := by
      rw [mul_pow, ← pow_mul]; ring_nf
    rw [hq, hu₁, hv₁, e1, e2, hbexp]; ring
  -- `q(r) ≠ 0`: the surviving term is `u₁(r)² > 0`
  have hqr : q.eval r ≠ 0 := by
    rw [hq]
    rcases eq_or_lt_of_le hab with heq | hlt
    · -- `a = b`: `q(r) = u₁(r)² + v₁(r)²`
      simp only [eval_add, eval_pow, show b - a = 0 by omega, Nat.mul_zero,
        pow_zero, one_mul]
      nlinarith [sq_nonneg (v₁.eval r), pow_two_pos_of_ne_zero hu₁r]
    · -- `a < b`: the `v₁` term carries a positive power of `(X - r)`, so `q(r) = u₁(r)²`
      simp only [eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self]
      rw [zero_pow (by omega)]
      simpa using pow_ne_zero 2 hu₁r
  have hp0 : (X - C r) ^ (2 * a) * q ≠ 0 := by rw [← key]; exact sq_add_sq_ne_zero hu0
  rw [key, rootMultiplicity_mul hp0, rootMultiplicity_X_sub_C_pow,
      rootMultiplicity_eq_zero (by simpa [IsRoot] using hqr), add_zero]

/-- **Exact root-multiplicity formula for a real 2-SOS.**

For nonzero `u, v`, the multiplicity of any real number `r` as a root of `u² + v²`
is *exactly twice* the smaller of its multiplicities in `u` and `v`:

  `rootMultiplicity r (u² + v²) = 2 · min (rootMultiplicity r u) (rootMultiplicity r v)`.

Two real squares cannot cancel at a point any more than at top degree: at the
common order of vanishing `m = min(a,b)`, factoring out `(X - r)^{2m}` leaves a
polynomial whose value at `r` is a *positive* sum of squares. -/
theorem rootMultiplicity_sq_add_sq (r : ℝ) {u v : ℝ[X]} (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
    rootMultiplicity r (u ^ 2 + v ^ 2)
      = 2 * min (rootMultiplicity r u) (rootMultiplicity r v) := by
  rcases le_total (rootMultiplicity r u) (rootMultiplicity r v) with hab | hba
  · rw [min_eq_left hab, rootMultiplicity_sq_add_sq_of_le r hu0 hv0 hab]
  · rw [min_eq_right hba, add_comm (u ^ 2),
      rootMultiplicity_sq_add_sq_of_le r hv0 hu0 hba]

/-- **Every real root of a real 2-SOS has even multiplicity.**

A real polynomial that is a sum of two squares (and is nonzero) can only meet the
real axis with even order of contact.  Equivalently: a polynomial with even degree
is necessary but a polynomial with *any* simple real root is *never* a sum of two
squares.  The degenerate cases `u = 0` and `v = 0` (where `p` is a single square)
are included. -/
theorem even_rootMultiplicity_sq_add_sq {p u v : ℝ[X]} (hp0 : p ≠ 0)
    (huv : p = u ^ 2 + v ^ 2) (r : ℝ) : Even (rootMultiplicity r p) := by
  by_cases hu0 : u = 0
  · -- `p = v²`
    have hv0 : v ≠ 0 := by intro h; rw [huv, hu0, h] at hp0; simp at hp0
    have : p = v * v := by rw [huv, hu0]; ring
    rw [this, rootMultiplicity_mul (by rw [← this]; exact hp0)]
    exact ⟨rootMultiplicity r v, rfl⟩
  · by_cases hv0 : v = 0
    · -- `p = u²`
      have : p = u * u := by rw [huv, hv0]; ring
      rw [this, rootMultiplicity_mul (by rw [← this]; exact hp0)]
      exact ⟨rootMultiplicity r u, rfl⟩
    · -- both nonzero: the `2·min` formula is manifestly even
      rw [huv, rootMultiplicity_sq_add_sq r hu0 hv0]
      exact ⟨min (rootMultiplicity r u) (rootMultiplicity r v), two_mul _⟩

/-- **Even order of contact for nonnegative polynomials.**  Every real root of a
nonzero PSD univariate polynomial has even multiplicity: a nonnegative real
polynomial touches the axis only to even order (it cannot cross it).  This combines
the parent's PSD ⟹ sum-of-two-squares theorem with the even-multiplicity
obstruction above. -/
theorem IsPSD.even_rootMultiplicity {p : ℝ[X]} (hp0 : p ≠ 0) (h : IsPSD p) (r : ℝ) :
    Even (rootMultiplicity r p) := by
  obtain ⟨u, v, huv, _, _⟩ := Hilbert17OQ01OQ01.univariate_psd_is_two_sos_deg p h
  exact even_rootMultiplicity_sq_add_sq hp0 huv r

end Hilbert17OQ01OQ01RootMult

-- Axiom audit: headline theorems should report only the foundational trio
-- (propext, Classical.choice, Quot.sound) — no sorryAx, no Lean.ofReduceBool.
#print axioms Hilbert17OQ01OQ01RootMult.eval_sq_add_sq_eq_zero_iff
#print axioms Hilbert17OQ01OQ01RootMult.rootMultiplicity_sq_add_sq
#print axioms Hilbert17OQ01OQ01RootMult.even_rootMultiplicity_sq_add_sq
#print axioms Hilbert17OQ01OQ01RootMult.IsPSD.even_rootMultiplicity
