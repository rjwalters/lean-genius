/-
  Hilbert's 17th problem, univariate case — COPRIME NORMALIZATION of a real sum of
  two squares.

  The sharpness file `Proofs/Hilbert17OQ01OQ01OQ01.lean` pins down the *degree* of the
  summands in a representation `p = u² + v²`, and the companion
  `Proofs/Hilbert17OQ01OQ01RootMultiplicity.lean` pins down the *multiplicity* of the
  real roots.  This file answers that entry's remaining open question: the
  **coprime (primitive) normalization** of a real 2-SOS.

  Two facts drive everything:

    * **Bézout at a point.**  If `u` and `v` are coprime (`IsCoprime u v`) then they
      have no common real root: evaluating a Bézout identity `a·u + b·v = 1` at any
      point `t` gives `1 = 0` the moment both `u(t) = v(t) = 0`.  Combined with the
      pointwise non-cancellation `u(t)² + v(t)² = 0 ⟺ u(t) = v(t) = 0`, this makes a
      coprime 2-SOS **positive definite**:  `u² + v² > 0` everywhere on `ℝ`, so it has
      no real roots at all.

    * **Divide out the gcd.**  For any `(u, v) ≠ (0, 0)`, writing `d = gcd(u, v)` and
      `u = d·u₁`, `v = d·v₁`, the cofactors `u₁, v₁` are coprime (cancel `d` in the
      Bézout identity for `d`), giving the factorisation

          u² + v² = d² · (u₁² + v₁²),   with  u₁² + v₁²  positive definite.

  So every real 2-SOS splits as `(square of the gcd) · (positive-definite primitive
  2-SOS)`.  All real zeros live in the `d²` factor, recovering
  `rootMultiplicity r (u² + v²) = 2 · rootMultiplicity r (gcd u v)` — the exact link
  between the root multiplicities of the parent entry and the gcd of the summands.

  Finally we settle the *uniqueness* half of the open question **negatively**: the
  primitive part is **not** an invariant of `p`.  Concretely `(X² + 1)²` is
  simultaneously the non-coprime square `(X² + 1)² + 0²` (primitive part `1`) and the
  coprime sum `(X² − 1)² + (2X)²` (primitive part `p` itself).  Coprimality of the
  summands is not preserved across different 2-SOS decompositions of the same `p`.

  Fully elementary and 0-axiom, like the parent.

  Results:
    * `no_common_root_of_isCoprime` — coprime summands share no real root (Bézout).
    * `sq_add_sq_pos_of_isCoprime`  — a coprime 2-SOS is positive definite.
    * `not_isRoot_of_isCoprime`     — hence has no real roots.
    * `exists_primitive_factorization` — `p = (gcd u v)² · (primitive 2-SOS)`.
    * `rootMultiplicity_two_sos`    — `rootMult r p = 2 · rootMult r (gcd u v)`.
    * `coprimality_not_invariant`   — the primitive part is not determined by `p`.
-/
import Mathlib
import Proofs.Hilbert17OQ01OQ01RootMultiplicity

namespace Hilbert17OQ01OQ01CoprimeNorm

open Polynomial
open Hilbert17OQ01OQ01RootMult (eval_sq_add_sq_eq_zero_iff)

/-- **Coprime polynomials have no common real root.**  From a Bézout identity
`a·u + b·v = 1`, evaluating at any point `t` where `u(t) = v(t) = 0` gives `1 = 0`. -/
theorem no_common_root_of_isCoprime {u v : ℝ[X]} (h : IsCoprime u v) (t : ℝ) :
    ¬ (u.eval t = 0 ∧ v.eval t = 0) := by
  rintro ⟨hu, hv⟩
  obtain ⟨a, b, hab⟩ := h
  have hev := congrArg (eval t) hab
  simp only [eval_add, eval_mul, hu, hv, mul_zero, add_zero, eval_one] at hev
  exact one_ne_zero hev.symm

/-- **A coprime sum of two squares is positive definite.**  It is `≥ 0` pointwise and
never `0` (that would force a common root, impossible for coprime summands), hence
strictly positive everywhere. -/
theorem sq_add_sq_pos_of_isCoprime {u v : ℝ[X]} (h : IsCoprime u v) (t : ℝ) :
    0 < (u ^ 2 + v ^ 2).eval t := by
  have hne : (u ^ 2 + v ^ 2).eval t ≠ 0 := fun hc =>
    no_common_root_of_isCoprime h t (eval_sq_add_sq_eq_zero_iff.mp hc)
  have hge : 0 ≤ (u ^ 2 + v ^ 2).eval t := by
    simp only [eval_add, eval_pow]; positivity
  exact lt_of_le_of_ne hge (Ne.symm hne)

/-- **A coprime 2-SOS has no real roots.**  Immediate from positive definiteness. -/
theorem not_isRoot_of_isCoprime {u v : ℝ[X]} (h : IsCoprime u v) (t : ℝ) :
    ¬ (u ^ 2 + v ^ 2).IsRoot t :=
  fun hroot => (sq_add_sq_pos_of_isCoprime h t).ne' hroot

/-- **Coprime cofactors.**  Dividing `u` and `v` by their gcd `d` yields coprime
polynomials: cancel `d` in the Bézout identity `d = u·gcdA + v·gcdB`. -/
theorem isCoprime_cofactors {u v u₁ v₁ : ℝ[X]} (h : ¬ (u = 0 ∧ v = 0))
    (hu : u = EuclideanDomain.gcd u v * u₁) (hv : v = EuclideanDomain.gcd u v * v₁) :
    IsCoprime u₁ v₁ := by
  have hd0 : EuclideanDomain.gcd u v ≠ 0 := by
    rw [Ne, EuclideanDomain.gcd_eq_zero_iff]; exact h
  have hbez := EuclideanDomain.gcd_eq_gcd_ab u v
  set d := EuclideanDomain.gcd u v with hd
  set A := EuclideanDomain.gcdA u v with hA
  set B := EuclideanDomain.gcdB u v with hB
  rw [hu, hv] at hbez
  have hfac : d * 1 = d * (u₁ * A + v₁ * B) := by linear_combination hbez
  have hone : (1 : ℝ[X]) = u₁ * A + v₁ * B := mul_left_cancel₀ hd0 hfac
  exact ⟨A, B, by linear_combination -hone⟩

/-- **Coprime (primitive) normalisation of a real 2-SOS.**  For `(u, v) ≠ (0, 0)`,
writing `d = gcd(u, v)` and `u = d·u₁`, `v = d·v₁`, the cofactors are coprime and

    u² + v² = d² · (u₁² + v₁²),

where the primitive part `u₁² + v₁²` is positive definite.  So every real 2-SOS is a
perfect square (`d²`) times a strictly positive polynomial. -/
theorem exists_primitive_factorization {u v : ℝ[X]} (h : ¬ (u = 0 ∧ v = 0)) :
    ∃ u₁ v₁ : ℝ[X],
      u = EuclideanDomain.gcd u v * u₁ ∧ v = EuclideanDomain.gcd u v * v₁ ∧
      IsCoprime u₁ v₁ ∧
      u ^ 2 + v ^ 2 = (EuclideanDomain.gcd u v) ^ 2 * (u₁ ^ 2 + v₁ ^ 2) ∧
      ∀ t, 0 < (u₁ ^ 2 + v₁ ^ 2).eval t := by
  obtain ⟨u₁, hu₁⟩ := EuclideanDomain.gcd_dvd_left u v
  obtain ⟨v₁, hv₁⟩ := EuclideanDomain.gcd_dvd_right u v
  have hcop : IsCoprime u₁ v₁ := isCoprime_cofactors h hu₁ hv₁
  set d := EuclideanDomain.gcd u v with hd
  refine ⟨u₁, v₁, hu₁, hv₁, hcop, ?_, ?_⟩
  · rw [hu₁, hv₁]; ring
  · exact fun t => sq_add_sq_pos_of_isCoprime hcop t

/-- **Root multiplicity is carried entirely by the gcd.**  Since the primitive part is
positive definite it contributes no real zeros, so in `p = d² · (primitive)` every
real root of `p` comes from `d²`:

    rootMultiplicity r (u² + v²) = 2 · rootMultiplicity r (gcd u v).

This makes the parent entry's `2·min` formula transparent: the multiplicity of `r` in
the gcd is exactly `min (rootMultiplicity r u) (rootMultiplicity r v)`. -/
theorem rootMultiplicity_two_sos {u v : ℝ[X]} (h : ¬ (u = 0 ∧ v = 0)) (r : ℝ) :
    rootMultiplicity r (u ^ 2 + v ^ 2)
      = 2 * rootMultiplicity r (EuclideanDomain.gcd u v) := by
  obtain ⟨u₁, v₁, _, _, _, hfac, hpos⟩ := exists_primitive_factorization h
  set d := EuclideanDomain.gcd u v with hd
  have hd0 : d ≠ 0 := by rw [hd, Ne, EuclideanDomain.gcd_eq_zero_iff]; exact h
  have hq0 : u₁ ^ 2 + v₁ ^ 2 ≠ 0 := by
    intro hc; have hp := hpos r; rw [hc] at hp; simp at hp
  have hqnr : rootMultiplicity r (u₁ ^ 2 + v₁ ^ 2) = 0 := by
    apply rootMultiplicity_eq_zero
    intro hroot
    have hp := hpos r
    rw [IsRoot.def] at hroot
    rw [hroot] at hp
    exact lt_irrefl 0 hp
  rw [hfac, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 2 hd0) hq0), hqnr, add_zero,
    pow_two, rootMultiplicity_mul (mul_ne_zero hd0 hd0)]
  ring

/-- **The primitive part is not an invariant of `p`.**  Coprimality of the summands is
*not* preserved across different 2-SOS decompositions of the same polynomial, so the
"primitive part" of the previous theorem depends on the chosen decomposition, not on
`p` alone.  Witness: `(X² + 1)²` equals both the non-coprime square `(X² + 1)² + 0²`
and the coprime sum `(X² − 1)² + (2X)²`.  This settles the uniqueness half of the open
question negatively. -/
theorem coprimality_not_invariant :
    ∃ p u v s t : ℝ[X],
      p = u ^ 2 + v ^ 2 ∧ p = s ^ 2 + t ^ 2 ∧ IsCoprime u v ∧ ¬ IsCoprime s t := by
  refine ⟨(X ^ 2 + 1) ^ 2, X ^ 2 - 1, 2 * X, X ^ 2 + 1, 0, by ring, by ring, ?_, ?_⟩
  · -- IsCoprime (X² − 1) (2X):  (-1)·(X² − 1) + (½·X)·(2X) = 1
    refine ⟨C (-1), C (1 / 2) * X, ?_⟩
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_C, eval_X, eval_one,
      eval_ofNat]
    ring
  · -- ¬ IsCoprime (X² + 1) 0:  X² + 1 is not a unit (it has degree 2)
    rw [isCoprime_zero_right]
    intro hu
    have h0 : (X ^ 2 + 1 : ℝ[X]).natDegree = 0 := natDegree_eq_zero_of_isUnit hu
    rw [← C_1, natDegree_X_pow_add_C] at h0
    exact absurd h0 (by norm_num)

end Hilbert17OQ01OQ01CoprimeNorm

-- Axiom audit: headline theorems should report only the foundational trio
-- (propext, Classical.choice, Quot.sound) — no sorryAx, no Lean.ofReduceBool.
#print axioms Hilbert17OQ01OQ01CoprimeNorm.sq_add_sq_pos_of_isCoprime
#print axioms Hilbert17OQ01OQ01CoprimeNorm.exists_primitive_factorization
#print axioms Hilbert17OQ01OQ01CoprimeNorm.rootMultiplicity_two_sos
#print axioms Hilbert17OQ01OQ01CoprimeNorm.coprimality_not_invariant
