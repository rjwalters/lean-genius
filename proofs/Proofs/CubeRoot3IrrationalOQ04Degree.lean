/-
  ∛3 is not a quadratic irrational  (OQ-04, Half (a))
  ===================================================

  Companion to `CubeRoot3IrrationalOQ04.lean`. Authored under a verification
  blackout (Docker build + Aristotle `prove` both unavailable). All Mathlib
  identifiers below were name-checked against the repo's pinned Mathlib v4.26.0
  (`~/GitHub/mathlib4` @ rev 2df2f0150c…), but the proofs have NOT been
  machine-checked. UNREGISTERED (not imported by `Proofs.lean`) — do not
  register until a live build session verifies it.

  ── Why this file ────────────────────────────────────────────────────────
  The open question for this slug is that the regular continued fraction of ∛3
  is not eventually periodic (hence ∛3 has no finite-state CF description).
  Prior sessions (S18/S19) factored the missing non-periodicity theorem into:

    Half (a)  ∛3 is NOT a quadratic irrational  — formalizable NOW (this file).
    Half (b)  Lagrange's CF theorem (quadratic-irrational ⟺ eventually-periodic
              simple CF) — CONFIRMED ABSENT from Mathlib v4.26.0 (the real
              blocker; a substantial standalone development).

  This file discharges Half (a): `minpoly ℚ ∛3 = X³ − 3`, so `∛3` has algebraic
  degree 3 ≠ 2 and is therefore not a quadratic irrational. Combined with
  Half (b) (when it lands upstream), the contrapositive of Lagrange's theorem
  would give the non-periodicity conclusion directly.

  ── Bearers (Mathlib v4.26.0) ─────────────────────────────────────────────
    X_pow_sub_C_irreducible_iff_of_prime   (FieldTheory/KummerPolynomial:123)
      hp.Prime → (Irreducible (X^p − C a) ↔ ∀ b, b^p ≠ a)
    minpoly.eq_of_irreducible_of_monic     (FieldTheory/Minpoly/Field:139)
      Irreducible p → aeval x p = 0 → p.Monic → p = minpoly A x
    monic_X_pow_sub_C                       (Algebra/Polynomial/Monic:440)
    natDegree_X_pow_sub_C                   (…/Degree/Operations:790)
    Odd.strictMono_pow                      (Algebra/Order/Ring/Basic:193)
    CubeRoot3Irrational.irrational_cbrt3 / cbrt3_cubed   (parent file)
-/
import Mathlib
import Proofs.CubeRoot3Irrational

open Polynomial CubeRoot3Irrational

namespace CubeRoot3IrrationalOQ04Degree

/-- `3` has no cube root in `ℚ`. Reduces to the parent's `irrational_cbrt3`:
if `b^3 = 3` in `ℚ` then `(b : ℝ)^3 = ∛3 ^ 3`, and `x ↦ x^3` is injective on `ℝ`
(odd power, strictly monotone), so `(b : ℝ) = ∛3` would make `∛3` rational. -/
theorem not_cube : ∀ b : ℚ, b ^ 3 ≠ 3 := by
  intro b hb
  have hcast : ((b : ℝ)) ^ 3 = cbrt3 ^ 3 := by
    rw [cbrt3_cubed]; exact_mod_cast hb
  have hbeq : ((b : ℝ)) = cbrt3 :=
    (Odd.strictMono_pow (by decide : Odd 3)).injective hcast
  exact irrational_cbrt3 ⟨b, hbeq⟩

/-- `X³ − 3` is irreducible over `ℚ` (Kummer / Eisenstein at the prime 3). -/
theorem irreducible_X_pow_three_sub_C :
    Irreducible (X ^ 3 - C (3 : ℚ)) :=
  (X_pow_sub_C_irreducible_iff_of_prime (by norm_num : Nat.Prime 3)).mpr not_cube

/-- `∛3` is a root of `X³ − 3`. -/
theorem aeval_cbrt3 : (aeval cbrt3) (X ^ 3 - C (3 : ℚ)) = 0 := by
  have h3 : (algebraMap ℚ ℝ) (3 : ℚ) = (3 : ℝ) := by norm_num
  simp only [map_sub, map_pow, aeval_X, aeval_C, h3]
  rw [cbrt3_cubed]; norm_num

/-- **The minimal polynomial of `∛3` over `ℚ` is `X³ − 3`.** -/
theorem minpoly_cbrt3 : minpoly ℚ cbrt3 = X ^ 3 - C (3 : ℚ) :=
  (minpoly.eq_of_irreducible_of_monic
    irreducible_X_pow_three_sub_C
    aeval_cbrt3
    (monic_X_pow_sub_C (3 : ℚ) (by norm_num))).symm

/-- **`∛3` has algebraic degree 3 over `ℚ`.** -/
theorem natDegree_minpoly_cbrt3 : (minpoly ℚ cbrt3).natDegree = 3 := by
  rw [minpoly_cbrt3, natDegree_X_pow_sub_C]

/-- **`∛3` is not a quadratic irrational** (its minimal polynomial has degree 3,
not 2). This is Half (a) of the non-periodicity factorization; the remaining
Half (b), Lagrange's continued-fraction theorem, is absent from Mathlib. -/
theorem cbrt3_not_quadratic : (minpoly ℚ cbrt3).natDegree ≠ 2 := by
  rw [natDegree_minpoly_cbrt3]; decide

end CubeRoot3IrrationalOQ04Degree
