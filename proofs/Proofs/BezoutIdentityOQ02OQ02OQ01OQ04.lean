import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-
# Bézout Quotient Formula in Non-Commutative Rings

## Research Problem: bezout-identity-oq-02-oq-02-oq-01-oq-04

Open question 4 from the parent (Constructive Divisibility Algorithm via Bézout
Coefficients, `bezout-identity-oq-02-oq-02-oq-01`):

> "Can the quotient formula be generalized to non-commutative rings (e.g., matrix
>  rings) where Euclid's lemma fails?"

The parent's core result, in a **commutative** ring, is:

  if `u*a + v*b = 1` and `b*c = a*k`, then `a*(u*c + v*k) = c`,

which yields `a ∣ c` — a constructive form of Euclid's lemma.

## Answer: PARTIALLY — the formula needs a commutativity condition, and that
condition is genuinely necessary.

**Salvage (positive direction).** Tracking the algebra in a general ring,

  c = (u*a + v*b)*c = u*(a*c) + v*(b*c) = u*(a*c) + v*(a*k),

so the only obstruction to factoring `a` out on the left is whether `a` commutes
with the Bézout coefficients `u, v`. We prove that **if `a` commutes with `u` and
`v`, the formula holds in any ring** (`quotient_formula_comm`), with a right-handed
twin, a central-element corollary, and the original commutative result recovered as
a special case. From it we get a constructive Euclid's lemma for central `a`.

**Necessity (negative direction).** Over the non-commutative ring
`M₂(ℤ/2)`, we exhibit explicit matrices `a, b, c, u, v, k` with

  `u*a + v*b = 1` (identity)   and   `b*c = a*k`,   but   `a*(u*c + v*k) ≠ c`.

Here `a` does **not** commute with `u`, so the hypothesis of `quotient_formula_comm`
fails — and so does its conclusion. This shows the commutativity condition is not a
proof artifact: Euclid's lemma and the quotient formula genuinely break in matrix
rings.

## Status (0 sorries, 0 `axiom` declarations)

The matrix counterexample is verified by kernel `decide` (NOT `native_decide`), so the
file is axiom-free aside from the usual `propext`/`Classical.choice`/`Quot.sound`.

## References
- Parent: bezout-identity-oq-02-oq-02-oq-01 (constructive quotient formula)
- Lam (2001): "A First Course in Noncommutative Rings"
-/

set_option linter.unusedVariables false

namespace BezoutNoncomm

-- ============================================================
-- PART I: The salvage — the quotient formula under commutativity
-- ============================================================

/-- **Quotient formula in a general ring.** If `u*a + v*b = 1` and `b*c = a*k`, and `a`
    commutes with both Bézout coefficients `u` and `v`, then `a*(u*c + v*k) = c`.

    The two `Commute` hypotheses are exactly what is needed to pull `a` out on the left;
    in a commutative ring they hold automatically (see `quotient_formula_commRing`). -/
theorem quotient_formula_comm {R : Type*} [Ring R] {a b c k u v : R}
    (hbez : u * a + v * b = 1) (hk : b * c = a * k)
    (hu : Commute a u) (hv : Commute a v) :
    a * (u * c + v * k) = c := by
  have hau : a * (u * c) = u * (a * c) := by
    rw [← mul_assoc, hu.eq, mul_assoc]
  have hav : a * (v * k) = v * (a * k) := by
    rw [← mul_assoc, hv.eq, mul_assoc]
  have hcollect : u * (a * c) + v * (b * c) = (u * a + v * b) * c := by
    noncomm_ring
  rw [mul_add, hau, hav, ← hk, hcollect, hbez, one_mul]

/-- **Right-handed quotient formula.** The mirror image: if `a*u + b*v = 1` and
    `c*b = k*a`, and `a` commutes with `u` and `v`, then `(c*u + k*v)*a = c`. -/
theorem quotient_formula_comm_right {R : Type*} [Ring R] {a b c k u v : R}
    (hbez : a * u + b * v = 1) (hk : c * b = k * a)
    (hu : Commute a u) (hv : Commute a v) :
    (c * u + k * v) * a = c := by
  have h1 : c * u * a = c * a * u := by
    rw [mul_assoc, hu.symm.eq, ← mul_assoc]
  have h2 : k * v * a = k * a * v := by
    rw [mul_assoc, hv.symm.eq, ← mul_assoc]
  have hcollect : c * a * u + c * b * v = c * (a * u + b * v) := by
    noncomm_ring
  rw [add_mul, h1, h2, ← hk, hcollect, hbez, mul_one]

/-- **Central-element corollary.** If `a` is central (commutes with every element), the
    explicit `Commute` hypotheses are automatic. -/
theorem quotient_formula_central {R : Type*} [Ring R] {a b c k u v : R}
    (hbez : u * a + v * b = 1) (hk : b * c = a * k)
    (hcentral : ∀ x : R, Commute a x) :
    a * (u * c + v * k) = c :=
  quotient_formula_comm hbez hk (hcentral u) (hcentral v)

/-- **Commutative recovery.** In a commutative ring every pair commutes, so the parent's
    quotient formula is the special case of `quotient_formula_comm` with no side
    conditions. -/
theorem quotient_formula_commRing {R : Type*} [CommRing R] {a b c k u v : R}
    (hbez : u * a + v * b = 1) (hk : b * c = a * k) :
    a * (u * c + v * k) = c :=
  quotient_formula_comm hbez hk (Commute.all a u) (Commute.all a v)

/-- **Constructive Euclid's lemma for a central element.** If `a` is central, coprime to
    `b` (witnessed by Bézout coefficients), and divides `b*c`, then `a ∣ c` — with the
    explicit quotient `u*c + v*k`. -/
theorem euclids_lemma_central {R : Type*} [Ring R] {a b c : R}
    (hcentral : ∀ x : R, Commute a x) (u v : R) (hbez : u * a + v * b = 1)
    (k : R) (hk : b * c = a * k) :
    a ∣ c :=
  ⟨u * c + v * k, (quotient_formula_central hbez hk hcentral).symm⟩

-- ============================================================
-- PART II: Necessity — the formula fails over M₂(ℤ/2)
-- ============================================================

open Matrix

/-- The non-commutative ring of 2×2 matrices over `ℤ/2`. -/
abbrev M := Matrix (Fin 2) (Fin 2) (ZMod 2)

/-- `a = [[0,0],[1,0]]`. -/
def aM : M := !![0, 0; 1, 0]
/-- `b = [[0,0],[0,1]]`. -/
def bM : M := !![0, 0; 0, 1]
/-- `c = [[0,1],[0,0]]` (nonzero). -/
def cM : M := !![0, 1; 0, 0]
/-- `u = [[0,1],[0,0]]`, a left Bézout coefficient. -/
def uM : M := !![0, 1; 0, 0]
/-- `v = [[0,0],[0,1]]`, a left Bézout coefficient. -/
def vM : M := !![0, 0; 0, 1]
/-- `k = 0`, the divisibility witness (`b*c = 0 = a*k`). -/
def kM : M := !![0, 0; 0, 0]

/-- The Bézout relation holds: `u*a + v*b = 1`. -/
theorem counterexample_bezout : uM * aM + vM * bM = 1 := by decide

/-- The divisibility witness holds: `b*c = a*k` (both are the zero matrix). -/
theorem counterexample_div : bM * cM = aM * kM := by decide

/-- `c` is genuinely nonzero, so the failure below is not a degenerate `c = 0` case. -/
theorem counterexample_c_ne_zero : cM ≠ 0 := by decide

/-- **The quotient formula fails.** Despite `u*a + v*b = 1` and `b*c = a*k`, we have
    `a*(u*c + v*k) ≠ c`. Concretely the left side is the zero matrix while `c ≠ 0`. -/
theorem counterexample_formula_fails : aM * (uM * cM + vM * kM) ≠ cM := by decide

/-- The reason: `a` does not commute with the Bézout coefficient `u`, so the hypothesis
    of `quotient_formula_comm` is violated. -/
theorem counterexample_not_commute : ¬ Commute aM uM := by
  show aM * uM ≠ uM * aM
  decide

/-- **Euclid's lemma itself fails here.** `a` divides `b*c` (it is `0 = a*0`) and `a, b`
    are Bézout-coprime, yet `a ∤ c`: no matrix `q` satisfies `c = a*q`, because every
    product `a*q` has zero top row while `c` does not. -/
theorem counterexample_not_dvd : ¬ aM ∣ cM := by
  rintro ⟨q, hq⟩
  -- Compare the (0,1) entries: cM 0 1 = 1, but (aM*q) 0 1 = 0 since aM's top row is 0.
  have e := congrFun (congrFun hq 0) 1
  simp [aM, cM, Matrix.mul_apply, Fin.sum_univ_two] at e

/-- **Summary of necessity.** There is a (non-commutative) ring and elements satisfying
    the Bézout relation and the divisibility witness for which the quotient formula fails.
    Hence the commutativity hypothesis in `quotient_formula_comm` cannot be dropped. -/
theorem quotient_formula_needs_commutativity :
    ∃ (R : Type) (_ : Ring R) (a b c k u v : R),
      u * a + v * b = 1 ∧ b * c = a * k ∧ a * (u * c + v * k) ≠ c :=
  ⟨M, inferInstance, aM, bM, cM, kM, uM, vM,
    counterexample_bezout, counterexample_div, counterexample_formula_fails⟩

end BezoutNoncomm
