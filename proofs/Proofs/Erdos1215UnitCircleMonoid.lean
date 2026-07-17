/-
Erdős Problem #1215 (Mac Lane 1953) — the multiplicative structure of the
unit-circle polynomial class.

Parent: `Proofs.Erdos1215Problem`.  Mac Lane's question concerns the class of
polynomials `P` with `P(0) = 1` and *all* roots on the unit circle
(`Erdos1215.IsUnitCirclePolynomial`).  The companion `Erdos1215UnitCircleRadius`
established the *geometric* confinement of the level sets of such polynomials
(sharp radius, compactness, area sandwich).

This file records the *algebraic* fact that the class is closed under the ring
multiplication of `ℂ[X]`: it is a **submonoid** of `ℂ[X]`.  Concretely, if `P`
and `Q` both have value `1` at the origin and all roots on the unit circle, then
so does `P·Q`:

* `(P·Q)(0) = P(0)·Q(0) = 1`;
* a root of `P·Q` is a root of `P` or of `Q`, hence on the unit circle.

The constant polynomial `1` is the unit.  Packaging this as
`unitCircleSubmonoid : Submonoid ℂ[X]` makes the class a monoid under
multiplication, so it is closed under arbitrary finite products and powers
(`IsUnitCirclePolynomial.pow`), and degrees add
(`natDegree_mul_of_isUnitCirclePolynomial`).  Because every member evaluates to
`1 ≠ 0` at the origin, **no unit-circle polynomial vanishes at `0`**
(`zero_not_isRoot`) — the geometric fact underlying Mac Lane's labyrinth (the
origin always sits *inside* the lemniscate, never on it).

All results are `0`-axiom / `0`-sorry, and none invoke the parent's
`maclane_labyrinth` axiom.

Main results:
* `isUnitCirclePolynomial_one`               — `1` is a unit-circle polynomial;
* `IsUnitCirclePolynomial.mul`               — closure under multiplication;
* `IsUnitCirclePolynomial.pow`               — closure under powers;
* `natDegree_mul_of_isUnitCirclePolynomial`  — degrees add on products;
* `unitCircleSubmonoid`                       — the submonoid packaging;
* `zero_not_isRoot`                           — `0` is never a root.
-/

import Mathlib
import Proofs.Erdos1215Problem

open Polynomial

namespace Erdos1215UnitCircleMonoid

open Erdos1215

/-- A unit-circle polynomial is nonzero (its value at `0` is `1 ≠ 0`). -/
theorem ne_zero_of_isUnitCirclePolynomial {P : ℂ[X]}
    (hP : IsUnitCirclePolynomial P) : P ≠ 0 := by
  intro h
  have h0 := hP.1
  rw [h] at h0
  simp at h0

/-- **The constant polynomial `1` is a unit-circle polynomial.**  Its value at `0`
    is `1` and it has no roots at all (`1 ≠ 0` everywhere). -/
theorem isUnitCirclePolynomial_one : IsUnitCirclePolynomial (1 : ℂ[X]) := by
  refine ⟨by simp, ?_⟩
  intro z hz
  rw [IsRoot.def, eval_one] at hz
  exact absurd hz one_ne_zero

/-- **The class is closed under multiplication.**  If `P` and `Q` are unit-circle
    polynomials then so is `P·Q`: the value at `0` multiplies to `1·1 = 1`, and a
    root of `P·Q` is a root of `P` or of `Q`, hence of unit modulus. -/
theorem IsUnitCirclePolynomial.mul {P Q : ℂ[X]}
    (hP : IsUnitCirclePolynomial P) (hQ : IsUnitCirclePolynomial Q) :
    IsUnitCirclePolynomial (P * Q) := by
  refine ⟨?_, ?_⟩
  · rw [eval_mul, hP.1, hQ.1, mul_one]
  · intro z hz
    rw [IsRoot.def, eval_mul, mul_eq_zero] at hz
    rcases hz with h | h
    · exact hP.2 z h
    · exact hQ.2 z h

/-- **The class is closed under powers.**  Iterating `IsUnitCirclePolynomial.mul`
    from the unit `1` shows `P^n` is a unit-circle polynomial for every `n`. -/
theorem IsUnitCirclePolynomial.pow {P : ℂ[X]} (hP : IsUnitCirclePolynomial P) :
    ∀ n : ℕ, IsUnitCirclePolynomial (P ^ n)
  | 0 => by simpa using isUnitCirclePolynomial_one
  | n + 1 => by
      rw [pow_succ]
      exact IsUnitCirclePolynomial.mul (IsUnitCirclePolynomial.pow hP n) hP

/-- **Degrees add on products of unit-circle polynomials.**  Both factors are
    nonzero, so `natDegree` is additive: `deg(P·Q) = deg P + deg Q`.  In particular
    the sharp confinement radius `1 + C^{1/deg}` of the radius companion uses the
    summed degree for products. -/
theorem natDegree_mul_of_isUnitCirclePolynomial {P Q : ℂ[X]}
    (hP : IsUnitCirclePolynomial P) (hQ : IsUnitCirclePolynomial Q) :
    (P * Q).natDegree = P.natDegree + Q.natDegree :=
  natDegree_mul (ne_zero_of_isUnitCirclePolynomial hP) (ne_zero_of_isUnitCirclePolynomial hQ)

/-- **The unit-circle polynomials form a submonoid of `ℂ[X]`.**  Closed under
    multiplication (`IsUnitCirclePolynomial.mul`) and containing the unit
    (`isUnitCirclePolynomial_one`) — the algebraic counterpart of the geometric
    confinement theory. -/
def unitCircleSubmonoid : Submonoid ℂ[X] where
  carrier := {P | IsUnitCirclePolynomial P}
  one_mem' := isUnitCirclePolynomial_one
  mul_mem' := fun hP hQ => IsUnitCirclePolynomial.mul hP hQ

/-- Membership in `unitCircleSubmonoid` is exactly `IsUnitCirclePolynomial`. -/
theorem mem_unitCircleSubmonoid {P : ℂ[X]} :
    P ∈ unitCircleSubmonoid ↔ IsUnitCirclePolynomial P :=
  Iff.rfl

/-- A finite product of unit-circle polynomials is a unit-circle polynomial —
    the submonoid closure under `List.prod`. -/
theorem isUnitCirclePolynomial_list_prod {L : List ℂ[X]}
    (hL : ∀ P ∈ L, IsUnitCirclePolynomial P) :
    IsUnitCirclePolynomial L.prod :=
  (mem_unitCircleSubmonoid).1 (list_prod_mem (fun P hP => (mem_unitCircleSubmonoid).2 (hL P hP)))

/-- **No unit-circle polynomial vanishes at the origin.**  Since `P(0) = 1 ≠ 0`,
    the point `0` is never a root — geometrically, the origin always lies strictly
    inside every sublevel set `{|P| ≤ C}` for `C ≥ 1`, the fact underlying Mac
    Lane's labyrinth phenomenon. -/
theorem zero_not_isRoot {P : ℂ[X]} (hP : IsUnitCirclePolynomial P) :
    ¬ P.IsRoot 0 := by
  rw [IsRoot.def, hP.1]
  exact one_ne_zero

end Erdos1215UnitCircleMonoid
