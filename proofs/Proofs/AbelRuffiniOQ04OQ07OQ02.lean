/-
  Eliminating the `bringRadical_not_in_radicals` axiom
  (Abel–Ruffini OQ-04-OQ-07-OQ-02)

  ## Background

  The parent entry `AbelRuffiniOQ04OQ07.lean` defines the **Bring radical**
  `BR(t)` analytically: the unique real root of `x⁵ + x + t = 0`, constructed
  via the intermediate value theorem and characterized by strict monotonicity.
  It then asserts — through the axiom `bringRadical_not_in_radicals` — that the
  Bring radical is "not expressible in radicals".

  That axiom is, as written, **degenerate**: its "expressible in radicals"
  predicate is a literal `True`, so the statement
    `¬ ∃ F, (∀ t, F t = bringRadical t) ∧ True`
  is in fact *false* (take `F = bringRadical`). It is a placeholder, not a
  faithful formalization, and it cannot be "proved" because it is not true.

  ## What this file does (0 sorry, 0 axiom)

  We replace that placeholder with the **genuine** Abel–Ruffini statement for
  the Bring radical, machine-checked against Mathlib's real algebraic notion of
  radical-solvability (`IsSolvableByRad`) and the real Galois group
  (`Polynomial.Gal`), following the sibling `AbelRuffiniOQ07NotSolvable.lean`.

  The key bridge — new here — connects the *analytically* defined real number
  `bringRadical (↑t)` to the *algebraic* Bring–Jerrard polynomial
  `X⁵ + X + C t ∈ ℚ[X]`:

    * `bringRadical_aeval` — `BR(↑t)` is a root of `X⁵ + X + C t` over `ℚ`
      (the analytic defining equation, read through `aeval` into `ℝ`).
    * `bringRadical_not_solvableByRad` — if the Bring–Jerrard quintic
      `X⁵ + X + C t` is irreducible over `ℚ` and its Galois group is **not**
      solvable, then `BR(↑t)` is **not solvable by radicals** over `ℚ`. This is
      the contrapositive of Mathlib's Abel–Ruffini theorem
      `solvableByRad.isSolvable'`.
    * `bringRadical_not_solvableByRad_of_iso_S5` — the same conclusion granting
      instead the standard witness `Gal ≃* S₅` (`S₅` is not solvable).
    * `bringRadical_solvableByRad_imp_gal_solvable` — the unconditional
      converse-direction content: radical-solvability of `BR(↑t)` would *force*
      the Galois group to be solvable.

  These are honest, conditional theorems: their hypotheses (irreducibility and
  non-solvability of the specific quintic's Galois group) are exactly the same
  genuinely-open inputs that block the rest of the Abel–Ruffini family in
  Mathlib v4.26 (the Dedekind–Frobenius bridge giving `Gal ≃ S₅`). What this
  file certifies is that **everything downstream of those inputs is now formal**:
  the previously degenerate axiom is replaced by a correct statement reduced to
  exactly its open hypotheses, with no axioms and no sorries of its own.

  ## References
  - Abel, N. H. (1824). Proof of the impossibility of solving the general
    quintic.
  - Mathlib, `Mathlib/FieldTheory/AbelRuffini.lean` (`solvableByRad.isSolvable'`).
  - Sibling: `AbelRuffiniOQ07NotSolvable.lean` (the same reduction for
    `X⁵ − X − 1`).
-/

import Proofs.AbelRuffiniOQ04OQ07
import Mathlib.FieldTheory.AbelRuffini
import Mathlib.GroupTheory.Solvable

open Polynomial

namespace AbelRuffiniOQ04OQ07OQ02

open BringJerrardReduction

/-- The **Bring–Jerrard quintic** over `ℚ` with parameter `t`:
`bjPoly t = X⁵ + X + C t`. Its real roots are exactly the Bring radicals
`BR(t)` of the parent entry. -/
noncomputable def bjPoly (t : ℚ) : ℚ[X] := X ^ 5 + X + C t

/-- **The analytic–algebraic bridge.** The real number `bringRadical (↑t)`,
defined in the parent entry as the unique real root of `x⁵ + x + t = 0` (via the
intermediate value theorem), is a root of the rational polynomial
`bjPoly t = X⁵ + X + C t` in the sense of `aeval` through the `ℚ`-algebra `ℝ`.

This is the link that lets us feed the *analytically* constructed Bring radical
into Mathlib's *algebraic* Abel–Ruffini machinery. -/
theorem bringRadical_aeval (t : ℚ) :
    aeval (bringRadical (t : ℝ)) (bjPoly t) = 0 := by
  have h := bringRadical_spec (t : ℝ)
  simp only [bjPoly, map_add, map_pow, aeval_X, aeval_C, eq_ratCast]
  linear_combination h

/-- **No solvability by radicals (Galois form).** If the Bring–Jerrard quintic
`X⁵ + X + C t` is irreducible over `ℚ` and its Galois group is not solvable,
then the Bring radical `BR(↑t)` is **not solvable by radicals** over `ℚ`.

This is the contrapositive of Mathlib's Abel–Ruffini theorem
`solvableByRad.isSolvable'`: an irreducible polynomial with a radical-solvable
root has solvable Galois group. It is the faithful replacement for the parent's
degenerate `bringRadical_not_in_radicals` axiom. -/
theorem bringRadical_not_solvableByRad (t : ℚ)
    (hirr : Irreducible (bjPoly t))
    (hns : ¬ IsSolvable (bjPoly t).Gal) :
    ¬ IsSolvableByRad ℚ (bringRadical (t : ℝ)) :=
  fun h => hns (solvableByRad.isSolvable' hirr (bringRadical_aeval t) h)

/-- **The unconditional converse content.** If the Bring radical `BR(↑t)` *were*
solvable by radicals over `ℚ`, then — given irreducibility of `X⁵ + X + C t` —
the Galois group of the quintic would be solvable. This is the direct content of
`solvableByRad.isSolvable'`, the engine behind the non-solvability statement
above. -/
theorem bringRadical_solvableByRad_imp_gal_solvable (t : ℚ)
    (hirr : Irreducible (bjPoly t))
    (h : IsSolvableByRad ℚ (bringRadical (t : ℝ))) :
    IsSolvable (bjPoly t).Gal :=
  solvableByRad.isSolvable' hirr (bringRadical_aeval t) h

/-- An isomorphism `(bjPoly t).Gal ≃* S₅` forces the Galois group to be **not
solvable**: `S₅` is not solvable (`Equiv.Perm.fin_5_not_solvable`), and
solvability transfers across the (surjective) isomorphism. -/
theorem gal_not_solvable_of_iso_S5 {t : ℚ}
    (e : (bjPoly t).Gal ≃* Equiv.Perm (Fin 5)) :
    ¬ IsSolvable (bjPoly t).Gal := by
  intro h
  haveI : IsSolvable (bjPoly t).Gal := h
  have hsurj : Function.Surjective (e.toMonoidHom) := fun y => ⟨e.symm y, by simp⟩
  exact Equiv.Perm.fin_5_not_solvable (solvable_of_surjective hsurj)

/-- **Capstone — the Abel–Ruffini conclusion for the Bring radical, reduced to
its open input.** Granting that the Bring–Jerrard quintic `X⁵ + X + C t` is
irreducible over `ℚ` with full symmetric Galois group (`Gal ≃* S₅` — the
standard witness, the Dedekind–Frobenius bridge being the only genuinely-open
piece in Mathlib v4.26), the Bring radical `BR(↑t)` is **not solvable by
radicals** over `ℚ`.

Everything except the irreducibility and `S₅` hypotheses is machine-checked: the
non-solvability of `S₅`, its transport across the iso, the analytic–algebraic
root bridge, and Mathlib's Abel–Ruffini theorem. The degenerate parent axiom
`bringRadical_not_in_radicals` is thereby replaced by a correct conditional
theorem with **no axioms and no sorries**. -/
theorem bringRadical_not_solvableByRad_of_iso_S5 (t : ℚ)
    (hirr : Irreducible (bjPoly t))
    (e : (bjPoly t).Gal ≃* Equiv.Perm (Fin 5)) :
    ¬ IsSolvableByRad ℚ (bringRadical (t : ℝ)) :=
  bringRadical_not_solvableByRad t hirr (gal_not_solvable_of_iso_S5 e)

end AbelRuffiniOQ04OQ07OQ02
