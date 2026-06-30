/-
  The Abel–Ruffini payoff for f = X⁵ − X − 1, machine-checked
  (Open Question OQ-07 of abel-ruffini, "not solvable by radicals" conclusion)

  ## Background
  The sibling entries (`AbelRuffiniOQ07.lean`, `…Discriminant.lean`, `…Order6.lean`)
  establish the *group-theoretic* core of the Abel–Ruffini witness `X⁵ − X − 1`:

    * `5 ∣ |Gal(f)|` is proved **unconditionally** for the real Galois group
      (`five_dvd_card_gal_unconditional`, via Selmer irreducibility + prime degree);
    * the abstract `S₅` assembly criteria (transposition route, 3-cycle/Jordan route)
      are fully verified for `Subgroup (Perm (Fin 5))`.

  The headline `Gal(f) ≅ S₅` remains genuinely open in Mathlib v4.26 — it is blocked
  on the **Dedekind–Frobenius bridge** (factor type of `f` mod an unramified prime ⟹ a
  Frobenius element of matching cycle type *inside the actual* `f.Gal`), which Mathlib
  does not yet provide (no `decompositionGroup` / `arithFrobAt` for number fields, no
  discriminant ⟺ alternating-group bridge).

  ## What this file adds (0 sorry, 0 axiom)
  All the sibling files describe the *final* conclusion — "hence `X⁵ − X − 1` is **not
  solvable by radicals**" — only in **prose**. This file machine-checks that last step
  via Mathlib's Abel–Ruffini theorem (`solvableByRad.isSolvable'`):

    * `gal_not_solvable_of_iso_S5` — an isomorphism `f.Gal ≃* S₅` makes `f.Gal` not
      solvable (`Equiv.Perm.fin_5_not_solvable`: `S₅` is not solvable, transported
      across the iso).
    * `root_not_solvableByRad_of_gal_not_solvable` — if `f.Gal` is not solvable then
      **no** root of `f` (in any `ℚ`-field extension) is solvable by radicals. This is
      the contrapositive of Mathlib's `solvableByRad.isSolvable'` applied to the
      (Selmer-)irreducible `f`.
    * `root_not_solvableByRad_of_gal_iso_S5` — the **capstone**: granting the single
      genuinely-open fact `f.Gal ≃* S₅`, the roots of `X⁵ − X − 1` are not solvable by
      radicals. The Abel–Ruffini conclusion of OQ-07, reduced to exactly its open input.

  Nothing here closes the open bridge; it certifies that the *only* missing piece is the
  iso `f.Gal ≅ S₅`, and that everything downstream of it (the actual unsolvability) is
  fully machine-checked against the real `Polynomial.Gal` and the real `IsSolvableByRad`.

  ## References
  - Selmer, E. S. (1956). "On the irreducibility of certain trinomials." Math. Scand. 4.
  - Mathlib, `Mathlib/FieldTheory/AbelRuffini.lean` (`solvableByRad.isSolvable'`).
-/

import Mathlib.FieldTheory.AbelRuffini
import Mathlib.GroupTheory.Solvable
import Mathlib.RingTheory.Polynomial.Selmer

open Polynomial

namespace AbelRuffiniOQ07NotSolvable

/-- The Abel–Ruffini witness `f = X⁵ − X − 1 ∈ ℚ[X]`. -/
noncomputable def f : ℚ[X] := X ^ 5 - X - 1

/-- **`f = X⁵ − X − 1` is irreducible over `ℚ`** — Selmer's theorem, from Mathlib
(`Polynomial.X_pow_sub_X_sub_one_irreducible_rat` at `n = 5`). -/
theorem f_irreducible : Irreducible f := by
  unfold f
  exact X_pow_sub_X_sub_one_irreducible_rat (by norm_num)

/-- An isomorphism `f.Gal ≃* S₅` forces `f.Gal` to be **not solvable**: `S₅` is not
solvable (`Equiv.Perm.fin_5_not_solvable`), and solvability transfers across a
surjective hom, so a solvable `f.Gal` would make `S₅` solvable. -/
theorem gal_not_solvable_of_iso_S5 (e : f.Gal ≃* Equiv.Perm (Fin 5)) :
    ¬ IsSolvable f.Gal := by
  intro h
  haveI : IsSolvable f.Gal := h
  have hsurj : Function.Surjective (e.toMonoidHom) := fun y => ⟨e.symm y, by simp⟩
  exact Equiv.Perm.fin_5_not_solvable (solvable_of_surjective hsurj)

/-- **No root of `f` is solvable by radicals, given a non-solvable Galois group.**
If `f.Gal` is not solvable then for every root `α` of `f` in any `ℚ`-extension `E`,
`α` is not solvable by radicals. This is the contrapositive of Mathlib's Abel–Ruffini
theorem `solvableByRad.isSolvable'` (an irreducible polynomial with a radical-solvable
root has solvable Galois group), with irreducibility supplied by Selmer. -/
theorem root_not_solvableByRad_of_gal_not_solvable
    {E : Type*} [Field E] [Algebra ℚ E]
    (hns : ¬ IsSolvable f.Gal) {α : E} (hα : aeval α f = 0) :
    ¬ IsSolvableByRad ℚ α :=
  fun h => hns (solvableByRad.isSolvable' f_irreducible hα h)

/-- **Capstone — the Abel–Ruffini conclusion of OQ-07, reduced to its open input.**
Granting the single genuinely-open fact `f.Gal ≃* S₅` (the Dedekind–Frobenius bridge),
every root of `X⁵ − X − 1` in any `ℚ`-extension is **not solvable by radicals**.

Everything except the iso hypothesis is machine-checked: the unsolvability of `S₅`, its
transport to `f.Gal`, and Mathlib's Abel–Ruffini theorem applied to the (Selmer-)
irreducible `f`. The previously prose-only conclusion "hence `X⁵ − X − 1` is not solvable
by radicals" is now formal, conditional on exactly the headline open isomorphism. -/
theorem root_not_solvableByRad_of_gal_iso_S5
    {E : Type*} [Field E] [Algebra ℚ E]
    (e : f.Gal ≃* Equiv.Perm (Fin 5)) {α : E} (hα : aeval α f = 0) :
    ¬ IsSolvableByRad ℚ α :=
  root_not_solvableByRad_of_gal_not_solvable (gal_not_solvable_of_iso_S5 e) hα

end AbelRuffiniOQ07NotSolvable
