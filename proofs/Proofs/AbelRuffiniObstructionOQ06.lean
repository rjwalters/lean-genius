import Mathlib

/-
# The Abel–Ruffini Obstruction

This file formalizes the *group-theoretic obstruction* at the heart of the
Abel–Ruffini theorem, together with the abstract radical-solvability criterion
that turns it into a statement about polynomials.

## The story

A polynomial equation is *solvable by radicals* exactly when the Galois group of
the polynomial is a *solvable* group (Galois). The Abel–Ruffini theorem says the
general equation of degree `n ≥ 5` is **not** solvable by radicals, because the
relevant Galois group is the full symmetric group `Sₙ`, and:

* `Sₙ` is solvable for `n ≤ 4` (so degrees 1–4 have the classical radical
  formulas — linear, quadratic, Cardano, Ferrari), but
* `Sₙ` is **not** solvable for `n ≥ 5`.

Here we prove the sharp non-solvability half for *all* `n ≥ 5` (generalizing
Mathlib's `Equiv.Perm.fin_5_not_solvable`, which is stated only for `Fin 5`), the
easy solvable cases, and the radical criterion
`not_solvableByRad_of_not_solvable_gal` — the contrapositive of Mathlib's
`solvableByRad.isSolvable'`. The latter is exactly the implication "non-solvable
Galois group ⟹ root not expressible by radicals" that powers every concrete
Abel–Ruffini example.

## Scope

This is the *characteristic-independent core* of the theory: the symmetric-group
obstruction and the Galois criterion. The deep characteristic-`p` refinements
(wild ramification, the Abhyankar conjecture on fundamental groups of curves in
positive characteristic — Raynaud/Harbater) are **out of scope** and remain
unformalized here.
-/

namespace AbelRuffiniObstructionOQ06

open Polynomial

/-!
## Part I: The symmetric-group obstruction
-/

/--
**Non-solvability of `Sₙ` for `n ≥ 5`.**

The symmetric group on `n` symbols is not solvable once `n ≥ 5`. This generalizes
Mathlib's `Equiv.Perm.fin_5_not_solvable` (the `n = 5` case) to every `n ≥ 5`: any
such permutation group contains a copy of `S₅`, whose derived series never reaches
the trivial subgroup because `A₅` is its own commutator subgroup (a perfect,
nonabelian simple group).
-/
theorem symmetricGroup_not_solvable {n : ℕ} (hn : 5 ≤ n) :
    ¬ IsSolvable (Equiv.Perm (Fin n)) := by
  apply Equiv.Perm.not_solvable (Fin n)
  rw [Cardinal.mk_fin]
  exact_mod_cast hn

/--
**Solvability of `S₂`.**

`S₂` is cyclic of order two, hence abelian, hence solvable. (`S₀` and `S₁` are
trivial; the first interesting solvable case is `S₂`.) This is the low end of the
threshold `Sₙ` solvable ⟺ `n ≤ 4`.
-/
theorem perm_fin_two_solvable : IsSolvable (Equiv.Perm (Fin 2)) :=
  isSolvable_of_comm (by decide)

/--
**The symmetric threshold, both endpoints.**

`S₂` is solvable while `Sₙ` is not solvable for any `n ≥ 5`. This is the
group-theoretic skeleton of Abel–Ruffini: solvability of the symmetric group is
exactly what separates the radically-solvable low degrees from the
radically-unsolvable high degrees.
-/
theorem symmetric_threshold :
    IsSolvable (Equiv.Perm (Fin 2)) ∧
    (∀ n : ℕ, 5 ≤ n → ¬ IsSolvable (Equiv.Perm (Fin n))) :=
  ⟨perm_fin_two_solvable, fun _ hn => symmetricGroup_not_solvable hn⟩

/-!
## Part II: The radical-solvability criterion
-/

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

/--
**Abel–Ruffini criterion (Galois form).**

If an element `α` of an extension `E/F` is a root of an *irreducible* polynomial
`q ∈ F[X]` whose Galois group is **not** solvable, then `α` is **not** solvable by
radicals over `F`.

This is the contrapositive of Mathlib's `solvableByRad.isSolvable'`
(solvable-by-radicals ⟹ solvable Galois group), and it is the exact tool used to
exhibit unsolvable quintics: produce an irreducible degree-`5` polynomial whose
Galois group is `S₅` (not solvable by `symmetricGroup_not_solvable`), and its
roots cannot be written with radicals.
-/
theorem not_solvableByRad_of_not_solvable_gal {α : E} {q : F[X]}
    (q_irred : Irreducible q) (q_aeval : aeval α q = 0)
    (hq : ¬ IsSolvable q.Gal) : ¬ IsSolvableByRad F α :=
  fun h => hq (solvableByRad.isSolvable' q_irred q_aeval h)

/--
**Contrapositive restatement: radicals force a solvable Galois group.**

Packaged in the positive direction for convenience: a root that *is* solvable by
radicals must come from an irreducible polynomial with solvable Galois group.
(This is definitionally `solvableByRad.isSolvable'`; we re-expose it under a local
name so the criterion and its converse sit side by side.)
-/
theorem solvable_gal_of_solvableByRad {α : E} {q : F[X]}
    (q_irred : Irreducible q) (q_aeval : aeval α q = 0)
    (hα : IsSolvableByRad F α) : IsSolvable q.Gal :=
  solvableByRad.isSolvable' q_irred q_aeval hα

end AbelRuffiniObstructionOQ06
