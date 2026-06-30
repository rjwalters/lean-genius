/-
  Abel–Ruffini, concrete-quintic branch (oq-04-oq-01), open question oq-02:

      "Generalize to transitive subgroups of `S_n` via Galois theory."

  The parent entry (`AbelRuffiniOQ04OQ01`, "Gal(x⁵ − 4x + 2) ≅ S₅") computes a
  *single* Galois group by hand, and the sibling `AbelRuffiniOQ04OQ01OQ04`
  proves the abstract group-theory lemma "a transitive subgroup of `S_p`
  (`p` prime) containing a transposition is all of `S_p`" — but takes the
  transitivity `[IsPretransitive G α]` as a *hypothesis*. Neither file records
  the Galois-theoretic fact that supplies that hypothesis in the first place:

      **the Galois group of an irreducible polynomial really is a transitive
      subgroup of the symmetric group on its roots.**

  This file fills that gap, axiom-free, working over an *arbitrary* base field
  and for an *arbitrary* degree (not just the prime-degree quintic case):

  * `galActionHom_range_isPretransitive` — for an irreducible `p` that splits in
    `E`, the image `(galActionHom p E).range ≤ Equiv.Perm (rootSet p E)` acts
    transitively on the roots. This is the precise sense in which `Gal p` *is a
    transitive subgroup of `S_n`* (`n = #roots`); it is the Galois-theoretic
    input that the sibling `eq_top_of_isPretransitive_of_mem_isSwap` consumes.
  * `galMulEquivRange` — `Gal p ≃* (galActionHom p E).range`, packaging the
    standard injectivity of `galActionHom` so that `Gal p` is *literally*
    realised as a (transitive) permutation group of the roots.
  * `natDegree_dvd_card` — the orbit–stabiliser payoff in Galois-theoretic
    form: for any irreducible `p` (char `0`), `p.natDegree ∣ Nat.card p.Gal`.
    This **generalises Mathlib's `Polynomial.Gal.prime_degree_dvd_card`**, which
    states the same divisibility only when `p.natDegree` is prime; the parent
    entry used the prime case as Stage 3's "5 ∣ |Gal|".

  Together these say: passing from the concrete quintic to general `n` is not
  ad hoc — every irreducible polynomial hands you a transitive subgroup of `Sₙ`,
  with `n ∣ |Gal|` automatically.
-/

import Mathlib

open Polynomial Polynomial.Gal MulAction
open scoped IntermediateField

namespace AbelRuffiniOQ04OQ01OQ02

variable {F : Type*} [Field F] (p : F[X]) (E : Type*) [Field E] [Algebra F E]

/-- **The Galois group of an irreducible polynomial is a transitive subgroup of
the symmetric group on its roots.**

For an irreducible `p` that splits in `E`, the image of the permutation
representation `galActionHom p E : p.Gal →* Equiv.Perm (rootSet p E)` is a
subgroup of `Equiv.Perm (rootSet p E)` whose tautological action on the roots is
transitive. Mathlib's `Polynomial.Gal.galAction_isPretransitive` gives
transitivity of the `p.Gal`-action; this transports it to the realised
permutation subgroup, which is exactly "a transitive subgroup of `Sₙ`". -/
theorem galActionHom_range_isPretransitive
    [Fact ((p.map (algebraMap F E)).Splits)] (hp : Irreducible p) :
    MulAction.IsPretransitive (galActionHom p E).range (p.rootSet E) := by
  have ht := galAction_isPretransitive p E hp
  refine ⟨fun x y => ?_⟩
  obtain ⟨g, hg⟩ := ht.exists_smul_eq x y
  -- `galActionHom p E g` lies in the range and acts on `x` exactly as `g` does.
  refine ⟨⟨galActionHom p E g, g, rfl⟩, ?_⟩
  have hstep : (⟨galActionHom p E g, g, rfl⟩ : (galActionHom p E).range) • x
      = g • x := rfl
  rw [hstep]
  exact hg

/-- `Gal p` is realised, via `galActionHom`, as the transitive permutation
subgroup `(galActionHom p E).range` of `Equiv.Perm (rootSet p E)`. This packages
Mathlib's `galActionHom_injective` as the group isomorphism onto the range. -/
noncomputable def galMulEquivRange [Fact ((p.map (algebraMap F E)).Splits)] :
    p.Gal ≃* (galActionHom p E).range :=
  MonoidHom.ofInjective (galActionHom_injective p E)

/-- **Degree divides the order of the Galois group, in any degree.**

For an irreducible polynomial `p` over a characteristic-zero field,
`p.natDegree ∣ Nat.card p.Gal`. This is the orbit–stabiliser consequence of the
transitive action on the `natDegree`-many roots, and it generalises Mathlib's
`Polynomial.Gal.prime_degree_dvd_card` (which assumes `p.natDegree` prime).

The proof mirrors Mathlib's prime-degree argument: it only used primality to
secure `p.degree ≠ 0`, which for an irreducible polynomial is automatic
(`Irreducible.natDegree_pos`). -/
theorem natDegree_dvd_card [CharZero F] (hirr : Irreducible p) :
    p.natDegree ∣ Nat.card p.Gal := by
  rw [Polynomial.Gal.card_of_separable hirr.separable]
  have hdeg : p.degree ≠ 0 := fun h =>
    (hirr.natDegree_pos).ne' (natDegree_eq_zero_iff_degree_le_zero.mpr h.le)
  let α : p.SplittingField :=
    rootOfSplits (SplittingField.splits p) (by rwa [degree_map])
  have hα : IsIntegral F α := .of_finite F α
  use Module.finrank F⟮α⟯ p.SplittingField
  suffices (minpoly F α).natDegree = p.natDegree by
    letI _ : AddCommGroup F⟮α⟯ := Ring.toAddCommGroup
    rw [← Module.finrank_mul_finrank F F⟮α⟯ p.SplittingField,
      IntermediateField.adjoin.finrank hα, this]
  suffices minpoly F α ∣ p by
    have key := (minpoly.irreducible hα).dvd_symm hirr this
    apply le_antisymm
    · exact natDegree_le_of_dvd this hirr.ne_zero
    · exact natDegree_le_of_dvd key (minpoly.ne_zero hα)
  apply minpoly.dvd F α
  rw [← eval_map_algebraMap, eval_rootOfSplits]

end AbelRuffiniOQ04OQ01OQ02
