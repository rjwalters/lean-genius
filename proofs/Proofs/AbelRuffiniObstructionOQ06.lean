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
**Solvability of `S₃`.**

`S₃` is solvable: the alternating subgroup `A₃ = ker(sign)` has order `3!/2 = 3`, a
prime, so it is cyclic, hence abelian, hence solvable; and the quotient `S₃/A₃ ↪ ℤˣ`
(through `sign`) is abelian. Solvability is closed under such extensions
(`solvable_of_ker_le_range`), so `S₃` is solvable. This is the next step of the
positive side of the threshold above `S₂`. -/
theorem perm_fin_three_solvable : IsSolvable (Equiv.Perm (Fin 3)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]; decide
  haveI : IsCyclic (alternatingGroup (Fin 3)) := isCyclic_of_prime_card hcard
  haveI : IsSolvable (alternatingGroup (Fin 3)) :=
    isSolvable_of_comm (fun a b => IsCyclic.commutative.comm a b)
  refine solvable_of_ker_le_range
    (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign ?_
  rw [Subgroup.range_subtype]
  exact le_of_eq alternatingGroup_eq_sign_ker.symm

/--
**Solvability of `A₄` (the alternating group on four symbols).**

`A₄` is solvable via its own one-step extension
`1 → V₄ → A₄ → A₄/V₄ → 1`, where the normal Klein four-subgroup
`V₄ = alternatingGroup.kleinFour (Fin 4)` has exponent two (hence is abelian,
hence solvable) and the quotient `A₄/V₄` has order `|A₄|/|V₄| = 12/4 = 3`, so it
is cyclic of prime order, hence abelian, hence solvable. (`V₄` is in fact the
commutator subgroup of `A₄`, so this is exactly the derived series
`A₄ ⊳ V₄ ⊳ 1`.) This is the crucial non-abelian-but-solvable case that makes the
general quartic solvable by radicals (Ferrari's resolvent cubic).
-/
theorem alt_fin_four_solvable : IsSolvable (alternatingGroup (Fin 4)) := by
  have hcard : Nat.card (Fin 4) = 4 := by simp
  haveI hnorm : (alternatingGroup.kleinFour (Fin 4)).Normal :=
    alternatingGroup.normal_kleinFour hcard
  -- The kernel V₄ has exponent two, hence is abelian, hence solvable.
  haveI hkSolv : IsSolvable (alternatingGroup.kleinFour (Fin 4)) :=
    isSolvable_of_comm
      (mul_comm_of_exponent_two (alternatingGroup.exponent_kleinFour_of_card_eq_four hcard))
  -- The quotient A₄/V₄ has order 3, hence is cyclic, hence solvable.
  have hcard3 : Nat.card (alternatingGroup (Fin 4) ⧸ alternatingGroup.kleinFour (Fin 4)) = 3 := by
    rw [← Nat.mul_left_inj (a := Nat.card (alternatingGroup.kleinFour (Fin 4)))]
    · rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup]
      rw [alternatingGroup.card_of_card_eq_four hcard,
        alternatingGroup.kleinFour_card_of_card_eq_four hcard]
    rw [alternatingGroup.kleinFour_card_of_card_eq_four hcard]; simp
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI hcyc : IsCyclic (alternatingGroup (Fin 4) ⧸ alternatingGroup.kleinFour (Fin 4)) :=
    isCyclic_of_prime_card hcard3
  haveI hqSolv : IsSolvable (alternatingGroup (Fin 4) ⧸ alternatingGroup.kleinFour (Fin 4)) :=
    isSolvable_of_comm (fun a b => IsCyclic.commutative.comm a b)
  refine solvable_of_ker_le_range
    (alternatingGroup.kleinFour (Fin 4)).subtype
    (QuotientGroup.mk' (alternatingGroup.kleinFour (Fin 4))) ?_
  exact (QuotientGroup.ker_mk' _).le.trans (Subgroup.range_subtype _).ge

/--
**Solvability of `S₄`.**

`S₄` is solvable: the sign sequence `1 → A₄ → S₄ →^{sign} ℤˣ → 1` has solvable
kernel `A₄` (`alt_fin_four_solvable`) and abelian image `ℤˣ`, so
`solvable_of_ker_le_range` applies. This is the top of the solvable range: `S₄`
is the largest symmetric group solvable by radicals, which is why the general
quartic has a radical formula but the quintic does not.
-/
theorem perm_fin_four_solvable : IsSolvable (Equiv.Perm (Fin 4)) := by
  haveI : IsSolvable (alternatingGroup (Fin 4)) := alt_fin_four_solvable
  exact solvable_of_ker_le_range
    (alternatingGroup (Fin 4)).subtype
    (Equiv.Perm.sign (α := Fin 4))
    ((le_of_eq (alternatingGroup_eq_sign_ker (α := Fin 4)).symm).trans
      (Subgroup.range_subtype _).ge)

/--
**The symmetric threshold, both endpoints.**

`S₂` and `S₃` are solvable while `Sₙ` is not solvable for any `n ≥ 5`. This is the
group-theoretic skeleton of Abel–Ruffini: solvability of the symmetric group is
exactly what separates the radically-solvable low degrees from the
radically-unsolvable high degrees.
-/
theorem symmetric_threshold :
    IsSolvable (Equiv.Perm (Fin 2)) ∧ IsSolvable (Equiv.Perm (Fin 3)) ∧
    (∀ n : ℕ, 5 ≤ n → ¬ IsSolvable (Equiv.Perm (Fin n))) :=
  ⟨perm_fin_two_solvable, perm_fin_three_solvable,
    fun _ hn => symmetricGroup_not_solvable hn⟩

/--
**The full symmetric threshold `Sₙ` solvable ⟺ `n ≤ 4`, all cases discharged.**

The complete classification at the level of the concrete small groups: `S₂`,
`S₃`, and `S₄` are each solvable (the solvable side, now proved for *every*
`n ≤ 4` with `n ≥ 2` — the cases `n ≤ 1` are trivial), while `Sₙ` is not solvable
for any `n ≥ 5` (`symmetricGroup_not_solvable`). This is the sharp group-theoretic
dividing line behind Abel–Ruffini: degrees `≤ 4` have radical formulas (quadratic,
Cardano, Ferrari) exactly because `S₂, S₃, S₄` are solvable, and degree `≥ 5` does
not because `Sₙ` is not.
-/
theorem symmetric_threshold_full :
    IsSolvable (Equiv.Perm (Fin 2)) ∧
    IsSolvable (Equiv.Perm (Fin 3)) ∧
    IsSolvable (Equiv.Perm (Fin 4)) ∧
    (∀ n : ℕ, 5 ≤ n → ¬ IsSolvable (Equiv.Perm (Fin n))) :=
  ⟨perm_fin_two_solvable, perm_fin_three_solvable, perm_fin_four_solvable,
    fun _ hn => symmetricGroup_not_solvable hn⟩

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
