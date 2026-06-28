import Mathlib

/-
# The permutation-representation bridge: a 3-cycle on the roots ⟹ `3 ∣ |Gal(p)|`

The mod-7 Dedekind route toward the last axiom of `InverseGaloisA5.lean`

  `axiom three_dvd_gal_card : 3 ∣ Fintype.card q.Gal`

splits into two halves (see `InverseGaloisOQ06OQ02Cycle.lean`):

  (A) **Frobenius ↔ factorization** — the genuine number-theory gap (Dedekind's
      theorem), owned by the sibling track `inverse-galois-a5-oq-01`
      (`InverseGaloisA5Dedekind.exists_gal_order_three`).
  (B) **cycle type ⟹ order ⟹ divisibility** — pure group theory.

`InverseGaloisOQ06OQ02Cycle.lean` verified part (B) *abstractly*, for a subgroup
`H ⊆ Equiv.Perm α` literally containing a 3-cycle. But the axiom is phrased for
the **abstract Galois group** `q.Gal = q.SplittingField ≃ₐ[ℚ] q.SplittingField`,
which is an `AlgEquiv` type, **not** literally a subgroup of `Equiv.Perm`.

This file closes that interface gap with the standard *permutation representation*
`Polynomial.Gal.galActionHom : p.Gal →* Equiv.Perm (p.rootSet E)`, which is an
**injective** monoid homomorphism (faithful action on the roots). We prove, for the
real `p.Gal` type:

* `orderOf_galActionHom`        : the representation is order-preserving,
                                  `orderOf (galActionHom σ) = orderOf σ`.
* `three_dvd_card_gal_of_isThreeCycle`
                                : if **some** Galois element acts on the roots as a
                                  **3-cycle**, then `3 ∣ |Gal(p)|`.
* `three_dvd_card_gal_of_cycleType`
                                : same, stated with the cycle-type identity
                                  `(galActionHom σ).cycleType = {3}`.

## Why this is the faithful Dedekind interface

Dedekind's theorem does **not** hand back an abstract "element of order 3"; it
hands back a Frobenius element whose **action on the roots has cycle type equal to
the mod-`p` factorization degrees**. For `q mod 7 = (X-5)(X-6)·(cubic)` that cycle
type is `(1, 1, 3)`, i.e. a 3-cycle on the rootSet. These lemmas consume *exactly*
that output and deliver `3 ∣ |Gal|` for the genuine `q.Gal`, so the only residual
gap is part (A): producing the Frobenius permutation itself.

## Honest scope

This file is **0-axiom / 0-sorry** but does **NOT** discharge `three_dvd_gal_card`.
It is the deterministic group-theoretic eliminator phrased against the real
`Polynomial.Gal` type, making precise that the sole remaining input is the
number-theoretic Frobenius construction (A).

## Key Mathlib API

- `Polynomial.Gal.galActionHom : p.Gal →* Equiv.Perm (p.rootSet E)`
- `Polynomial.Gal.galActionHom_injective`  (needs `Fact (p.map (algebraMap F E)).Splits`)
- `orderOf_injective`, `orderOf_dvd_card`
- `Equiv.Perm.IsThreeCycle.orderOf`  (`IsThreeCycle σ := σ.cycleType = {3}`)
-/

set_option linter.unusedVariables false

open Polynomial Polynomial.Gal Equiv Equiv.Perm

open scoped Classical

namespace InverseGaloisOQ06OQ02GalAction

variable {F : Type*} [Field F] {p : F[X]} {E : Type*} [Field E] [Algebra F E]
  [Fact ((p.map (algebraMap F E)).Splits)]

/-- **The permutation representation is order-preserving.** Because
`Polynomial.Gal.galActionHom` is an *injective* monoid homomorphism, the order of a
Galois element equals the order of the permutation it induces on the roots of `p`
in `E`. This is what lets a *root-permutation* statement (Dedekind's natural
output) control the order of an *abstract* `AlgEquiv`. -/
theorem orderOf_galActionHom (σ : p.Gal) :
    orderOf (galActionHom p E σ) = orderOf σ :=
  orderOf_injective (galActionHom p E) (galActionHom_injective p E) σ

/-- **Faithful Dedekind bridge (3-cycle form).** If some element of `Gal(p)` acts
on the roots of `p` in `E` as a **three-cycle**, then `3 ∣ |Gal(p)|`.

This is the precise shape Dedekind's theorem delivers at an unramified prime whose
mod-`p` factorization has a single cubic (degree-3) irreducible factor and the rest
linear: the Frobenius acts as a 3-cycle on the corresponding roots. -/
theorem three_dvd_card_gal_of_isThreeCycle
    {σ : p.Gal} (hσ : (galActionHom p E σ).IsThreeCycle) :
    3 ∣ Fintype.card p.Gal := by
  have h3 : orderOf σ = 3 := by
    rw [← orderOf_galActionHom (E := E) σ, hσ.orderOf]
  rw [← h3]
  exact orderOf_dvd_card

/-- **Faithful Dedekind bridge (cycle-type form).** Identical to
`three_dvd_card_gal_of_isThreeCycle`, with the hypothesis written as the cycle-type
identity `(galActionHom σ).cycleType = {3}` — the literal `(1,1,3)` shape of
`q mod 7` (one 3-cycle, two fixed points). `IsThreeCycle` is *defined* as this
identity, so the two forms are interchangeable. -/
theorem three_dvd_card_gal_of_cycleType
    {σ : p.Gal} (hσ : (galActionHom p E σ).cycleType = {3}) :
    3 ∣ Fintype.card p.Gal :=
  three_dvd_card_gal_of_isThreeCycle hσ

/-- **Order-3 form (sanity bridge).** The classical reduction: an abstract
order-3 Galois element already forces `3 ∣ |Gal(p)|`. This recovers the sibling's
`three_dvd_gal_card_proved` shape and shows the 3-cycle bridge above is strictly an
*interface refinement* of it (3-cycle on roots ⟹ order 3 ⟹ divisibility). -/
theorem three_dvd_card_gal_of_orderOf_three
    {σ : p.Gal} (hσ : orderOf σ = 3) :
    3 ∣ Fintype.card p.Gal := by
  rw [← hσ]; exact orderOf_dvd_card

end InverseGaloisOQ06OQ02GalAction
