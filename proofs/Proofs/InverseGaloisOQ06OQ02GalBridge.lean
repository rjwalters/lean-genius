import Mathlib
import Proofs.InverseGaloisA5

/-
# Concrete deterministic-half bridge for `q.Gal` (OQ-06 → OQ-02, Gal instantiation)

The sibling file `InverseGaloisOQ06OQ02Cycle.lean` isolates the *abstract*
deterministic half of the mod-7 Dedekind route — "a permutation of cycle type
`(1,1,3)` in a subgroup of `Sₙ` forces `3 ∣ |subgroup|`" — over an arbitrary
permutation group. That statement is correct but stated for `{Gal : Subgroup
(Perm α)}`, not for the *actual* Galois group of the A₅ quintic
`q = X⁵ - 5X⁴ + 10X³ - 10X² + 25X - 5` whose last axiom we are chasing:

```
axiom three_dvd_gal_card : 3 ∣ Fintype.card q.Gal     -- InverseGaloisA5.lean:309
```

This file closes that gap of abstraction. Using the genuine Galois action on the
five roots,

  `Polynomial.Gal.galActionHom q q.SplittingField : q.Gal →* Perm (q.rootSet q.SplittingField)`

which `InverseGaloisA5` already knows to be **injective**, we prove fully (0 axioms,
0 sorries) the deterministic half **for `q.Gal` itself**:

  *If some Galois automorphism `σ ∈ q.Gal` acts on the five roots as a 3-cycle
   (cycle type `{3}`, i.e. the `(1,1,3)` shape of `q mod 7`), then
   `3 ∣ Fintype.card q.Gal`.*

This makes the residual Mathlib gap maximally precise. After this file, the only
thing standing between the **verified** algebraic input
(`InverseGaloisOQ06OQ02.q_mod7_factor_type`: `q mod 7` is a product of distinct
irreducibles of degrees `(1,1,3)`) and the axiom `three_dvd_gal_card` is the
single existential

  `∃ σ : q.Gal, (galActionHom q q.SplittingField σ).IsThreeCycle`

— the Frobenius ↔ factorization correspondence (Dedekind's theorem), owned by the
sibling track `inverse-galois-a5-oq-01`. Note this is phrased directly in terms of
the **permutation cycle type** that Dedekind produces, rather than the abstract
`orderOf σ = 3` of `InverseGaloisA5Dedekind.exists_gal_order_three`: it is one step
closer to the factorization data, and the injectivity step that converts cycle
type to order is discharged here.

This file does **not** eliminate `three_dvd_gal_card`; it verifies the
deterministic half against the real `q.Gal`, leaving exactly the Frobenius
construction as the open input.
-/

open Polynomial InverseGaloisA5

open scoped Classical

namespace InverseGaloisOQ06OQ02GalBridge

/-- The Galois action on the five roots is order-preserving on `q.Gal`: an
automorphism and its induced root permutation have the same order. This is the
injectivity of `galActionHom` (proved in `InverseGaloisA5`) fed through
`orderOf_injective`. -/
theorem orderOf_galActionHom (σ : q.Gal) :
    orderOf (Polynomial.Gal.galActionHom q q.SplittingField σ) = orderOf σ :=
  orderOf_injective _ (Polynomial.Gal.galActionHom_injective q q.SplittingField) σ

/-- **Concrete deterministic half of Dedekind for `q.Gal`.** If a Galois
automorphism acts on the five roots as a three-cycle — the `(1,1,3)` cycle type
of `q mod 7` realised as a genuine element of `q.Gal` — then `3 ∣ |q.Gal|`.

The verified algebraic input `InverseGaloisOQ06OQ02.q_mod7_factor_type` supplies
the factorization side; what remains open is producing the Galois element `σ`
whose root permutation has this cycle type (the Frobenius element). -/
theorem three_dvd_gal_card_of_galAction_isThreeCycle {σ : q.Gal}
    (hσ : (Polynomial.Gal.galActionHom q q.SplittingField σ).IsThreeCycle) :
    3 ∣ Fintype.card q.Gal := by
  have horder : orderOf σ = 3 := by
    rw [← orderOf_galActionHom σ]; exact hσ.orderOf
  rw [← horder]
  exact orderOf_dvd_card

/-- Cycle-type phrasing of the same bridge: `IsThreeCycle` unfolds definitionally
to `cycleType = {3}`, the exact `(1,1,3)` datum of the mod-7 factorization. -/
theorem three_dvd_gal_card_of_galAction_cycleType {σ : q.Gal}
    (hσ : (Polynomial.Gal.galActionHom q q.SplittingField σ).cycleType = {3}) :
    3 ∣ Fintype.card q.Gal :=
  three_dvd_gal_card_of_galAction_isThreeCycle hσ

/-- **The residual gap, made precise.** `three_dvd_gal_card` follows from the
single existential hypothesis that the Galois group contains an automorphism
acting on the five roots as a 3-cycle. This is exactly the conclusion of
Dedekind's theorem applied to the verified mod-7 `(1,1,3)` factorization, and is
the sole remaining open input on the mod-7 route. -/
theorem three_dvd_gal_card_of_exists_galAction_threeCycle
    (h : ∃ σ : q.Gal, (Polynomial.Gal.galActionHom q q.SplittingField σ).IsThreeCycle) :
    3 ∣ Fintype.card q.Gal := by
  obtain ⟨σ, hσ⟩ := h
  exact three_dvd_gal_card_of_galAction_isThreeCycle hσ

/-- Equivalent reduction phrased via `exists_gal_order_three` (the sibling's
sorry shape): an order-3 Galois element gives `3 ∣ |q.Gal|`. Kept here so the two
formulations of the residual gap — "a root-3-cycle exists" (this file) and "an
order-3 element exists" (`InverseGaloisA5Dedekind`) — sit side by side; the former
implies the latter through `orderOf_galActionHom`. -/
theorem three_dvd_gal_card_of_exists_order_three
    (h : ∃ σ : q.Gal, orderOf σ = 3) : 3 ∣ Fintype.card q.Gal := by
  obtain ⟨σ, hσ⟩ := h
  rw [← hσ]; exact orderOf_dvd_card

/-- The root-3-cycle hypothesis implies the order-3 hypothesis: a Galois element
acting as a 3-cycle on the roots has order 3 in `q.Gal`. This shows the precise
form of the gap supplied here is at least as strong as the sibling's. -/
theorem exists_order_three_of_exists_galAction_threeCycle
    (h : ∃ σ : q.Gal, (Polynomial.Gal.galActionHom q q.SplittingField σ).IsThreeCycle) :
    ∃ σ : q.Gal, orderOf σ = 3 := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ, by rw [← orderOf_galActionHom σ]; exact hσ.orderOf⟩

end InverseGaloisOQ06OQ02GalBridge
