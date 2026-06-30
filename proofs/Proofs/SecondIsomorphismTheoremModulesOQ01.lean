import Mathlib.Tactic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-
# Second (Diamond) Isomorphism Theorem for modules — OQ01

## Question

The three classical isomorphism theorems are foundational structure theorems for modules.
Mathlib packages the **second (diamond) isomorphism theorem** as the linear equivalence
`Submodule.quotientInfEquivSupQuotient`: for submodules `p p'` of an `R`-module `M`,

  `p ⧸ (p ⊓ p')  ≃ₗ[R]  (p ⊔ p') ⧸ p'`

(read inside the relevant ambient submodules, so the literal types are
`↥p ⧸ comap p.subtype (p ⊓ p')` and `↥(p ⊔ p') ⧸ comap (p ⊔ p').subtype p'`).

This entry is **not** a re-export of that equivalence. The question is whether the equivalence
has genuine *computational* force: does it, on its own, recover the **modular dimension law**

  `finrank (p ⊔ p') + finrank (p ⊓ p') = finrank p + finrank p'`

for finite-dimensional vector spaces — without appealing to Mathlib's independent proof
`Submodule.finrank_sup_add_finrank_inf_eq`?

## Answer

**Yes.** We derive the modular dimension law *purely from the second isomorphism theorem*
(`secondIso`), the rank–nullity identity for quotients
(`Submodule.finrank_quotient_add_finrank`), and the fact that the comap of a submodule
under an inclusion has the same dimension as that submodule
(`Submodule.comap_subtype_equiv_of_le`). The equivalence forces the two quotients to share a
dimension; rank–nullity turns each quotient dimension into a difference of finranks; the two
differences being equal *is* the modular law. We then read off the direct-sum corollary
(`p ⊓ p' = ⊥ ⟹ finrank (p ⊔ p') = finrank p + finrank p'`).

## What this establishes

* `secondIso` — the second isomorphism theorem as a named `LinearEquiv` (any ring/module).
* `secondIso_bijective` — its underlying map is a genuine bijection (the equivalence is
  *constructed*, via `LinearEquiv.ofBijective` upstream, not postulated).
* `finrank_modular_law` — the modular dimension law, derived from `secondIso`.
* `finrank_sup_of_inf_bot` — the direct-sum dimension corollary.
* `finrank_inf_of_sup_top` — the dual co-dimension corollary.

Mathlib's `Submodule.finrank_sup_add_finrank_inf_eq` is an *independent* proof of the same
law; the value here is exhibiting it as a corollary of the isomorphism theorem.
-/

open Submodule FiniteDimensional Module

namespace SecondIsomorphismTheoremModulesOQ01

section AnyRing

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

/-- **Second (diamond) isomorphism theorem** as a named linear equivalence:
`p ⧸ (p ⊓ p') ≃ₗ (p ⊔ p') ⧸ p'`, read inside the appropriate ambient submodules. -/
noncomputable def secondIso (p p' : Submodule R M) :
    (↥p ⧸ Submodule.comap p.subtype (p ⊓ p')) ≃ₗ[R]
      (↥(p ⊔ p') ⧸ Submodule.comap (p ⊔ p').subtype p') :=
  LinearMap.quotientInfEquivSupQuotient p p'

/-- The underlying linear map of the second isomorphism is a genuine bijection. -/
theorem secondIso_bijective (p p' : Submodule R M) :
    Function.Bijective (secondIso p p') :=
  (secondIso p p').bijective

end AnyRing

section FiniteDimensional

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] (p p' : Submodule K V)

omit [FiniteDimensional K V] in
/-- The comap of `p ⊓ p'` into `p` has the same dimension as `p ⊓ p'`. -/
private theorem finrank_comap_inf :
    Module.finrank K (Submodule.comap p.subtype (p ⊓ p')) = Module.finrank K ↥(p ⊓ p') :=
  (Submodule.comapSubtypeEquivOfLe (inf_le_left)).finrank_eq

omit [FiniteDimensional K V] in
/-- The comap of `p'` into `p ⊔ p'` has the same dimension as `p'`. -/
private theorem finrank_comap_sup :
    Module.finrank K (Submodule.comap (p ⊔ p').subtype p') = Module.finrank K ↥p' :=
  (Submodule.comapSubtypeEquivOfLe (le_sup_right)).finrank_eq

/-- **Modular dimension law**, derived *from the second isomorphism theorem*:
`finrank (p ⊔ p') + finrank (p ⊓ p') = finrank p + finrank p'`. -/
theorem finrank_modular_law :
    Module.finrank K ↥(p ⊔ p') + Module.finrank K ↥(p ⊓ p')
      = Module.finrank K ↥p + Module.finrank K ↥p' := by
  -- The two quotients have equal dimension because `secondIso` is an equivalence.
  have hiso :
      Module.finrank K (↥p ⧸ Submodule.comap p.subtype (p ⊓ p'))
        = Module.finrank K (↥(p ⊔ p') ⧸ Submodule.comap (p ⊔ p').subtype p') :=
    (secondIso p p').finrank_eq
  -- Rank–nullity on the left quotient (ambient `↥p`).
  have hL :
      Module.finrank K (↥p ⧸ Submodule.comap p.subtype (p ⊓ p'))
        + Module.finrank K ↥(p ⊓ p') = Module.finrank K ↥p := by
    have := Submodule.finrank_quotient_add_finrank (Submodule.comap p.subtype (p ⊓ p'))
    rwa [finrank_comap_inf] at this
  -- Rank–nullity on the right quotient (ambient `↥(p ⊔ p')`).
  have hR :
      Module.finrank K (↥(p ⊔ p') ⧸ Submodule.comap (p ⊔ p').subtype p')
        + Module.finrank K ↥p' = Module.finrank K ↥(p ⊔ p') := by
    have := Submodule.finrank_quotient_add_finrank (Submodule.comap (p ⊔ p').subtype p')
    rwa [finrank_comap_sup] at this
  omega

/-- **Direct-sum dimension corollary**: independent submodules add dimensions. -/
theorem finrank_sup_of_inf_bot (h : p ⊓ p' = ⊥) :
    Module.finrank K ↥(p ⊔ p') = Module.finrank K ↥p + Module.finrank K ↥p' := by
  have hmod := finrank_modular_law p p'
  rw [h, finrank_bot] at hmod
  omega

/-- **Co-dimension corollary**: spanning submodules' intersection carries the excess dimension. -/
theorem finrank_inf_of_sup_top (h : p ⊔ p' = ⊤) :
    Module.finrank K ↥(p ⊓ p') + Module.finrank K V
      = Module.finrank K ↥p + Module.finrank K ↥p' := by
  have hmod := finrank_modular_law p p'
  rw [h, finrank_top] at hmod
  omega

end FiniteDimensional

end SecondIsomorphismTheoremModulesOQ01
