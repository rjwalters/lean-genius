import Mathlib
import Proofs.FundamentalTheoremAlgebraOQ04OQ03OQ01

/-
# Identifying the explicit `Gal(ℂ/ℝ) ≃* Multiplicative (ZMod 2)` with Mathlib's generic iso

## What This Proves

This is the leaf `oq-04-oq-03-oq-01-oq-02` of `fundamental-theorem-algebra-oq-04`.
The parent leaf `FundamentalTheoremAlgebraOQ04OQ03OQ01` built, *by hand and with
the generator named*, the isomorphism

  `galoisGroupEquivZMod2 : (ℂ ≃ₐ[ℝ] ℂ) ≃* Multiplicative (ZMod 2)`,

sending complex conjugation `Complex.conjAe` to the nontrivial element `ofAdd 1`.
Mathlib also offers a *generic* construction `zmodCyclicMulEquiv`, which for any
cyclic group `G` produces `Multiplicative (ZMod (Nat.card G)) ≃* G` — but only by
`Classical.choice`-ing some generator, so a priori it is opaque about *which*
automorphism the nontrivial element lands on.

The parent's open question OQ[2] asks to **identify the two**: to show the generic
Mathlib iso, once specialised to `Gal(ℂ/ℝ)` (where `Nat.card = 2`), coincides with
the explicit one, and that its canonical generator can be taken to be complex
conjugation.

The mathematical content is a **rigidity / uniqueness** statement:

* `any_equiv_ofAdd_one` : *every* group isomorphism
  `e : Multiplicative (ZMod 2) ≃* (ℂ ≃ₐ[ℝ] ℂ)` sends the generator `ofAdd 1` to
  `Complex.conjAe`. (A group of order two has a unique non-identity element, and a
  group iso must carry the unique non-identity element `ofAdd 1` to it.)
* `eq_galoisGroupEquivZMod2_symm` : *every* such `e` is **equal** to
  `galoisGroupEquivZMod2.symm`. There is therefore only one isomorphism
  `Multiplicative (ZMod 2) ≃* Gal(ℂ/ℝ)` at all — the explicit one — and any choice
  of generator made elsewhere is forced to agree with it.

Specialising this rigidity to Mathlib's `zmodCyclicMulEquiv` (transported along
`|Gal(ℂ/ℝ)| = 2`) yields the requested identification:

* `mathlibGaloisIso_eq` : `zmodCyclicMulEquiv` (so transported) **equals**
  `galoisGroupEquivZMod2.symm`;
* `mathlibGaloisIso_ofAdd_one` : its generator `ofAdd 1` maps to `Complex.conjAe`.

Note the rigidity theorems treat the Mathlib iso as an *arbitrary* `e`, so no
`Classical.choice`-built data has to be unfolded — the cast transporting the type
along `Nat.card = 2` never needs to reduce.

*Reference:* `Mathlib.GroupTheory.SpecificGroups.Cyclic` (`zmodCyclicMulEquiv`,
`isCyclic_of_prime_card`); parent leaf `FundamentalTheoremAlgebraOQ04OQ03OQ01`.
-/

open Complex
open scoped Classical

namespace FTAGaloisIso

/-! ## `Gal(ℂ/ℝ)` is cyclic -/

/-- **`Gal(ℂ/ℝ)` is cyclic**, being a group of prime order `2`. This is the
    hypothesis Mathlib's `zmodCyclicMulEquiv` consumes. -/
instance galoisGroup_isCyclic : IsCyclic (ℂ ≃ₐ[ℝ] ℂ) :=
  isCyclic_of_prime_card card_galoisGroup_eq_two

/-! ## Rigidity of order-two isomorphisms -/

/-- **Every** isomorphism `Multiplicative (ZMod 2) ≃* Gal(ℂ/ℝ)` sends the generator
    `ofAdd 1` to complex conjugation. The non-identity element `ofAdd 1` must map to a
    non-identity automorphism, and `Complex.conjAe` is the only one. -/
theorem any_equiv_ofAdd_one (e : Multiplicative (ZMod 2) ≃* (ℂ ≃ₐ[ℝ] ℂ)) :
    e (Multiplicative.ofAdd 1) = Complex.conjAe := by
  rcases eq_one_or_conjAe (e (Multiplicative.ofAdd 1)) with h | h
  · -- `e (ofAdd 1) = 1` would force `ofAdd 1 = 1` by injectivity, impossible.
    exfalso
    have hbad : Multiplicative.ofAdd (1 : ZMod 2) = 1 :=
      e.injective (h.trans (map_one e).symm)
    exact ofAdd_one_ne_one hbad
  · exact h

/-- **Uniqueness of the order-two iso.** Any isomorphism
    `Multiplicative (ZMod 2) ≃* Gal(ℂ/ℝ)` equals the explicit `galoisGroupEquivZMod2.symm`.
    Both agree on the two elements `1` and `ofAdd 1`. -/
theorem eq_galoisGroupEquivZMod2_symm (e : Multiplicative (ZMod 2) ≃* (ℂ ≃ₐ[ℝ] ℂ)) :
    e = galoisGroupEquivZMod2.symm := by
  ext x
  rcases zmod2_eq_one_or x with h | h
  · subst h; simp
  · subst h
    rw [any_equiv_ofAdd_one e, galoisGroupEquivZMod2_symm_ofAdd_one]

/-! ## Specialisation to Mathlib's generic `zmodCyclicMulEquiv` -/

/-- **Mathlib's generic cyclic iso, specialised to `Gal(ℂ/ℝ)`.** Transporting
    `zmodCyclicMulEquiv` along `Nat.card (ℂ ≃ₐ[ℝ] ℂ) = 2` gives an isomorphism
    `Multiplicative (ZMod 2) ≃* Gal(ℂ/ℝ)`. -/
noncomputable def mathlibGaloisIso : Multiplicative (ZMod 2) ≃* (ℂ ≃ₐ[ℝ] ℂ) :=
  card_galoisGroup_eq_two ▸ zmodCyclicMulEquiv galoisGroup_isCyclic

/-- **Identification.** Mathlib's generic iso (transported along `|Gal(ℂ/ℝ)| = 2`)
    is *exactly* the explicit hand-built isomorphism `galoisGroupEquivZMod2.symm`. The
    `Classical.choice` of a generator hidden inside `zmodCyclicMulEquiv` is therefore
    forced to be the canonical one. -/
theorem mathlibGaloisIso_eq : mathlibGaloisIso = galoisGroupEquivZMod2.symm :=
  eq_galoisGroupEquivZMod2_symm mathlibGaloisIso

/-- **The canonical generator is complex conjugation.** Under Mathlib's generic iso,
    the generator `ofAdd 1` of `Multiplicative (ZMod 2)` maps to `Complex.conjAe`. -/
theorem mathlibGaloisIso_ofAdd_one :
    mathlibGaloisIso (Multiplicative.ofAdd 1) = Complex.conjAe :=
  any_equiv_ofAdd_one mathlibGaloisIso

end FTAGaloisIso
