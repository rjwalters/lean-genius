import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.Rat
import Mathlib.Data.Nat.Totient
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum

/-!
# Hilbert's Ninth Problem: Cyclotomic Reciprocity — the Abelian Case over ℚ

## What This Proves

Hilbert's 9th problem asked for *the most general reciprocity law* in algebraic number
fields. Its complete answer is **Artin reciprocity** (1927), the central theorem of class
field theory: for an abelian extension `L/K` of number fields, the Artin map induces an
isomorphism between a ray class group and `Gal(L/K)`.

The parent gallery entry states Artin reciprocity axiomatically (its full proof needs the
whole machinery of class field theory). This file instead formalizes, with **no axioms and
no `sorry`**, the single most important *concrete* instance of Artin reciprocity: the
reciprocity law for **cyclotomic extensions of ℚ**. This is exactly the abelian case that
Hilbert himself first proved (1897) and that Kronecker–Weber shows is *all* of the abelian
extensions of ℚ.

The reciprocity isomorphism is
$$\mathrm{Gal}\big(\mathbb{Q}(\zeta_n)/\mathbb{Q}\big) \;\cong\; (\mathbb{Z}/n\mathbb{Z})^\times,$$
under which an automorphism `σ` corresponds to the unique unit `t ∈ (ℤ/n)ˣ` with
`σ(ζ) = ζ^t`. On the arithmetic side, the Artin symbol (Frobenius) of an unramified prime
`p ∤ n` is sent to the residue class `p mod n`; this is the reciprocity content — the action
of Galois on roots of unity is governed entirely by residues modulo `n`.

## Results

* `galEquivUnits` : the reciprocity isomorphism `Gal(ℚ(ζ_n)/ℚ) ≃* (ℤ/n)ˣ`.
* `galEquivUnits_apply_spec` : the explicit action `σ(ζ) = ζ^(galEquivUnits σ).val`.
* `card_gal_eq_totient` : `|Gal(ℚ(ζ_n)/ℚ)| = φ(n)`.
* `gal_mul_comm` : the Galois group is abelian — the defining hypothesis of Artin reciprocity.
* Concrete cardinalities for `n = 5, 7, 8` (`φ(5)=4`, `φ(7)=6`, `φ(8)=4`).

## Mathlib Dependencies

* `IsCyclotomicExtension.autEquivPow` : `Gal(L/K) ≃* (ZMod n)ˣ` when `cyclotomic n K` is irreducible.
* `Polynomial.cyclotomic.irreducible_rat` : the `n`-th cyclotomic polynomial is irreducible over ℚ.
* `IsPrimitiveRoot.autToPow_spec` : `μ ^ (autToPow f).val = f μ`.
* `ZMod.card_units_eq_totient` : `|(ℤ/n)ˣ| = φ(n)`.

## References

* Artin, E. "Beweis des allgemeinen Reziprozitätsgesetzes" (1927).
* Neukirch, J. "Algebraic Number Theory", Chapter VII (class field theory).
* K. Conrad, "The Galois group of a cyclotomic field",
  https://kconrad.math.uconn.edu/blurbs/galoistheory/cyclotomic.pdf

## Hilbert's 23 Problems: Problem 9
-/

namespace Hilbert9CyclotomicReciprocity

open Polynomial IsCyclotomicExtension

variable (n : ℕ) [NeZero n]

/-- The `n`-th cyclotomic polynomial is irreducible over `ℚ` — the hypothesis that turns the
injection `Gal(ℚ(ζ_n)/ℚ) ↪ (ℤ/n)ˣ` into an isomorphism. -/
theorem cyclotomic_irreducible_rat : Irreducible (cyclotomic n ℚ) :=
  cyclotomic.irreducible_rat (NeZero.pos n)

/-- **Cyclotomic reciprocity (abelian Artin reciprocity over ℚ).**

The Galois group of the `n`-th cyclotomic field `ℚ(ζ_n)` over `ℚ` is isomorphic to the unit
group `(ℤ/n)ˣ`. This is the concrete, fully verified instance of Artin's reciprocity law:
Galois acts on the roots of unity through residues modulo `n`. -/
noncomputable def galEquivUnits :
    (CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ) ≃* (ZMod n)ˣ :=
  autEquivPow (CyclotomicField n ℚ) (cyclotomic_irreducible_rat n)

/-- **Explicit reciprocity action.** Every automorphism `σ` of `ℚ(ζ_n)` raises the canonical
primitive root `ζ` to the power `t = galEquivUnits σ ∈ (ℤ/n)ˣ`: `σ(ζ) = ζ^t`. This is the
statement that Galois acts on roots of unity by a residue modulo `n`. -/
theorem galEquivUnits_apply_spec
    (σ : CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ) :
    (zeta n ℚ (CyclotomicField n ℚ)) ^ ((galEquivUnits n σ : ZMod n).val)
      = σ (zeta n ℚ (CyclotomicField n ℚ)) := by
  have hζ := zeta_spec n ℚ (CyclotomicField n ℚ)
  simpa [galEquivUnits, autEquivPow_apply] using hζ.autToPow_spec ℚ σ

/-- The identity automorphism corresponds to the unit `1` under the reciprocity map. -/
theorem galEquivUnits_one : galEquivUnits n 1 = 1 :=
  map_one (galEquivUnits n)

/-- The reciprocity map is multiplicative: composition of automorphisms corresponds to
multiplication of residues. -/
theorem galEquivUnits_mul
    (σ τ : CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ) :
    galEquivUnits n (σ * τ) = galEquivUnits n σ * galEquivUnits n τ :=
  map_mul (galEquivUnits n) σ τ

/-- **The cyclotomic Galois group is abelian.** Commutativity is the defining hypothesis of
Artin reciprocity (it applies precisely to abelian extensions); here it is a theorem, inherited
from the commutativity of `(ℤ/n)ˣ` through the reciprocity isomorphism. -/
theorem gal_mul_comm
    (σ τ : CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ) :
    σ * τ = τ * σ := by
  apply (galEquivUnits n).injective
  rw [map_mul, map_mul, mul_comm]

/-- **Degree of the cyclotomic extension.** `[ℚ(ζ_n) : ℚ] = φ(n)`, expressed as the order of
the Galois group. This recovers the classical count of automorphisms of `ℚ(ζ_n)`. -/
theorem card_gal_eq_totient :
    Nat.card (CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ) = n.totient := by
  rw [Nat.card_congr (galEquivUnits n).toEquiv, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient]

/-! ## Concrete instances

For a prime `p`, `(ℤ/p)ˣ` is cyclic of order `p - 1`, so `Gal(ℚ(ζ_p)/ℚ) ≅ ℤ/(p-1)`.
For `n = 8` the group `(ℤ/8)ˣ ≅ ℤ/2 × ℤ/2` is the first non-cyclic example — the reciprocity
isomorphism still holds, with order `φ(8) = 4`. -/

/-- `|Gal(ℚ(ζ₅)/ℚ)| = φ(5) = 4`. -/
theorem card_gal_five :
    Nat.card (CyclotomicField 5 ℚ ≃ₐ[ℚ] CyclotomicField 5 ℚ) = 4 := by
  haveI : NeZero (5 : ℕ) := ⟨by norm_num⟩
  rw [card_gal_eq_totient 5]
  decide

/-- `|Gal(ℚ(ζ₇)/ℚ)| = φ(7) = 6`. -/
theorem card_gal_seven :
    Nat.card (CyclotomicField 7 ℚ ≃ₐ[ℚ] CyclotomicField 7 ℚ) = 6 := by
  haveI : NeZero (7 : ℕ) := ⟨by norm_num⟩
  rw [card_gal_eq_totient 7]
  decide

/-- `|Gal(ℚ(ζ₈)/ℚ)| = φ(8) = 4` — the first non-cyclic cyclotomic Galois group over ℚ. -/
theorem card_gal_eight :
    Nat.card (CyclotomicField 8 ℚ ≃ₐ[ℚ] CyclotomicField 8 ℚ) = 4 := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  rw [card_gal_eq_totient 8]
  decide

#check @galEquivUnits
#check @galEquivUnits_apply_spec
#check @card_gal_eq_totient
#check @gal_mul_comm

end Hilbert9CyclotomicReciprocity
