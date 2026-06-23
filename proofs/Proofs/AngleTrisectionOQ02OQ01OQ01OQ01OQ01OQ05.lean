/-
# The Automorphism Bound: |Aut_F(K)| ≤ [K : F]_s

This file answers the fifth open question raised by
`angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01` (the purely-inseparable boundary
case of the Galois-group cardinality story for the trisection tower):

> Does Mathlib formalise the separable-degree bound `|Aut_F(K)| ≤ [K : F]_s` in the
> form `Nat.card (K ≃ₐ[F] K) ≤ Module.finSepDegree F K`?  If so,
> `gal_card_one_of_purelyInseparable_splitting` becomes a one-liner.

**Status of the question in Mathlib.**  Mathlib v4.26 does *not* package this
inequality as a named lemma, and the spelling `Module.finSepDegree` does not exist
in this toolchain — the separable degree lives in the `Field` namespace as
`Field.finSepDegree F K := Nat.card (Field.Emb F K)`, with
`Field.Emb F K := K →ₐ[F] AlgebraicClosure K`.  So the right reading of the open
question is the second branch: supply the clean lemma.

**The proof.**  The whole content is one injection.  An `F`-algebra automorphism
`e : K ≃ₐ[F] K` becomes an element of `Field.Emb F K` by post-composing with the
structure map `K → AlgebraicClosure K`:

  `e  ↦  (IsScalarTower.toAlgHom F K (AlgebraicClosure K)).comp e.toAlgHom`.

This map is injective because the structure map `algebraMap K (AlgebraicClosure K)`
is injective (any ring map out of a field into a nonzero ring is).  Counting with
`Nat.card_le_card_of_injective` — the codomain `Field.Emb F K` is finite for a
finite extension (`minpoly.AlgHom.fintype`) — gives the bound, and
`Field.finSepDegree` is *definitionally* `Nat.card (Field.Emb F K)`.

**Consequences.**  Combined with the existing Mathlib API this immediately yields
the `finrank` bound `|Aut_F(K)| ≤ [K : F]` and the boundary case the parent entry
cares about: a purely inseparable finite extension has a trivial automorphism
group (`Subsingleton (K ≃ₐ[F] K)`), the abstract reason
`gal_card_one_of_purelyInseparable_splitting` holds.

No axioms, no `sorry`, no `native_decide`.
-/
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.FieldTheory.PurelyInseparable.Basic

open Field

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

namespace AngleTrisectionAutBound

/-- The post-composition map sending an `F`-algebra automorphism of `K` to the
`F`-embedding of `K` into its algebraic closure obtained by following it with the
structure map `K → AlgebraicClosure K`. -/
noncomputable def toEmb (e : K ≃ₐ[F] K) : Field.Emb F K :=
  (IsScalarTower.toAlgHom F K (AlgebraicClosure K)).comp e.toAlgHom

@[simp]
theorem toEmb_apply (e : K ≃ₐ[F] K) (x : K) :
    toEmb F K e x = algebraMap K (AlgebraicClosure K) (e x) := rfl

/-- Post-composing with the (injective) structure map `K → AlgebraicClosure K` is
injective: distinct automorphisms give distinct embeddings. -/
theorem toEmb_injective : Function.Injective (toEmb F K) := by
  intro e₁ e₂ h
  ext x
  have hx : algebraMap K (AlgebraicClosure K) (e₁ x)
      = algebraMap K (AlgebraicClosure K) (e₂ x) := by
    simpa using congrFun (congrArg (DFunLike.coe) h) x
  exact (algebraMap K (AlgebraicClosure K)).injective hx

/-- **The automorphism bound.**  For a finite extension `K / F`, the number of
`F`-algebra automorphisms of `K` is at most the separable degree `[K : F]_s`.
This is `|Aut_F(K)| ≤ [K : F]_s` in the form requested by the open question
(with the actual Mathlib name `Field.finSepDegree`). -/
theorem card_algEquiv_le_finSepDegree [FiniteDimensional F K] :
    Nat.card (K ≃ₐ[F] K) ≤ Field.finSepDegree F K :=
  Nat.card_le_card_of_injective (toEmb F K) (toEmb_injective F K)

/-- **Corollary (finrank bound).**  The number of `F`-algebra automorphisms of a
finite extension `K / F` is at most the degree `[K : F]`.  This composes the
separable-degree bound with `Field.finSepDegree_le_finrank`. -/
theorem card_algEquiv_le_finrank [FiniteDimensional F K] :
    Nat.card (K ≃ₐ[F] K) ≤ Module.finrank F K :=
  (card_algEquiv_le_finSepDegree F K).trans (Field.finSepDegree_le_finrank F K)

/-- **Corollary (purely inseparable boundary case).**  A finite purely inseparable
extension has at most one `F`-algebra automorphism: its automorphism group is a
subsingleton.  This is the abstract content of
`gal_card_one_of_purelyInseparable_splitting` — purely inseparable forces
`finSepDegree = 1`, and the bound then pins `Nat.card (K ≃ₐ[F] K) ≤ 1`. -/
theorem subsingleton_algEquiv_of_isPurelyInseparable
    [FiniteDimensional F K] [IsPurelyInseparable F K] :
    Subsingleton (K ≃ₐ[F] K) := by
  haveI : Finite (K ≃ₐ[F] K) := Finite.of_injective (toEmb F K) (toEmb_injective F K)
  rw [← Finite.card_le_one_iff_subsingleton]
  calc Nat.card (K ≃ₐ[F] K)
      ≤ Field.finSepDegree F K := card_algEquiv_le_finSepDegree F K
    _ = 1 := IsPurelyInseparable.finSepDegree_eq_one F K

/-- The boundary case stated as an equality: a finite purely inseparable extension
has exactly one `F`-algebra automorphism (the identity). -/
theorem card_algEquiv_eq_one_of_isPurelyInseparable
    [FiniteDimensional F K] [IsPurelyInseparable F K] :
    Nat.card (K ≃ₐ[F] K) = 1 := by
  have : Subsingleton (K ≃ₐ[F] K) := subsingleton_algEquiv_of_isPurelyInseparable F K
  exact Nat.card_eq_one_iff_unique.mpr ⟨this, ⟨1⟩⟩

end AngleTrisectionAutBound
