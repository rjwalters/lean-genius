/-
# The Automorphism Equality for Normal Extensions: |Aut_F(K)| = [K : F]_s

This file answers the two open questions raised by
`angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01-oq-05`
("The Automorphism Bound: |Aut_F(K)| ≤ [K : F]_s"), which proved the *inequality*
`Nat.card (K ≃ₐ[F] K) ≤ Field.finSepDegree F K` via a single injection

  `toEmb : (K ≃ₐ[F] K) → Field.Emb F K`,
  `toEmb e = (IsScalarTower.toAlgHom F K (AlgebraicClosure K)).comp e.toAlgHom`,

and asked:

> 1. Can the bound be sharpened to an equality criterion —
>    `Nat.card (K ≃ₐ[F] K) = Field.finSepDegree F K` when `K / F` is normal —
>    recovering the Galois characterisation `|Gal| = [K : F]` for normal separable
>    extensions?
> 2. Does the injection `toEmb` extend to a *bijection* onto the embeddings, giving
>    `|Aut_F(K)|` equal to the number of `F`-embeddings of `K` for normal `K / F`?

**The key observation.**  Mathlib packages `Normal.algHomEquivAut`, the equivalence

  `(E →ₐ[F] K₁) ≃ (E ≃ₐ[F] E)`   for `[Normal F E]`,

whose *inverse* sends `σ ↦ (IsScalarTower.toAlgHom F E K₁).comp σ.toAlgHom`.
Taking `E = K` and `K₁ = AlgebraicClosure K`, this inverse is *definitionally* the
parent's `toEmb`.  So for a normal extension the parent's injection is exactly one
half of a Mathlib equivalence: it is automatically **bijective**, and counting both
sides gives the equality `[K : F]_s = |Aut_F(K)|`.  This is the second branch of
the open question answered head-on, and the equality of the first.

**Why this is more than the Galois fact.**  Mathlib already has
`IsGalois.card_aut_eq_finrank` (`|Aut| = [K : F]` for *Galois* = normal *and*
separable extensions).  The equality proved here drops separability: for an
arbitrary **normal** extension the automorphism count equals the *separable*
degree `[K : F]_s`, which is `[K : F]` only when the extension is also separable.
Indeed, among finite normal extensions, `|Aut_F(K)| = [K : F]` holds **iff** `K / F`
is separable (`card_algEquiv_eq_finrank_iff_isSeparable` below); for a normal
*purely inseparable* extension both `[K : F]_s` and `|Aut_F(K)|` collapse to `1`
while `[K : F]` can be arbitrarily large.  So the automorphism group sees only the
separable part of the degree — the equality isolates exactly that phenomenon.

No axioms, no `sorry`, no `native_decide`.
-/
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.FieldTheory.Normal.Defs

open Field

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

namespace NormalAutEquality

/-- The post-composition map from the parent entry: an `F`-algebra automorphism of
`K` becomes an `F`-embedding of `K` into its algebraic closure by following it with
the structure map `K → AlgebraicClosure K`. -/
noncomputable def toEmb (e : K ≃ₐ[F] K) : Field.Emb F K :=
  (IsScalarTower.toAlgHom F K (AlgebraicClosure K)).comp e.toAlgHom

/-- For a normal extension, the parent's `toEmb` is *definitionally* the inverse of
Mathlib's `Normal.algHomEquivAut` (specialised to embeddings into the algebraic
closure): `Normal.algHomEquivAut` sends `σ` to `(toAlgHom F K _).comp σ.toAlgHom`,
which is exactly `toEmb`. -/
theorem toEmb_eq_symm_algHomEquivAut [Normal F K] :
    toEmb F K = ⇑(Normal.algHomEquivAut F (AlgebraicClosure K) K).symm := rfl

/-- The equivalence `Field.Emb F K ≃ (K ≃ₐ[F] K)` for a normal extension: every
`F`-embedding of `K` into its algebraic closure restricts to an `F`-automorphism of
`K`, and conversely. This is `Normal.algHomEquivAut` read through
`Field.Emb F K = K →ₐ[F] AlgebraicClosure K`. -/
noncomputable def embEquivAlgEquiv [Normal F K] :
    Field.Emb F K ≃ (K ≃ₐ[F] K) :=
  Normal.algHomEquivAut F (AlgebraicClosure K) K

/-- **Answer to open question 2.**  For a normal extension `K / F`, the parent's
injection `toEmb` is in fact a *bijection*: the `F`-automorphisms of `K` are in
bijection with the `F`-embeddings of `K` into its algebraic closure. -/
theorem toEmb_bijective [Normal F K] : Function.Bijective (toEmb F K) := by
  rw [toEmb_eq_symm_algHomEquivAut]
  exact (Normal.algHomEquivAut F (AlgebraicClosure K) K).symm.bijective

/-- **Answer to open question 1 (the equality).**  For a normal extension `K / F`,
the separable degree equals the number of `F`-algebra automorphisms of `K`:

  `[K : F]_s = |Aut_F(K)|`.

This sharpens the parent's inequality `|Aut_F(K)| ≤ [K : F]_s` to an equality
whenever `K / F` is normal, by exhibiting the parent's injection as one half of
`Normal.algHomEquivAut`. No finiteness hypothesis is needed: for an infinite normal
extension both `Nat.card`s are `0`. -/
theorem finSepDegree_eq_card_algEquiv [Normal F K] :
    Field.finSepDegree F K = Nat.card (K ≃ₐ[F] K) :=
  Nat.card_congr (Normal.algHomEquivAut F (AlgebraicClosure K) K)

/-- The same equality written with the automorphism count on the left, matching the
shape of the parent's bound `Nat.card (K ≃ₐ[F] K) ≤ Field.finSepDegree F K`. -/
theorem card_algEquiv_eq_finSepDegree [Normal F K] :
    Nat.card (K ≃ₐ[F] K) = Field.finSepDegree F K :=
  (finSepDegree_eq_card_algEquiv F K).symm

/-- **Sharp separability boundary.**  Among *finite normal* extensions, the
automorphism count reaches the full degree `[K : F]` precisely when `K / F` is
separable.  This is what distinguishes the equality above from the Galois fact
`IsGalois.card_aut_eq_finrank`: the automorphism group always counts the separable
degree, and that equals `[K : F]` exactly in the separable (hence Galois) case. -/
theorem card_algEquiv_eq_finrank_iff_isSeparable
    [FiniteDimensional F K] [Normal F K] :
    Nat.card (K ≃ₐ[F] K) = Module.finrank F K ↔ Algebra.IsSeparable F K := by
  rw [card_algEquiv_eq_finSepDegree, Field.finSepDegree_eq_finrank_iff]

/-- **Galois corollary (recovering `IsGalois.card_aut_eq_finrank`).**  A finite
normal *separable* extension — i.e. a finite Galois extension — has exactly
`[K : F]` automorphisms.  Here it falls straight out of the normal equality plus
`[K : F]_s = [K : F]` for separable extensions. -/
theorem card_algEquiv_eq_finrank_of_normal_isSeparable
    [FiniteDimensional F K] [Normal F K] [Algebra.IsSeparable F K] :
    Nat.card (K ≃ₐ[F] K) = Module.finrank F K := by
  rw [card_algEquiv_eq_finSepDegree, Field.finSepDegree_eq_finrank_of_isSeparable]

end NormalAutEquality
