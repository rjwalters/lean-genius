/-
# Sharpness of the automorphism bound: |Aut_F(K)| = [K : F]_s ⟺ K/F normal

The parent entry `angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01-oq-05` proved the
*inequality*

  `|Aut_F(K)| ≤ [K : F]_s`        (`Nat.card (K ≃ₐ[F] K) ≤ Field.finSepDegree F K`)

for a finite extension `K / F`, via a single injection of `K ≃ₐ[F] K` into the
embeddings of `K`.  A sibling entry (`…-oq-05-oq-01`) proved that *equality holds
for normal extensions*, recovering `IsGalois.card_aut_eq_finrank`.

This file proves the **converse**, completing the picture into a sharp
characterisation:

  > For a finite extension, the automorphism bound is attained — i.e.
  > `|Aut_F(K)| = [K : F]_s` — **if and only if** `K / F` is normal.

So the automorphism group is "as large as the separable degree allows" exactly
when the extension is normal; otherwise the inequality is strict.

**Setting.**  We fix an ambient normal extension `L / F` (think: an algebraic
closure) and view `K` as an intermediate field `F ≤ K ≤ L` with `K / F` finite.
The relevant count is the number of `F`-embeddings `K →ₐ[F] L`; when `L` is
algebraically closed this is exactly the separable degree `[K : F]_s`
(`Field.finSepDegree_eq_of_isAlgClosed`).

**The two directions.**

* *(normal ⟹ equality)*  This is Mathlib's `Normal.algHomEquivAut`, the bijection
  `(K →ₐ[F] L) ≃ (K ≃ₐ[F] K)` available whenever `K / F` is normal.  Counting both
  sides gives the equality directly.

* *(equality ⟹ normal)*  The map `autToAlgHom : (K ≃ₐ[F] K) → (K →ₐ[F] L)`,
  `e ↦ K.val ∘ e`, is injective (post-composition with the injective inclusion
  `K ↪ L`).  Equal finite cardinalities upgrade injectivity to **surjectivity**
  (`Nat.bijective_iff_injective_and_card`): every embedding `σ : K →ₐ[F] L` is the
  inclusion of an *automorphism*, so its image `σ.fieldRange` is `K` itself.
  By Mathlib's normality criterion `normal_iff_forall_fieldRange_le`
  (`Normal F K ↔ ∀ σ : K →ₐ[F] L, σ.fieldRange ≤ K`), `K / F` is normal.

Combining the two yields the biconditional `normal_iff_card_aut_eq_card_algHom`,
and the algebraically-closed specialisation `normal_iff_card_aut_eq_finSepDegree`
states it with the separable degree `[K : F]_s` on the nose.

No axioms, no `sorry`, no `native_decide`.
-/
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.FieldTheory.Normal.Closure

open Field IntermediateField

namespace AngleTrisectionAutSharp

variable {F L : Type*} [Field F] [Field L] [Algebra F L] (K : IntermediateField F L)

/-- An `F`-algebra automorphism of `K`, post-composed with the inclusion
`K ↪ L`, is an `F`-embedding of `K` into the ambient field `L`. -/
noncomputable def autToAlgHom (e : K ≃ₐ[F] K) : K →ₐ[F] L :=
  K.val.comp e.toAlgHom

@[simp]
theorem autToAlgHom_apply (e : K ≃ₐ[F] K) (x : K) :
    autToAlgHom K e x = (e x : L) := rfl

/-- Post-composition with the injective inclusion `K ↪ L` is injective:
distinct automorphisms give distinct embeddings. -/
theorem autToAlgHom_injective : Function.Injective (autToAlgHom K) := by
  intro e₁ e₂ h
  ext x
  simpa only [autToAlgHom_apply] using DFunLike.congr_fun h x

/-- The image of an automorphism (followed by the inclusion) is contained in `K`:
since each value `e x` already lies in `K`, the embedding `autToAlgHom K e` has
field range `≤ K`.  (In fact it equals `K`, but `≤` is all the normality
criterion needs.) -/
theorem autToAlgHom_fieldRange_le (e : K ≃ₐ[F] K) :
    (autToAlgHom K e).fieldRange ≤ K := by
  rintro y hy
  rw [AlgHom.mem_fieldRange] at hy
  obtain ⟨x, rfl⟩ := hy
  exact SetLike.coe_mem (e x)

/-- **Sharp automorphism bound (relative form).**  For a finite intermediate
field `K` of a normal extension `L / F`, the number of `F`-automorphisms of `K`
equals the number of `F`-embeddings `K →ₐ[F] L` **iff** `K / F` is normal.

The `←` direction is `Normal.algHomEquivAut`; the `→` direction promotes the
injection `autToAlgHom` to a bijection by counting, then reads off normality from
`normal_iff_forall_fieldRange_le`. -/
theorem normal_iff_card_aut_eq_card_algHom [Normal F L] [FiniteDimensional F K] :
    Nat.card (K ≃ₐ[F] K) = Nat.card (K →ₐ[F] L) ↔ Normal F K := by
  constructor
  · intro hcard
    -- injective + equal finite cardinality ⟹ bijective
    have hbij : Function.Bijective (autToAlgHom K) :=
      (Nat.bijective_iff_injective_and_card _).mpr ⟨autToAlgHom_injective K, hcard⟩
    -- every embedding has field range ≤ K, hence K/F is normal
    refine normal_iff_forall_fieldRange_le.mpr fun σ => ?_
    obtain ⟨e, rfl⟩ := hbij.surjective σ
    exact autToAlgHom_fieldRange_le K e
  · intro _
    exact Nat.card_congr (Normal.algHomEquivAut F L K).symm

/-- **Sharp automorphism bound (separable-degree form).**  For a finite extension
`K / F` inside an algebraically closed normal extension `L`, the automorphism
count attains the separable degree, `|Aut_F(K)| = [K : F]_s`, **iff** `K / F` is
normal.  This is the parent inequality `|Aut_F(K)| ≤ [K : F]_s` sharpened to an
equality characterisation. -/
theorem normal_iff_card_aut_eq_finSepDegree
    [Normal F L] [IsAlgClosed L] [FiniteDimensional F K] :
    Nat.card (K ≃ₐ[F] K) = Field.finSepDegree F K ↔ Normal F K := by
  rw [Field.finSepDegree_eq_of_isAlgClosed (K := L) F K]
  exact normal_iff_card_aut_eq_card_algHom K

/-- **Corollary (strict inequality off the normal locus).**  If `K / F` is *not*
normal, the automorphism bound is strict: `|Aut_F(K)| < [K : F]_s`. -/
theorem card_aut_lt_finSepDegree_of_not_normal
    [Normal F L] [IsAlgClosed L] [FiniteDimensional F K] (hK : ¬ Normal F K) :
    Nat.card (K ≃ₐ[F] K) < Field.finSepDegree F K := by
  -- finiteness of the embedding count, then `≤` from the parent + `≠` from sharpness
  have hbound : Nat.card (K ≃ₐ[F] K) ≤ Field.finSepDegree F K := by
    rw [Field.finSepDegree_eq_of_isAlgClosed (K := L) F K]
    exact Nat.card_le_card_of_injective _ (autToAlgHom_injective K)
  refine lt_of_le_of_ne hbound ?_
  intro heq
  exact hK ((normal_iff_card_aut_eq_finSepDegree K).mp heq)

end AngleTrisectionAutSharp

/-!
### Capstone: the sharp characterisation over an algebraic closure

Specialising the ambient field `L` to `AlgebraicClosure F` (which is normal and
algebraically closed over `F`), every finite intermediate field `K` satisfies the
clean biconditional below.  This is the form one usually quotes: a finite
extension is normal exactly when its automorphism group has order equal to its
separable degree.
-/
namespace AngleTrisectionAutSharp

example (F : Type*) [Field F] (K : IntermediateField F (AlgebraicClosure F))
    [FiniteDimensional F K] :
    Nat.card (K ≃ₐ[F] K) = Field.finSepDegree F K ↔ Normal F K :=
  normal_iff_card_aut_eq_finSepDegree K

end AngleTrisectionAutSharp
