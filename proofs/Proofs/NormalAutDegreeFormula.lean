/-
# The Degree Factorisation for Normal Extensions: [K : F] = |Aut_F(K)| · [K : F]ᵢ

This file is a follow-up to
`angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01-oq-05-oq-01`
("The Automorphism Equality for Normal Extensions: |Aut_F(K)| = [K : F]ₛ",
`Proofs/NormalAutFinSepDegreeEquality.lean`), which proved that for a normal
extension `K / F` the automorphism count equals the **separable** degree

  `Nat.card (K ≃ₐ[F] K) = Field.finSepDegree F K`.

That equality answered "how big is `Aut_F(K)`?" in terms of the separable degree.
The natural next question is how the automorphism count sits inside the *full*
degree `[K : F]`, which for an inseparable extension is strictly larger than the
separable degree.

**The factorisation.**  Mathlib records the multiplicativity of the two halves of
the degree, `Field.finSepDegree_mul_finInsepDegree`:

  `[K : F]ₛ · [K : F]ᵢ = [K : F]`,

where `[K : F]ᵢ = Field.finInsepDegree F K = finrank (separableClosure F K) K` is the
inseparable degree.  Substituting the parent's `Nat.card (K ≃ₐ[F] K) = [K : F]ₛ`
turns this into a statement *about the automorphism group*:

  `[K : F] = |Aut_F(K)| · [K : F]ᵢ`            (`finrank_eq_card_algEquiv_mul_finInsepDegree`).

This is the genuinely new content.  Mathlib's `finSepDegree_mul_finInsepDegree`
speaks only of the separable degree; the bridge to the *automorphism count*
requires normality and is supplied by the parent.  Three structural consequences
fall out immediately:

* **Divisibility** (`card_algEquiv_dvd_finrank`): for any normal `K / F`,
  `|Aut_F(K)| ∣ [K : F]`, with cofactor exactly the inseparable degree.  This is
  the inseparable refinement of the Galois fact `|Gal(K/F)| = [K : F]`: the
  automorphism group never sees the inseparable part of the degree, but it always
  divides it.

* **The inseparable degree as a quotient** (`finInsepDegree_eq_finrank_div_card`):
  `[K : F]ᵢ = [K : F] / |Aut_F(K)|` for a finite normal extension — the
  automorphism count measures exactly the separable part, so the leftover quotient
  *is* the inseparable degree.

* **The separability boundary** (`card_algEquiv_eq_finrank_iff_isSeparable`): the
  automorphism count reaches the full degree iff the inseparable degree is `1`, i.e.
  iff `K / F` is separable — recovering, *through the factorisation*, the boundary
  the parent proved directly, and the Galois corollary
  `IsGalois.card_aut_eq_finrank`.

No axioms, no `sorry`, no `native_decide`.
-/
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.FieldTheory.PurelyInseparable.Basic

open Field Module

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

namespace NormalAutDegreeFormula

/-- **Parent equality, recalled.**  For a normal extension `K / F` the number of
`F`-algebra automorphisms of `K` equals the separable degree `[K : F]ₛ`.  This is the
content of `NormalAutEquality.card_algEquiv_eq_finSepDegree`; we reprove it here in a
single line — the parent's injection `toEmb` is one half of `Normal.algHomEquivAut`,
so counting both sides of that equivalence gives the equality. -/
theorem card_algEquiv_eq_finSepDegree [Normal F K] :
    Nat.card (K ≃ₐ[F] K) = Field.finSepDegree F K :=
  (Nat.card_congr (Normal.algHomEquivAut F (AlgebraicClosure K) K)).symm

/-- **The degree factorisation.**  For a normal extension `K / F`, the field degree
factors as the automorphism count times the inseparable degree:

  `[K : F] = |Aut_F(K)| · [K : F]ᵢ`.

No finiteness hypothesis is needed: for an infinite normal extension every term is
`0` and the identity reads `0 = 0`.  This is the parent's separable-degree equality
fed into Mathlib's `finSepDegree_mul_finInsepDegree`. -/
theorem finrank_eq_card_algEquiv_mul_finInsepDegree [Normal F K] :
    finrank F K = Nat.card (K ≃ₐ[F] K) * Field.finInsepDegree F K := by
  rw [card_algEquiv_eq_finSepDegree]
  exact (Field.finSepDegree_mul_finInsepDegree F K).symm

/-- **Divisibility.**  For any normal extension `K / F`, the automorphism count
divides the full degree: `|Aut_F(K)| ∣ [K : F]`.  The cofactor is exactly the
inseparable degree `[K : F]ᵢ`.  For a Galois (normal *and* separable) extension the
cofactor is `1` and this recovers `|Gal(K/F)| = [K : F]`; in general the
automorphism group only ever divides the degree, never exceeds the separable part. -/
theorem card_algEquiv_dvd_finrank [Normal F K] :
    Nat.card (K ≃ₐ[F] K) ∣ finrank F K :=
  ⟨Field.finInsepDegree F K, finrank_eq_card_algEquiv_mul_finInsepDegree F K⟩

/-- The automorphism count of a finite normal extension is positive — it equals the
separable degree, which is nonzero in the finite-dimensional case. -/
theorem card_algEquiv_pos [Normal F K] [FiniteDimensional F K] :
    0 < Nat.card (K ≃ₐ[F] K) := by
  rw [card_algEquiv_eq_finSepDegree]
  exact Nat.pos_of_ne_zero (NeZero.ne _)

/-- **The inseparable degree as a quotient.**  For a finite normal extension, the
inseparable degree is precisely the full degree divided by the automorphism count:

  `[K : F]ᵢ = [K : F] / |Aut_F(K)|`.

Since `|Aut_F(K)|` measures exactly the separable part of the degree, the remaining
quotient is the inseparable degree. -/
theorem finInsepDegree_eq_finrank_div_card [Normal F K] [FiniteDimensional F K] :
    Field.finInsepDegree F K = finrank F K / Nat.card (K ≃ₐ[F] K) := by
  rw [finrank_eq_card_algEquiv_mul_finInsepDegree,
    Nat.mul_div_cancel_left _ (card_algEquiv_pos F K)]

/-- **The separability boundary, via the factorisation.**  For a finite normal
extension, the automorphism count reaches the full degree iff the inseparable degree
collapses to `1`.  This is the factorisation `[K : F] = |Aut_F(K)| · [K : F]ᵢ` read as
a cancellation: with `|Aut_F(K)| > 0`, equality `|Aut_F(K)| = [K : F]` forces the
inseparable cofactor to be `1`. -/
theorem card_algEquiv_eq_finrank_iff_finInsepDegree_eq_one
    [Normal F K] [FiniteDimensional F K] :
    Nat.card (K ≃ₐ[F] K) = finrank F K ↔ Field.finInsepDegree F K = 1 := by
  rw [finrank_eq_card_algEquiv_mul_finInsepDegree]
  constructor
  · intro h
    have hmul : Nat.card (K ≃ₐ[F] K) * 1
        = Nat.card (K ≃ₐ[F] K) * Field.finInsepDegree F K := by
      rw [mul_one]; exact h
    exact (Nat.eq_of_mul_eq_mul_left (card_algEquiv_pos F K) hmul).symm
  · intro h; rw [h, mul_one]

/-- **Separability boundary (intrinsic form).**  Recovering, through the
factorisation, the parent's boundary: a finite normal extension has full
automorphism count iff it is separable — i.e. iff it is Galois. -/
theorem card_algEquiv_eq_finrank_iff_isSeparable
    [Normal F K] [FiniteDimensional F K] :
    Nat.card (K ≃ₐ[F] K) = finrank F K ↔ Algebra.IsSeparable F K := by
  rw [card_algEquiv_eq_finrank_iff_finInsepDegree_eq_one,
    isSeparable_iff_finInsepDegree_eq_one]

/-- **Galois corollary.**  A finite normal *separable* extension — i.e. a finite
Galois extension — has exactly `[K : F]` automorphisms.  Here it drops out of the
factorisation once the inseparable degree is `1`, recovering
`IsGalois.card_aut_eq_finrank`. -/
theorem card_algEquiv_eq_finrank_of_isSeparable
    [Normal F K] [FiniteDimensional F K] [Algebra.IsSeparable F K] :
    Nat.card (K ≃ₐ[F] K) = finrank F K :=
  (card_algEquiv_eq_finrank_iff_isSeparable F K).mpr ‹_›

end NormalAutDegreeFormula
