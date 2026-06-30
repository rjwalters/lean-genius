import Mathlib

/-
# Sign Variations over an Arbitrary Ordered Field, and Invariance under Order Embeddings

*Open question from `DescartesRuleOfSignsOQ01OQ04`* (the constructive sign-variation count):
the parent built a **computable** `signVarList : List ℚ → ℕ` mirroring Mathlib's abstract
`Polynomial.signVariations`, certified by the definitional bridge
`signVarList P.coeffList = P.signVariations`, and used it to bound the *rational* positive-root
count of `P : ℚ[X]`.  Two things were left hanging:

1. **The coefficient field was pinned to `ℚ`.**  Nothing in the construction is special to `ℚ`;
   it works verbatim over any `LinearOrderedField` whose order is decidable (`ℚ`, the computable
   algebraic reals, …).  The point of `ℚ` was only that its order instances actually *reduce* in
   the kernel.  We generalise the definition and the `rfl` bridge to an arbitrary ordered field.

2. **The bound was only about *rational* roots.**  For `P : ℚ[X]`, `P.roots` lives in `ℚ`, so the
   parent's `posRoots_le_signVarList` bounds the *rational* positive roots — a strictly weaker
   statement than Descartes' rule, which is about *real* roots.  (Indeed the count is genuinely
   ℝ-valued: `X² − 2` has one sign variation but **zero** rational positive roots.)  To connect the
   computable ℚ-side count to the real-root content of Descartes one needs to know that passing
   `ℚ ↪ ℝ` does **not** change the sign-variation count.

The hinge for (2) — and the genuinely new piece of infrastructure here — is:

      **`signVariations` is invariant under any strictly monotone ring homomorphism**
      (`signVariations_map`): for `φ : F →+* K` with `StrictMono φ`,
      `(P.map φ).signVariations = P.signVariations`.

This is not in Mathlib.  It holds because the sign-variation count reads only the *signs* of the
coefficient list, and a strictly monotone ring hom preserves signs (`sign (φ x) = sign x`) and,
being injective, preserves the coefficient list up to the pointwise application of `φ`.

## Results

* `signVarList` — the computable count generalised to any `[Field F] [LinearOrder F]
  [IsStrictOrderedRing F]`; reduces in the kernel exactly when `F`'s order instances are computable.
* `signVarList_coeffList` — the bridge `signVarList P.coeffList = P.signVariations`, still by `rfl`.
* `coeffList_map_of_injective` — `(P.map φ).coeffList = P.coeffList.map φ` for injective `φ`.
* `sign_map_of_strictMono` — `sign (φ x) = sign x` for a strictly monotone ring hom.
* `signVariations_map` — **the headline**: invariance of `signVariations` under `StrictMono` ring
  homs.
* `signVarList_eq_signVariations_ratCast` — the `ℚ → ℝ` bridge: the computable ℚ-coefficient count
  equals the sign-variation count of the *real* polynomial.
* `realRoots_countP_pos_le_signVarList` — Descartes' bound for **real** positive roots, computed
  from the rational coefficient list (the honest Descartes statement, now on the computable side).

Fully verified: 0 sorries, 0 `axiom`s, no `native_decide` (worked examples use `decide`).
-/

namespace DescartesConstructiveGeneral

open Polynomial

-- Several lemmas below are stated in the ordered-field context for uniformity but are genuinely
-- more general (they need only injectivity/strict-monotonicity, not strict ordering); silence the
-- resulting "unused section variable" lint.
set_option linter.unusedSectionVars false

/-! ## Part I: the computable count over an arbitrary ordered field

`signVariations` is defined in Mathlib for any `[Semiring R] [LinearOrder R]`, and the sign map it
uses is computable whenever the order on `R` is decidable.  A `LinearOrderedField` (now spelled
`[Field F] [LinearOrder F] [IsStrictOrderedRing F]`) supplies exactly that, so the parent's
`ℚ`-specific construction lifts unchanged. -/

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- The **computable sign-variation count** on a list of coefficients (leading term first), now
over an arbitrary ordered field `F`.  Every operation — `SignType.sign`, the `· ≠ 0` filter, and
`List.destutter (· ≠ ·)` — is decidable, so the whole function reduces in the kernel precisely when
`F`'s order instances are computable (`ℚ`, computable algebraic reals, …).  This is the verbatim
generalisation of the parent's `ℚ`-only definition. -/
def signVarList (l : List F) : ℕ :=
  (((l.map SignType.sign).filter (· ≠ 0)).destutter (· ≠ ·)).length - 1

/-- **The bridge, still by `rfl`.**  Feeding `signVarList` the coefficient list of a polynomial
recovers Mathlib's abstract `signVariations` — definitionally, over *any* ordered field, exactly as
in the `ℚ` case. -/
theorem signVarList_coeffList (P : F[X]) :
    signVarList P.coeffList = P.signVariations := rfl

/-- **Descartes' bound, computable form (rational/own-field roots).**  The number of positive roots
of `P` *that lie in `F`* is at most the computable sign-variation count of its coefficient list. -/
theorem posRoots_le_signVarList (P : F[X]) :
    P.roots.countP (0 < ·) ≤ signVarList P.coeffList := by
  rw [signVarList_coeffList]
  exact P.roots_countP_pos_le_signVariations

/-- A decidable, sound certificate of "no positive roots in `F`". -/
theorem no_pos_roots_of_signVarList_zero (P : F[X]) (h : signVarList P.coeffList = 0) :
    P.roots.countP (0 < ·) = 0 :=
  Nat.le_zero.mp (h ▸ posRoots_le_signVarList P)

/-! ## Part II: invariance under a strictly monotone ring homomorphism

This is the new infrastructure.  A strictly monotone ring hom `φ : F →+* K` is injective, hence
preserves the coefficient list (up to applying `φ` pointwise), and it preserves signs, hence the
sign-variation count is unchanged. -/

section Map

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The coefficient list commutes with an **injective** ring hom: mapping the polynomial and then
listing coefficients is the same as listing coefficients and then mapping the entries.  Injectivity
is what keeps the degree (hence the list length) fixed. -/
theorem coeffList_map_of_injective (φ : F →+* K) (hφ : Function.Injective φ) (P : F[X]) :
    (P.map φ).coeffList = P.coeffList.map φ := by
  simp only [Polynomial.coeffList, Polynomial.degree_map_eq_of_injective hφ, List.map_map]
  exact List.map_congr_left fun i _ => Polynomial.coeff_map φ i

/-- **A strictly monotone ring hom preserves signs.**  `sign (φ x) = sign x`, by trichotomy on `x`:
`φ` fixes `0` and is order-preserving, so it sends positives to positives and negatives to
negatives. -/
theorem sign_map_of_strictMono (φ : F →+* K) (hφ : StrictMono φ) (x : F) :
    SignType.sign (φ x) = SignType.sign x := by
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  · rw [sign_neg hlt, sign_neg]
    simpa only [map_zero] using hφ hlt
  · subst heq; rw [map_zero, sign_zero, sign_zero]
  · rw [sign_pos hgt, sign_pos]
    simpa only [map_zero] using hφ hgt

/-- **Headline: `signVariations` is invariant under a strictly monotone ring homomorphism.**
Mapping the coefficients of `P` through an order-embedding `φ : F →+* K` changes neither the
coefficient list's signs (`sign_map_of_strictMono`) nor its length (`φ` injective), so the number of
sign changes is identical:

      `(P.map φ).signVariations = P.signVariations`.

In particular the sign-variation count is intrinsic to the *ordered-field-agnostic* sign data of the
coefficients, not to the field they live in. -/
theorem signVariations_map (φ : F →+* K) (hφ : StrictMono φ) (P : F[X]) :
    (P.map φ).signVariations = P.signVariations := by
  have key : ((P.map φ).coeffList).map SignType.sign = P.coeffList.map SignType.sign := by
    rw [coeffList_map_of_injective φ hφ.injective, List.map_map]
    exact List.map_congr_left fun x _ => sign_map_of_strictMono φ hφ x
  unfold Polynomial.signVariations
  rw [key]

end Map

/-! ## Part III: the `ℚ → ℝ` bridge — the computable count sees the *real* roots

The parent could only bound the *rational* roots of `P : ℚ[X]`.  Combining the field-genericity of
Part I with the map-invariance of Part II, the computable ℚ-coefficient count equals the
sign-variation count of the corresponding *real* polynomial, and therefore bounds the count of
positive *real* roots — which is the actual content of Descartes' rule. -/

/-- `ℚ → ℝ` is a strictly monotone ring homomorphism (it *is* the rational cast). -/
private theorem strictMono_algebraMap_rat_real :
    StrictMono (algebraMap ℚ ℝ) := by
  intro a b h
  simp only [eq_ratCast]
  exact_mod_cast h

/-- **The bridge.**  For a rational polynomial, the *computable* sign-variation count of its
coefficient list equals the sign-variation count of the polynomial pushed forward to `ℝ`.  This is
the precise sense in which the kernel-reducible ℚ-side count "sees" the real polynomial. -/
theorem signVarList_eq_signVariations_ratCast (P : ℚ[X]) :
    signVarList P.coeffList = (P.map (algebraMap ℚ ℝ)).signVariations := by
  rw [signVarList_coeffList, signVariations_map (algebraMap ℚ ℝ) strictMono_algebraMap_rat_real P]

/-- **Descartes' bound for *real* positive roots, computed from rational coefficients.**  The number
of positive *real* roots of `P : ℚ[X]` (i.e. of its image in `ℝ[X]`) is at most the computable
sign-variation count of its rational coefficient list.  Unlike the parent's `posRoots_le_signVarList`
— which only bounded the *rational* positive roots — this is the genuine Descartes statement on the
constructive side. -/
theorem realRoots_countP_pos_le_signVarList (P : ℚ[X]) :
    (P.map (algebraMap ℚ ℝ)).roots.countP (0 < ·) ≤ signVarList P.coeffList := by
  rw [signVarList_eq_signVariations_ratCast]
  exact (P.map (algebraMap ℚ ℝ)).roots_countP_pos_le_signVariations

/-! ## Part IV: worked computable examples

`signVarList` over `ℚ` reduces in the kernel, so these are discharged by `decide` (no
`native_decide`, hence no extra axioms).  They recover the parent's `ℚ`-specific examples as
instances of the now field-generic definition. -/

/-- `x³ - x² - x + 1`: coefficients `[1,-1,-1,1]`, two sign changes. -/
example : signVarList ([1, -1, -1, 1] : List ℚ) = 2 := by decide

/-- `x² + 3x + 2`: no sign changes — the no-positive-roots certificate fires. -/
example : signVarList ([1, 3, 2] : List ℚ) = 0 := by decide

/-- `x² - 1`: one sign change (interior structure irrelevant). -/
example : signVarList ([1, 0, -1] : List ℚ) = 1 := by decide

/-- Fully alternating `+ - + -`: three sign changes. -/
example : signVarList ([1, -2, 3, -4] : List ℚ) = 3 := by decide

/-- Interior zeros are ignored: `[2, 0, -3, 0, 1]` reduces to signs `+ - +`, two sign changes. -/
example : signVarList ([2, 0, -3, 0, 1] : List ℚ) = 2 := by decide

end DescartesConstructiveGeneral

-- Axiom audit: only the standard foundational axioms — no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms DescartesConstructiveGeneral.signVariations_map
#print axioms DescartesConstructiveGeneral.signVarList_eq_signVariations_ratCast
#print axioms DescartesConstructiveGeneral.realRoots_countP_pos_le_signVarList
