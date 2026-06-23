import Mathlib

/-
# Denumerability of localizations — the fraction field of a countable ring is countable

## What this proves

The root of this problem family is the classical fact that the rationals `ℚ` are
**denumerable** (countably infinite).  Earlier entries generalised the *polynomial*
side — `#(R[X]) = ℵ₀`, and the multivariate / monoid-algebra variants over a countable
ring.  This entry generalises the *rationals themselves*: `ℚ` is, by construction, the
field of fractions of `ℤ`, and the operation "invert a multiplicative set" never escapes
countability.

* `countable_of_isLocalization` — **the headline.**  For a countable commutative
  semiring `R`, a submonoid `M ≤ R`, and *any* localization `S` of `R` at `M`
  (`[IsLocalization M S]`), the ring `S` is countable.  This is the denumerable
  analogue of Mathlib's `IsLocalization.fintype'` (which Mathlib explicitly remarks
  "cannot be an instance").  Proof: `IsLocalization.mk'_surjective` exhibits every
  element of `S` as `mk' S r m` for some `(r, m) ∈ R × M`, and a surjective image of a
  countable type is countable.

* `Localization.instCountable` / `instCountableFractionRing` — the concrete localization
  `Localization M` and the fraction field `FractionRing R` inherit countability as
  honest instances.

* `mk_fractionRing_eq_aleph0` — for an *infinite* countable integral domain the fraction
  field is countably **infinite**: `#(FractionRing R) = ℵ₀`.

* `mk_rat_eq_aleph0` — **the loop closes.**  Applying the general theorem to
  `IsFractionRing ℤ ℚ` re-derives `#ℚ = ℵ₀`, the denumerability of the rationals, as a
  special case of the localization principle.  The non-negative rationals `ℚ≥0`
  (`IsFractionRing ℕ ℚ≥0`) follow for free in `mk_nnrat_eq_aleph0`.

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and
`sorry`-free.
-/

open Cardinal

namespace DenumerabilityRationalsOQ05OQ01OQ01OQ01

/-! ## Part 1: localizations preserve countability -/

/-- **Localizations preserve countability.**  If `R` is a countable commutative semiring
and `S` is any localization of `R` at a submonoid `M`, then `S` is countable.

This is the denumerable analogue of `IsLocalization.fintype'`.  Every `z : S` is of the
form `IsLocalization.mk' S r m` for some `(r, m) ∈ R × M` (`mk'_surjective`), so `S` is a
surjective image of the countable type `R × M`. -/
theorem countable_of_isLocalization {R : Type*} [CommSemiring R] (M : Submonoid R)
    (S : Type*) [CommSemiring S] [Algebra R S] [IsLocalization M S] [Countable R] :
    Countable S :=
  (IsLocalization.mk'_surjective (S := S) M).countable

/-- The concrete localization `Localization M` of a countable commutative semiring is
countable. -/
instance Localization.instCountable {R : Type*} [CommSemiring R] (M : Submonoid R)
    [Countable R] : Countable (Localization M) :=
  countable_of_isLocalization M (Localization M)

/-- The field of fractions of a countable commutative ring is countable. -/
instance instCountableFractionRing {R : Type*} [CommRing R] [Countable R] :
    Countable (FractionRing R) :=
  countable_of_isLocalization (nonZeroDivisors R) (FractionRing R)

/-! ## Part 2: cardinality bounds -/

/-- Any localization of a countable ring has cardinality at most `ℵ₀`. -/
theorem mk_le_aleph0_of_isLocalization {R : Type*} [CommSemiring R] (M : Submonoid R)
    (S : Type*) [CommSemiring S] [Algebra R S] [IsLocalization M S] [Countable R] :
    #S ≤ ℵ₀ :=
  have : Countable S := countable_of_isLocalization M S
  mk_le_aleph0

/-- **For an infinite countable integral domain the fraction field is denumerable.**
`#(FractionRing R) = ℵ₀`.  Countability is `instCountableFractionRing`; infinitude comes
from the injective `algebraMap R (FractionRing R)`. -/
theorem mk_fractionRing_eq_aleph0 {R : Type*} [CommRing R] [IsDomain R] [Countable R]
    [Infinite R] : #(FractionRing R) = ℵ₀ := by
  have : Infinite (FractionRing R) :=
    Infinite.of_injective _ (IsFractionRing.injective R (FractionRing R))
  exact mk_eq_aleph0 _

/-! ## Part 3: closing the loop — the rationals -/

/-- **Closing the loop.**  `ℚ` is the field of fractions of `ℤ`
(`Rat.isFractionRing : IsFractionRing ℤ ℚ`), so its denumerability `#ℚ = ℵ₀` is exactly
the localization principle applied to `ℤ`. -/
theorem mk_rat_eq_aleph0 : #ℚ = ℵ₀ := by
  have : Countable ℚ := countable_of_isLocalization (nonZeroDivisors ℤ) ℚ
  exact mk_eq_aleph0 _

/-- The non-negative rationals `ℚ≥0` are the fraction object of `ℕ`
(`NNRat.isFractionRing : IsFractionRing ℕ ℚ≥0`), hence also denumerable: `#ℚ≥0 = ℵ₀`. -/
theorem mk_nnrat_eq_aleph0 : #ℚ≥0 = ℵ₀ := by
  have : Countable ℚ≥0 := countable_of_isLocalization (nonZeroDivisors ℕ) ℚ≥0
  exact mk_eq_aleph0 _

end DenumerabilityRationalsOQ05OQ01OQ01OQ01
