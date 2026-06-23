import Mathlib

/-
# Localization preserves cardinality for infinite rings — `#(FractionRing R) = #R`

## What this proves

The parent entry showed that localization never escapes *countability*: the fraction
field of a countable ring is countable (`#(FractionRing R) = ℵ₀`).  That argument is
really a cardinal-arithmetic fact specialised to `ℵ₀`.  This entry isolates the
quantitative core and proves it for an **arbitrary infinite** ring: inverting a
multiplicative set never changes the cardinality.

* `mk_isLocalization_le` — **the headline bound.**  For an *infinite* commutative
  semiring `R`, a submonoid `M`, and any localization `S` of `R` at `M`, `#S ≤ #R`.
  Every `z : S` is `mk' S r m` for some `(r, m) ∈ R × M` (`IsLocalization.mk'_surjective`),
  so `#S ≤ #(R × M) = #R · #M ≤ #R · #R = #R`, the last step being
  `Cardinal.mul_eq_self` for an infinite cardinal.

* `mk_localization_eq_of_le_nonZeroDivisors` — when `M ≤ R⁰` the structure map
  `algebraMap R S` is injective, so the bound upgrades to an **equality** `#S = #R`.

* `mk_isFractionRing_eq` / `mk_fractionRing_eq` — the fraction field of an infinite
  integral domain has exactly the cardinality of the domain: `#(FractionRing R) = #R`.

* `mk_rat_eq_int` / `mk_rat_eq_aleph0` — **the loop closes.**  `ℚ` is the field of
  fractions of `ℤ`, so `#ℚ = #ℤ`, and since `ℤ` is denumerable this re-derives
  `#ℚ = ℵ₀` (the parent's headline) as the `R = ℤ` instance of the cardinality
  principle — but now via the *equality* `#ℚ = #ℤ`, not just an `ℵ₀` bound.

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and
`sorry`-free.
-/

open Cardinal

universe u

namespace DenumerabilityRationalsOQ05OQ01OQ01OQ01OQ01

/-! ## Part 1: localization never increases cardinality -/

/-- **Localization never increases cardinality (infinite base).**  For an infinite
commutative semiring `R` and any localization `S` of `R` at a submonoid `M`, `#S ≤ #R`.

`IsLocalization.mk'_surjective` exhibits `S` as a surjective image of `R × M`, so
`#S ≤ #(R × M)`.  Since `R` is infinite, `#(R × M) = #R · #M ≤ #R · #R = #R`. -/
theorem mk_isLocalization_le {R : Type u} [CommSemiring R] [Infinite R] (M : Submonoid R)
    (S : Type u) [CommSemiring S] [Algebra R S] [IsLocalization M S] :
    #S ≤ #R := by
  have h1 : #S ≤ #(R × M) :=
    mk_le_of_surjective (IsLocalization.mk'_surjective (S := S) M)
  have h2 : #(R × M) ≤ #R := by
    rw [Cardinal.mk_prod]
    simp only [Cardinal.lift_id]
    calc #R * #(M : Type _) ≤ #R * #R := by
          gcongr
          exact mk_le_of_injective Subtype.val_injective
      _ = #R := mul_eq_self (aleph0_le_mk R)
  exact h1.trans h2

/-! ## Part 2: equality when the structure map is injective -/

/-- When the inverted submonoid lies in the non-zero-divisors, `algebraMap R S` is
injective, so the bound `#S ≤ #R` becomes an equality `#S = #R`. -/
theorem mk_localization_eq_of_le_nonZeroDivisors {R : Type u} [CommRing R] [Infinite R]
    {M : Submonoid R} (hM : M ≤ nonZeroDivisors R) (S : Type u) [CommRing S]
    [Algebra R S] [IsLocalization M S] :
    #S = #R :=
  le_antisymm (mk_isLocalization_le M S)
    (mk_le_of_injective (IsLocalization.injective (S := S) hM))

/-- **The fraction field of an infinite integral domain has the domain's cardinality.**
For any field of fractions `S` of an infinite integral domain `R`, `#S = #R`. -/
theorem mk_isFractionRing_eq {R : Type u} [CommRing R] [IsDomain R] [Infinite R]
    (S : Type u) [CommRing S] [Algebra R S] [IsFractionRing R S] :
    #S = #R :=
  le_antisymm (mk_isLocalization_le (nonZeroDivisors R) S)
    (mk_le_of_injective (IsFractionRing.injective R S))

/-- The concrete fraction field `FractionRing R` of an infinite integral domain has
cardinality `#R`. -/
theorem mk_fractionRing_eq {R : Type u} [CommRing R] [IsDomain R] [Infinite R] :
    #(FractionRing R) = #R :=
  mk_isFractionRing_eq (R := R) (FractionRing R)

/-! ## Part 3: closing the loop — the rationals -/

/-- **Closing the loop.**  `ℚ` is the field of fractions of `ℤ`
(`Rat.isFractionRing : IsFractionRing ℤ ℚ`), so `#ℚ = #ℤ` is the cardinality principle
applied to `ℤ`. -/
theorem mk_rat_eq_int : #ℚ = #ℤ :=
  mk_isFractionRing_eq (R := ℤ) ℚ

/-- Re-deriving the parent's headline `#ℚ = ℵ₀` from the equality `#ℚ = #ℤ` together with
the denumerability of `ℤ`. -/
theorem mk_rat_eq_aleph0 : #ℚ = ℵ₀ := by
  rw [mk_rat_eq_int]; exact mk_eq_aleph0 ℤ

end DenumerabilityRationalsOQ05OQ01OQ01OQ01OQ01
