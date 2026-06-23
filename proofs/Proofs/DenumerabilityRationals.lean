import Mathlib.Data.Rat.Denumerable
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic

/-!
# Denumerability of the Rational Numbers

## What This Proves
We prove Wiedijk's Theorem #3: The set of rational numbers ℚ is countable (denumerable).
This means there exists a bijection between ℕ and ℚ—despite the rationals being dense
in the reals, they can still be "listed" by the natural numbers.

## Approach
- **Foundation (from Mathlib):** We use `Mathlib.Data.Rat.Denumerable` which provides
  the `Denumerable ℚ` instance. This instance constructs an explicit encoding of
  rationals via the pairing of numerator and denominator.
- **Original Contributions:** We provide alternative formulations of the theorem,
  demonstrate the explicit bijection, and add pedagogical documentation showing
  how the diagonal enumeration works.
- **Proof Techniques Demonstrated:** Type equivalences, bijection construction,
  use of the Denumerable typeclass.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [ ] Proves extensions/corollaries
- [ ] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Denumerable ℚ` : The main typeclass instance proving rationals are denumerable
- `Denumerable.eqv` : The explicit equivalence α ≃ ℕ for denumerable types
- `Countable` : A weaker notion that follows from Denumerable

## Historical Note
Georg Cantor proved this result in the 1870s using his famous diagonal argument.
The key insight is that while ℚ is dense (between any two rationals lies another),
it is still only "as big" as ℕ. This contrasts sharply with ℝ, which Cantor later
proved to be uncountable (see CantorDiagonalization.lean).

This is #3 on Wiedijk's list of 100 theorems.
-/

namespace DenumerabilityRationals

/-! ## The Main Result: ℚ is Denumerable

A type is **denumerable** if there exists a bijection with ℕ. This is stronger
than just being countable (having an injection into ℕ) because it requires the
type to be infinite AND constructively bijective with ℕ.

Mathlib provides `Denumerable ℚ` which gives us an explicit encoding. -/

/-- The rationals are denumerable - this is the core instance from Mathlib. -/
example : Denumerable ℚ := inferInstance

/-- The explicit equivalence between ℕ and ℚ.

This gives us functions in both directions that are mutual inverses.
Note: `Denumerable.eqv` gives `ℚ ≃ ℕ`, so we use `.symm` for `ℕ ≃ ℚ`. -/
def natEquivRat : ℕ ≃ ℚ := (Denumerable.eqv ℚ).symm

/-! ## Alternative Formulations -/

/-- **Theorem (Cantor)**: There exists a bijection between ℕ and ℚ.

This is the classical statement of the denumerability of rationals. -/
theorem rationals_denumerable : ∃ f : ℕ ≃ ℚ, Function.Bijective f := by
  use (Denumerable.eqv ℚ).symm
  exact (Denumerable.eqv ℚ).symm.bijective

/-- The rationals are countable (weaker statement).

Every denumerable type is countable, but not vice versa—finite types are
countable but not denumerable. -/
theorem rationals_countable : Countable ℚ := inferInstance

/-- There exists a surjection from ℕ onto ℚ.

This means every rational can be "reached" from some natural number. -/
theorem exists_surjection_nat_to_rat : ∃ f : ℕ → ℚ, Function.Surjective f := by
  use (Denumerable.eqv ℚ).symm
  exact (Denumerable.eqv ℚ).symm.surjective

/-- There exists an injection from ℚ into ℕ.

This means we can assign a unique natural number to each rational. -/
theorem exists_injection_rat_to_nat : ∃ f : ℚ → ℕ, Function.Injective f := by
  use Denumerable.eqv ℚ
  exact (Denumerable.eqv ℚ).injective

/-! ## The Encoding Explained

Mathlib's encoding works as follows:
1. Represent each rational q as a pair (num, denom) where:
   - denom > 0
   - gcd(|num|, denom) = 1 (reduced form)
2. Use Cantor's pairing function to encode pairs of natural numbers
3. Handle the sign of num separately

The key insight is that integer pairs form a countable set (ℤ × ℕ₊ is denumerable),
and the reduced-form constraint only selects a subset—subsets of countable sets
are countable. -/

/-- We can decode any natural number to get a rational. -/
def decodeNatToRat (n : ℕ) : ℚ := (Denumerable.eqv ℚ).symm n

/-- We can encode any rational to get a natural number. -/
def encodeRatToNat (q : ℚ) : ℕ := Denumerable.eqv ℚ q

/-- Encoding then decoding gives back the original rational. -/
theorem decode_encode (q : ℚ) : decodeNatToRat (encodeRatToNat q) = q := by
  simp [decodeNatToRat, encodeRatToNat]

/-- Decoding then encoding gives back the original natural number. -/
theorem encode_decode (n : ℕ) : encodeRatToNat (decodeNatToRat n) = n := by
  simp [decodeNatToRat, encodeRatToNat]

/-! ## Comparison with the Reals

This result pairs beautifully with Cantor's diagonal argument showing ℝ is
UNcountable. Together they establish:
- |ℕ| = |ℤ| = |ℚ| = ℵ₀ (all countably infinite)
- |ℝ| = 2^ℵ₀ > ℵ₀ (uncountably infinite)

The rationals are "thin" in ℝ despite being dense—almost all real numbers
are irrational! This is quantified by measure theory: ℚ has Lebesgue measure zero. -/

/-- The rationals are infinite (required for denumerability). -/
theorem rationals_infinite : Infinite ℚ := inferInstance

/-! ## Visualization of Cantor's Enumeration

One classic way to enumerate ℚ⁺ is via diagonals:

```
     1   2   3   4   5  ...
   +------------------------
 1 | 1/1 2/1 3/1 4/1 5/1 ...
 2 | 1/2 2/2 3/2 4/2 5/2 ...
 3 | 1/3 2/3 3/3 4/3 5/3 ...
 4 | 1/4 2/4 3/4 4/4 5/4 ...
   | ...

Enumerate along diagonals (skipping non-reduced fractions):
1/1, 2/1, 1/2, 3/1, 1/3, 4/1, 3/2, 2/3, 1/4, ...
 ↓    ↓    ↓    ↓    ↓    ↓    ↓    ↓    ↓
 1    2    1/2  3   1/3   4   3/2  2/3  1/4  ...

Each positive rational appears exactly once (in reduced form).
Extend to all of ℚ by interleaving with negatives and zero:
0, 1, -1, 2, -2, 1/2, -1/2, 3, -3, 1/3, -1/3, ...
```

This diagonal traversal is essentially what Mathlib's encoding does,
but with a more efficient pairing function. -/

/-! ## Connection to Cardinality

In Mathlib's cardinal arithmetic, denumerability corresponds to having
cardinality ℵ₀ (aleph-null), the smallest infinite cardinal. -/

/-- The cardinality of ℚ equals ℵ₀.

Both ℚ and ℕ have cardinality ℵ₀, the smallest infinite cardinal. -/
theorem card_rat_eq_aleph0 : Cardinal.mk ℚ = Cardinal.aleph0 :=
  Cardinal.mk_denumerable ℚ

/-- The cardinality of ℚ equals the cardinality of ℕ. -/
theorem card_rat_eq_card_nat : Cardinal.mk ℚ = Cardinal.mk ℕ := by
  rw [card_rat_eq_aleph0, Cardinal.mk_denumerable ℕ]

/-! ## Philosophical Significance

This theorem has deep philosophical implications:
1. **Infinity comes in sizes**: Not all infinite sets are equally large
2. **Density ≠ cardinality**: ℚ is dense in ℝ but much "smaller"
3. **Countability is robust**: Countable unions of countable sets are countable
4. **The reals are special**: Adding limits creates uncountably many new numbers

Cantor's discovery of different sizes of infinity was initially controversial
but is now foundational to modern mathematics. -/

#check rationals_denumerable
#check rationals_countable
#check natEquivRat
#check card_rat_eq_card_nat

end DenumerabilityRationals
