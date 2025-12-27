import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic

/-!
# Formula for Pythagorean Triples (Wiedijk #23)

## What This Proves
All primitive Pythagorean triples (a, b, c) where a² + b² = c² are given by:
- a = m² - n²
- b = 2mn
- c = m² + n²

for coprime integers m > n > 0 with m - n odd.

More generally, all Pythagorean triples are scalar multiples of primitive triples.

## Approach
- **Foundation (from Mathlib):** We use Mathlib's `PythagoreanTriple` structure and its
  classification theorems `isPrimitiveClassified_of_coprime` and `classified`.
- **Key Insight:** The parametrization arises from the rational parametrization of the
  unit circle: any rational point (a/c, b/c) on x² + y² = 1 corresponds to the slope
  m/n of the line from (-1, 0) to (a/c, b/c).
- **Proof Techniques:** We leverage Mathlib's complete proof which uses the rational
  circle parametrization and coprimality arguments.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves examples and corollaries
- [x] Pedagogical documentation
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `PythagoreanTriple` : The basic predicate x² + y² = z²
- `PythagoreanTriple.IsPrimitiveClassified` : Primitive triples have the parametric form
- `PythagoreanTriple.IsClassified` : All triples are multiples of the parametric form
- `PythagoreanTriple.isPrimitiveClassified_of_coprime` : Main classification theorem
- `PythagoreanTriple.classified` : General classification

## Historical Note
This result was known to ancient Babylonians (Plimpton 322 tablet, c. 1800 BCE) and
later systematically studied by Greek mathematicians. The parametric formula provides
a complete characterization: given any m > n > 0 coprime with opposite parity, the
triple (m² - n², 2mn, m² + n²) is a primitive Pythagorean triple, and every primitive
triple arises this way.

This is #23 on Wiedijk's list of 100 theorems.
-/

namespace PythagoreanTriplesFormula

/-! ## The Pythagorean Triple Predicate

A Pythagorean triple consists of three integers satisfying the Pythagorean equation. -/

/-- A Pythagorean triple is three integers (x, y, z) satisfying x² + y² = z².

This uses Mathlib's definition which works over any commutative monoid with squares. -/
example : True := by
  -- PythagoreanTriple (x y z : ℤ) : Prop
  trivial

/-- The basic equation: x * x + y * y = z * z -/
example (x y z : ℤ) : PythagoreanTriple x y z ↔ x * x + y * y = z * z :=
  Iff.rfl

/-! ## The Parametric Formula

The key insight is that all Pythagorean triples can be expressed using the parametric
formulas involving m and n. -/

/-- **Primitive Classification**: A primitive Pythagorean triple is classified if it can
be written in the form (m² - n², 2mn, m² + n²) or (2mn, m² - n², m² + n²) for coprime
integers m, n with opposite parity. -/
example : True := by
  -- PythagoreanTriple.IsPrimitiveClassified
  trivial

/-- **General Classification**: A Pythagorean triple is classified if it is a scalar
multiple of a primitively classified triple. -/
example : True := by
  -- PythagoreanTriple.IsClassified
  trivial

/-! ## The Main Theorem: Every Primitive Triple Has This Form

The central result: every primitive Pythagorean triple (where gcd(x, y) = 1) can be
expressed using the parametric formula. -/

/-- **Formula for Primitive Pythagorean Triples (Wiedijk #23, Part 1)**

If (x, y, z) is a Pythagorean triple with gcd(x, y) = 1, then it can be written as:
- Either x = m² - n² and y = 2mn
- Or x = 2mn and y = m² - n²
for some coprime integers m, n with opposite parity.

This is the "if" direction: primitive triples have the parametric form. -/
theorem primitive_triples_are_classified {x y z : ℤ}
    (h : PythagoreanTriple x y z) (hcoprime : Int.gcd x y = 1) :
    h.IsPrimitiveClassified :=
  h.isPrimitiveClassified_of_coprime hcoprime

/-- **Formula for All Pythagorean Triples (Wiedijk #23, Part 2)**

Every Pythagorean triple (x, y, z) can be written as a scalar multiple k of a
primitively classified triple:
- Either x = k(m² - n²) and y = k(2mn)
- Or x = k(2mn) and y = k(m² - n²)
for some integer k and coprime integers m, n. -/
theorem all_triples_are_classified {x y z : ℤ}
    (h : PythagoreanTriple x y z) :
    h.IsClassified :=
  h.classified

/-! ## The Parametric Form Generates Pythagorean Triples

Conversely, the parametric formula always produces valid Pythagorean triples. This is
the "only if" direction: the formula generates valid triples. -/

/-- **Verification**: The parametric formula (m² - n², 2mn, m² + n²) always gives
a Pythagorean triple.

Proof: (m² - n²)² + (2mn)² = m⁴ - 2m²n² + n⁴ + 4m²n² = m⁴ + 2m²n² + n⁴ = (m² + n²)² -/
theorem parametric_form_is_triple (m n : ℤ) :
    PythagoreanTriple (m^2 - n^2) (2 * m * n) (m^2 + n^2) := by
  unfold PythagoreanTriple
  ring

/-- **Verification**: The swapped form (2mn, m² - n², m² + n²) is also a valid triple. -/
theorem parametric_form_is_triple' (m n : ℤ) :
    PythagoreanTriple (2 * m * n) (m^2 - n^2) (m^2 + n^2) := by
  unfold PythagoreanTriple
  ring

/-! ## Classical Examples

The most famous Pythagorean triples arise from small values of m and n. -/

/-- The (3, 4, 5) triple: m = 2, n = 1
- 2² - 1² = 3
- 2·2·1 = 4
- 2² + 1² = 5 -/
theorem triple_3_4_5 : PythagoreanTriple 3 4 5 := by
  unfold PythagoreanTriple
  norm_num

/-- Verify (3, 4, 5) comes from m = 2, n = 1 -/
example : (2 : ℤ)^2 - 1^2 = 3 := by norm_num
example : 2 * 2 * 1 = (4 : ℤ) := by norm_num
example : (2 : ℤ)^2 + 1^2 = 5 := by norm_num

/-- The (5, 12, 13) triple: m = 3, n = 2
- 3² - 2² = 5
- 2·3·2 = 12
- 3² + 2² = 13 -/
theorem triple_5_12_13 : PythagoreanTriple 5 12 13 := by
  unfold PythagoreanTriple
  norm_num

/-- Verify (5, 12, 13) comes from m = 3, n = 2 -/
example : (3 : ℤ)^2 - 2^2 = 5 := by norm_num
example : 2 * 3 * 2 = (12 : ℤ) := by norm_num
example : (3 : ℤ)^2 + 2^2 = 13 := by norm_num

/-- The (8, 15, 17) triple: m = 4, n = 1
- 4² - 1² = 15
- 2·4·1 = 8
- 4² + 1² = 17 -/
theorem triple_8_15_17 : PythagoreanTriple 8 15 17 := by
  unfold PythagoreanTriple
  norm_num

/-- Verify (8, 15, 17) comes from m = 4, n = 1 -/
example : (4 : ℤ)^2 - 1^2 = 15 := by norm_num
example : 2 * 4 * 1 = (8 : ℤ) := by norm_num
example : (4 : ℤ)^2 + 1^2 = 17 := by norm_num

/-- The (7, 24, 25) triple: m = 4, n = 3
- 4² - 3² = 7
- 2·4·3 = 24
- 4² + 3² = 25 -/
theorem triple_7_24_25 : PythagoreanTriple 7 24 25 := by
  unfold PythagoreanTriple
  norm_num

/-- The (20, 21, 29) triple: m = 5, n = 2
- 5² - 2² = 21
- 2·5·2 = 20
- 5² + 2² = 29 -/
theorem triple_20_21_29 : PythagoreanTriple 20 21 29 := by
  unfold PythagoreanTriple
  norm_num

/-! ## Properties of Pythagorean Triples -/

/-- **Symmetry**: Swapping x and y preserves the Pythagorean property. -/
theorem triple_symm {x y z : ℤ} (h : PythagoreanTriple x y z) :
    PythagoreanTriple y x z :=
  h.symm

/-- **Zero Triple**: (0, 0, 0) is a (trivial) Pythagorean triple. -/
theorem triple_zero : PythagoreanTriple 0 0 0 :=
  PythagoreanTriple.zero

/-- **Coprimality**: In a primitive triple, one leg is even and one is odd (in mod 2 terms). -/
theorem even_odd_of_coprime {x y z : ℤ}
    (h : PythagoreanTriple x y z) (hcoprime : Int.gcd x y = 1) :
    (x % 2 = 0 ∧ y % 2 = 1) ∨ (x % 2 = 1 ∧ y % 2 = 0) :=
  h.even_odd_of_coprime hcoprime

/-! ## Why the Formula Works

The derivation of the formula uses the rational parametrization of the unit circle.

**Key Insight**: Any rational point (p/q, r/s) on the unit circle x² + y² = 1 corresponds
to a Pythagorean triple when we clear denominators. The line from (-1, 0) with rational
slope t = m/n intersects the circle at a rational point, giving the parametrization.

**Geometric Interpretation**:
1. Start at (-1, 0) on the unit circle
2. Draw a line with slope t = n/m
3. Find the other intersection with the circle
4. Clear denominators to get integer solutions

**Algebraic Verification**:
Given m, n coprime with opposite parity, let:
- a = m² - n²
- b = 2mn
- c = m² + n²

Then:
a² + b² = (m² - n²)² + (2mn)²
        = m⁴ - 2m²n² + n⁴ + 4m²n²
        = m⁴ + 2m²n² + n⁴
        = (m² + n²)²
        = c²

The coprimality and parity conditions ensure gcd(a, b) = 1, making it primitive.
-/

/-! ## Non-primitive Triples

Multiples of primitive triples give all Pythagorean triples. -/

/-- Scaling a Pythagorean triple by k gives another triple. -/
theorem scale_triple {x y z : ℤ} (h : PythagoreanTriple x y z) (k : ℤ) :
    PythagoreanTriple (k * x) (k * y) (k * z) :=
  h.mul k

/-- The (6, 8, 10) triple is 2 × (3, 4, 5). -/
theorem triple_6_8_10 : PythagoreanTriple 6 8 10 := by
  have h := scale_triple triple_3_4_5 2
  simp at h
  exact h

/-- The (9, 12, 15) triple is 3 × (3, 4, 5). -/
theorem triple_9_12_15 : PythagoreanTriple 9 12 15 := by
  have h := scale_triple triple_3_4_5 3
  simp at h
  exact h

/-! ## Summary of Main Results -/

#check primitive_triples_are_classified
#check all_triples_are_classified
#check parametric_form_is_triple

end PythagoreanTriplesFormula
