/-
# Pythagorean Triples OQ-05: the Brahmagupta–Fibonacci identity

## Open Question
Formalize the two-squares identity
    (a² + b²)·(c² + d²) = (a·c − b·d)² + (a·d + b·c)²
over a commutative ring, and derive that "being a sum of two squares" is closed under
multiplication.

## Approach
The identity is a polynomial identity, dispatched by `ring`. Its content is structural:
it expresses the multiplicativity of the norm `N(a + b·i) = a² + b²` on the Gaussian
integers (equivalently `|z·w|² = |z|²·|w|²` for `z, w ∈ ℂ`), and it is the algebraic
heart of the classification of which integers are sums of two squares (the set is closed
under multiplication, so it suffices to understand primes). A second form with the signs
swapped, `(a·c + b·d)² + (a·d − b·c)²`, comes from conjugating one factor.

Sorry-free and axiom-free.
-/
import Mathlib

namespace PythagoreanTriplesOQ05

section CommRing

variable {R : Type*} [CommRing R]

/-- **The Brahmagupta–Fibonacci (two-squares) identity** over any commutative ring:
`(a² + b²)(c² + d²) = (ac − bd)² + (ad + bc)²`. -/
theorem sq_add_sq_mul_sq_add_sq (a b c d : R) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 := by
  ring

/-- The conjugate form of the identity, obtained by swapping the roles of the cross terms:
`(a² + b²)(c² + d²) = (ac + bd)² + (ad − bc)²`. -/
theorem sq_add_sq_mul_sq_add_sq' (a b c d : R) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 := by
  ring

/-- A predicate: `x` is a sum of two squares. -/
def IsSumOfTwoSquares (x : R) : Prop := ∃ a b : R, x = a ^ 2 + b ^ 2

/-- **Sums of two squares are closed under multiplication.** This is the structural
consequence of the Brahmagupta–Fibonacci identity. -/
theorem IsSumOfTwoSquares.mul {x y : R}
    (hx : IsSumOfTwoSquares x) (hy : IsSumOfTwoSquares y) :
    IsSumOfTwoSquares (x * y) := by
  obtain ⟨a, b, rfl⟩ := hx
  obtain ⟨c, d, rfl⟩ := hy
  exact ⟨a * c - b * d, a * d + b * c, sq_add_sq_mul_sq_add_sq a b c d⟩

/-- Every square is a sum of two squares (take the second summand to be `0`). -/
theorem IsSumOfTwoSquares.sq (a : R) : IsSumOfTwoSquares (a ^ 2) :=
  ⟨a, 0, by ring⟩

/-- Closure under multiplication extends to finite products: a product of a list of
sums-of-two-squares is itself a sum of two squares. -/
theorem IsSumOfTwoSquares.listProd :
    ∀ {l : List R}, (∀ x ∈ l, IsSumOfTwoSquares x) → IsSumOfTwoSquares l.prod
  | [], _ => ⟨1, 0, by rw [List.prod_nil]; ring⟩
  | a :: l, h => by
      rw [List.prod_cons]
      exact (h a (List.mem_cons_self ..)).mul
        (IsSumOfTwoSquares.listProd fun x hx => h x (List.mem_cons_of_mem _ hx))

end CommRing

/-! ### Concrete witness over ℤ -/

/-- A concrete instance: `(1² + 2²)(1² + 1²) = 5·2 = 10 = 1² + 3²`, exhibiting `10` as a
sum of two squares via the identity. -/
example : (1 ^ 2 + 2 ^ 2) * (1 ^ 2 + 1 ^ 2) = (1 : ℤ) ^ 2 + 3 ^ 2 := by
  rw [sq_add_sq_mul_sq_add_sq (1 : ℤ) 2 1 1]; norm_num

end PythagoreanTriplesOQ05
