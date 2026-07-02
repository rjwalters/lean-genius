/-
# Euler's Four-Square Identity: Multiplicative Structure

This file develops the *structural* consequences of Euler's four-square identity
(1748), going beyond the raw algebraic identity itself.

The parent entry `LagrangeFourSquares` records the bare identity
`(a²+b²+c²+d²)(x²+y²+z²+w²) = A²+B²+C²+D²` and notes informally that "the set of
sums-of-four-squares is closed under multiplication". Here we *prove* that
structural statement and package it:

1. **Multiplicative closure.** If `m` and `n` are each a sum of four integer
   squares, then so is `m * n` — with the four squares produced *explicitly* by
   Euler's identity (`IsSumOfFourSquares.mul`).
2. **Monoid structure.** The sums of four squares form a `Submonoid ℤ`.
3. **Sharp characterization.** Over `ℤ`, being a sum of four squares is exactly
   being nonnegative (`isSumOfFourSquares_iff_nonneg`): the "≥ 0" direction is a
   trivial positivity fact, while "0 ≤ n → sum of four squares" is Lagrange's
   theorem. So the submonoid is precisely `{n : ℤ | 0 ≤ n}`.
4. **Quaternion connection.** Euler's identity *is* the multiplicativity of the
   Hamilton quaternion norm `normSq (p * q) = normSq p * normSq q`.

Everything here is machine-checked with no additional axioms.
-/

import Mathlib

open scoped Quaternion

namespace LagrangeFourSquaresOQ05

/-! ## Euler's Four-Square Identity (the engine)

Stated over an arbitrary commutative ring; the specific quadruple `(A, B, C, D)`
below is the componentwise product of the quaternions `a + bi + cj + dk` and
`x + yi + zj + wk`. -/

/-- **Euler's Four-Square Identity (1748).** The product of two sums of four
squares is a sum of four squares, via an explicit bilinear formula. -/
theorem euler_four_square_identity {R : Type*} [CommRing R] (a b c d x y z w : R) :
    (a * x - b * y - c * z - d * w) ^ 2 +
    (a * y + b * x + c * w - d * z) ^ 2 +
    (a * z - b * w + c * x + d * y) ^ 2 +
    (a * w + b * z - c * y + d * x) ^ 2 =
    (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
  ring

/-! ## The sum-of-four-squares predicate over `ℤ` -/

/-- An integer is a sum of four squares. -/
def IsSumOfFourSquares (n : ℤ) : Prop :=
  ∃ a b c d : ℤ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n

/-- `0 = 0² + 0² + 0² + 0²`. -/
theorem IsSumOfFourSquares.zero : IsSumOfFourSquares 0 :=
  ⟨0, 0, 0, 0, by ring⟩

/-- `1 = 1² + 0² + 0² + 0²` — the multiplicative unit is a sum of four squares. -/
theorem IsSumOfFourSquares.one : IsSumOfFourSquares 1 :=
  ⟨1, 0, 0, 0, by ring⟩

/-- Every square is (trivially) a sum of four squares. -/
theorem IsSumOfFourSquares.sq (a : ℤ) : IsSumOfFourSquares (a ^ 2) :=
  ⟨a, 0, 0, 0, by ring⟩

/-- **Multiplicative closure.** If `m` and `n` are each a sum of four squares,
then so is `m * n`. The witnessing quadruple for `m * n` is built *explicitly*
from those of `m` and `n` through Euler's identity — this is the structural heart
of the four-square theorem's reduction to primes. -/
theorem IsSumOfFourSquares.mul {m n : ℤ}
    (hm : IsSumOfFourSquares m) (hn : IsSumOfFourSquares n) :
    IsSumOfFourSquares (m * n) := by
  obtain ⟨a, b, c, d, hmeq⟩ := hm
  obtain ⟨x, y, z, w, hneq⟩ := hn
  refine ⟨a * x - b * y - c * z - d * w,
          a * y + b * x + c * w - d * z,
          a * z - b * w + c * x + d * y,
          a * w + b * z - c * y + d * x, ?_⟩
  rw [euler_four_square_identity, hmeq, hneq]

/-! ## Monoid structure

The sums of four squares form a submonoid of `(ℤ, ·)`. -/

/-- The sums of four squares as a `Submonoid ℤ`. -/
def sumOfFourSquares : Submonoid ℤ where
  carrier := {n : ℤ | IsSumOfFourSquares n}
  one_mem' := IsSumOfFourSquares.one
  mul_mem' := IsSumOfFourSquares.mul

@[simp]
theorem mem_sumOfFourSquares {n : ℤ} :
    n ∈ sumOfFourSquares ↔ IsSumOfFourSquares n := Iff.rfl

/-! ## Sharp characterization: sum of four squares ⟺ nonnegative

Over `ℤ` the sum-of-four-squares property is *exactly* nonnegativity. One
direction is elementary positivity; the converse is Lagrange's theorem, applied
to the natural number `n.toNat`. -/

/-- A sum of four squares is nonnegative. -/
theorem IsSumOfFourSquares.nonneg {n : ℤ} (h : IsSumOfFourSquares n) : 0 ≤ n := by
  obtain ⟨a, b, c, d, rfl⟩ := h
  positivity

/-- Every nonnegative integer is a sum of four squares (Lagrange 1770, lifted to
`ℤ`). -/
theorem isSumOfFourSquares_of_nonneg {n : ℤ} (hn : 0 ≤ n) : IsSumOfFourSquares n := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n.toNat
  refine ⟨a, b, c, d, ?_⟩
  have : ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 : ℕ) : ℤ) = ((n.toNat : ℕ) : ℤ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h
  push_cast at this
  rw [this, Int.toNat_of_nonneg hn]

/-- **Sharp characterization.** An integer is a sum of four squares iff it is
nonnegative. Consequently `sumOfFourSquares = {n : ℤ | 0 ≤ n}` as a set. -/
theorem isSumOfFourSquares_iff_nonneg {n : ℤ} :
    IsSumOfFourSquares n ↔ 0 ≤ n :=
  ⟨IsSumOfFourSquares.nonneg, isSumOfFourSquares_of_nonneg⟩

/-- The submonoid of sums of four squares is exactly the nonnegative integers. -/
theorem sumOfFourSquares_carrier :
    (sumOfFourSquares : Set ℤ) = {n : ℤ | 0 ≤ n} := by
  ext n
  simp [sumOfFourSquares, isSumOfFourSquares_iff_nonneg, Set.mem_setOf_eq]

/-! ## Natural-number multiplicative closure

The same closure holds inside `ℕ`: a product of two sums of four natural squares
is a sum of four natural squares. Crucially we build the representation of `m * n`
*directly from the given representations of `m` and `n`* — casting to `ℤ`,
applying Euler's identity, and taking absolute values (`(t.natAbs) ^ 2 = t ^ 2`).
No appeal to Lagrange's theorem on the product is needed: this is exactly the
elementary multiplicative closure that `IsSumOfFourSquares.mul` provides. -/

/-- Multiplicativity of the sum-of-four-squares property over `ℕ`, built
explicitly from the two input representations via Euler's identity. -/
theorem nat_sum_four_squares_mul {m n : ℕ}
    (hm : ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = m)
    (hn : ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n) :
    ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = m * n := by
  obtain ⟨a, b, c, d, hm'⟩ := hm
  obtain ⟨x, y, z, w, hn'⟩ := hn
  -- Lift the two representations to `ℤ` and combine them with Euler's identity.
  have hmZ : IsSumOfFourSquares (m : ℤ) :=
    ⟨a, b, c, d, by exact_mod_cast hm'⟩
  have hnZ : IsSumOfFourSquares (n : ℤ) :=
    ⟨x, y, z, w, by exact_mod_cast hn'⟩
  obtain ⟨p, q, r, s, hpqrs⟩ := hmZ.mul hnZ
  -- Realise the (possibly negative) integer witnesses as naturals via natAbs.
  refine ⟨p.natAbs, q.natAbs, r.natAbs, s.natAbs, ?_⟩
  have hcast : ((p.natAbs ^ 2 + q.natAbs ^ 2 + r.natAbs ^ 2 + s.natAbs ^ 2 : ℕ) : ℤ)
      = ((m * n : ℕ) : ℤ) := by
    -- `push_cast` rewrites `(↑t.natAbs)` to `|t|`; `sq_abs` then gives `|t|² = t²`.
    push_cast
    rw [sq_abs, sq_abs, sq_abs, sq_abs, hpqrs]
  exact_mod_cast hcast

/-! ## The quaternion connection

Euler's identity is not a coincidence: it *is* the multiplicativity of the
Hamilton quaternion norm. For integer quaternions `p, q : ℍ[ℤ]`, the norm
`normSq` sends products to products, and `normSq` of a quaternion is the sum of
the squares of its four components. -/

open Quaternion in
/-- The Hamilton quaternion norm is multiplicative on `ℍ[ℤ]`; this is Euler's
four-square identity in disguise. -/
theorem quaternion_normSq_mul (p q : ℍ[ℤ]) :
    Quaternion.normSq (p * q) = Quaternion.normSq p * Quaternion.normSq q :=
  map_mul Quaternion.normSq p q

/-- Euler's identity recovered from quaternion norm multiplicativity: expanding
`normSq` of a quaternion into its four components and applying
`quaternion_normSq_mul` reproduces the four-square identity. -/
theorem euler_via_quaternion (a b c d x y z w : ℤ) :
    (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) =
      Quaternion.normSq ((⟨a, b, c, d⟩ : ℍ[ℤ]) * (⟨x, y, z, w⟩ : ℍ[ℤ])) := by
  rw [quaternion_normSq_mul]
  simp only [Quaternion.normSq_def']

end LagrangeFourSquaresOQ05
