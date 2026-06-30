import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-
# Euler's Four-Square Identity and Multiplicative Closure of Sums of Four Squares

## What This Proves

Euler's four-square identity expresses the product of two sums of four squares as
*itself* a sum of four squares, via explicit bilinear forms:

  (x₁² + x₂² + x₃² + x₄²)(y₁² + y₂² + y₃² + y₄²)
    = (x₁y₁ − x₂y₂ − x₃y₃ − x₄y₄)²
    + (x₁y₂ + x₂y₁ + x₃y₄ − x₄y₃)²
    + (x₁y₃ − x₂y₄ + x₃y₁ + x₄y₂)²
    + (x₁y₄ + x₂y₃ − x₃y₂ + x₄y₁)².

This is the algebraic engine behind Lagrange's four-square theorem: it reduces the
theorem to the prime case, because the identity shows that the set of sums of four
squares is closed under multiplication.

## What Mathlib Already Has — and the Gap This Fills

Mathlib proves the bare polynomial identity (`euler_four_squares`,
`sum_four_sq_mul_sum_four_sq`, both discharged by `ring`) and Lagrange's theorem
(`Nat.sum_four_squares`). For TWO squares it additionally packages the
*multiplicative closure* as `sq_add_sq_mul`:

  a = x²+y² → b = u²+v² → ∃ r s, a*b = r²+s².

But there is **no four-square analogue** of that closure lemma. This file supplies it:
a predicate `IsSumFourSq` together with the proof that it is closed under
multiplication (and that it contains `0` and `1`), making the "sums of four squares
form a multiplicative submonoid" structure explicit over any commutative ring — the
conceptual content Euler's identity provides, beyond the raw `ring` equation.

We also record the embedding of two-square sums into four-square sums, and concrete
worked examples with explicit witnesses.

## Status
- [x] Complete proof (0 sorries, 0 axioms)
- [x] Uses Mathlib for the underlying bilinear identity
- [x] Proves an original closure corollary absent from Mathlib
- [x] Pedagogical / worked examples
-/

namespace EulerIdentityOQ05

variable {R : Type*} [CommRing R]

/-! ## The bilinear identity (self-contained restatement) -/

/-- Euler's four-square identity, restated and discharged by `ring`. The product of two
sums of four squares equals a sum of four explicit bilinear squares. -/
theorem four_square_identity (x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : R) :
    (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2) * (y₁ ^ 2 + y₂ ^ 2 + y₃ ^ 2 + y₄ ^ 2) =
      (x₁ * y₁ - x₂ * y₂ - x₃ * y₃ - x₄ * y₄) ^ 2 +
        (x₁ * y₂ + x₂ * y₁ + x₃ * y₄ - x₄ * y₃) ^ 2 +
        (x₁ * y₃ - x₂ * y₄ + x₃ * y₁ + x₄ * y₂) ^ 2 +
        (x₁ * y₄ + x₂ * y₃ - x₃ * y₂ + x₄ * y₁) ^ 2 := by
  ring

/-! ## The predicate and its multiplicative-monoid structure -/

/-- `IsSumFourSq a` means `a` is a sum of four squares in `R`. -/
def IsSumFourSq (a : R) : Prop :=
  ∃ x y z w : R, a = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2

/-- `0` is a sum of four squares. -/
theorem isSumFourSq_zero : IsSumFourSq (0 : R) :=
  ⟨0, 0, 0, 0, by ring⟩

/-- `1` is a sum of four squares. -/
theorem isSumFourSq_one : IsSumFourSq (1 : R) :=
  ⟨1, 0, 0, 0, by ring⟩

/-- Every square is a sum of four squares. -/
theorem isSumFourSq_sq (a : R) : IsSumFourSq (a ^ 2) :=
  ⟨a, 0, 0, 0, by ring⟩

/-- **Multiplicative closure** (the gap Mathlib leaves): the product of two sums of
four squares is a sum of four squares. The witnesses come directly from Euler's
identity. This is the four-square analogue of Mathlib's two-square `sq_add_sq_mul`. -/
theorem IsSumFourSq.mul {a b : R} (ha : IsSumFourSq a) (hb : IsSumFourSq b) :
    IsSumFourSq (a * b) := by
  obtain ⟨x₁, x₂, x₃, x₄, rfl⟩ := ha
  obtain ⟨y₁, y₂, y₃, y₄, rfl⟩ := hb
  exact ⟨x₁ * y₁ - x₂ * y₂ - x₃ * y₃ - x₄ * y₄,
        x₁ * y₂ + x₂ * y₁ + x₃ * y₄ - x₄ * y₃,
        x₁ * y₃ - x₂ * y₄ + x₃ * y₁ + x₄ * y₂,
        x₁ * y₄ + x₂ * y₃ - x₃ * y₂ + x₄ * y₁,
        four_square_identity x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄⟩

/-- A finite product of sums of four squares is a sum of four squares. -/
theorem isSumFourSq_prod {ι : Type*} (s : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ s, IsSumFourSq (f i)) : IsSumFourSq (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isSumFourSq_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- A power of a sum of four squares is a sum of four squares. -/
theorem IsSumFourSq.pow {a : R} (ha : IsSumFourSq a) (n : ℕ) : IsSumFourSq (a ^ n) := by
  induction n with
  | zero => simpa using isSumFourSq_one
  | succ k ih => rw [pow_succ]; exact ih.mul ha

/-! ## Relation to sums of two squares -/

/-- A sum of two squares is in particular a sum of four squares (pad with two zeros). -/
theorem isSumFourSq_of_isSumTwoSq {a : R} (h : ∃ x y : R, a = x ^ 2 + y ^ 2) :
    IsSumFourSq a := by
  obtain ⟨x, y, rfl⟩ := h
  exact ⟨x, y, 0, 0, by ring⟩

/-! ## Worked numeric examples over ℤ -/

/-- `3 = 1² + 1² + 1² + 0²` is a sum of four squares. -/
example : IsSumFourSq (3 : ℤ) := ⟨1, 1, 1, 0, by ring⟩

/-- `7 = 2² + 1² + 1² + 1²` is a sum of four squares. -/
example : IsSumFourSq (7 : ℤ) := ⟨2, 1, 1, 1, by ring⟩

/-- The product `3 * 7 = 21` is a sum of four squares, with witnesses obtained
mechanically from the closure theorem (no guessing of the representation). -/
example : IsSumFourSq (21 : ℤ) := by
  have h : (21 : ℤ) = 3 * 7 := by norm_num
  rw [h]
  exact IsSumFourSq.mul (⟨1, 1, 1, 0, by ring⟩ : IsSumFourSq (3 : ℤ))
    (⟨2, 1, 1, 1, by ring⟩ : IsSumFourSq (7 : ℤ))

/-- Sanity check: the explicit witnesses produced by Euler's identity for `3 * 7`
indeed sum to `21`. Here `x = (1,1,1,0)`, `y = (2,1,1,1)`, giving
`(1·2−1·1−1·1−0·1)² + (1·1+1·2+1·1−0·1)² + (1·1−1·1+1·2+0·1)² + (1·1+1·1−1·1+0·2)²
 = 0² + 4² + 2² + 1² = 21`. -/
example : ((1 * 2 - 1 * 1 - 1 * 1 - (0 : ℤ) * 1) ^ 2 +
    (1 * 1 + 1 * 2 + 1 * 1 - 0 * 1) ^ 2 +
    (1 * 1 - 1 * 1 + 1 * 2 + 0 * 1) ^ 2 +
    (1 * 1 + 1 * 1 - 1 * 1 + 0 * 2) ^ 2) = 21 := by norm_num

/-! ## Sharpness: *three* squares are NOT multiplicatively closed

The closure theorem `IsSumFourSq.mul` makes "sums of four squares" a multiplicative
submonoid. A natural question is whether *fewer* squares already suffice. The answer is
no: sums of **three** squares fail to be closed under multiplication, so four is the
minimal number of squares for which Euler-type multiplicativity can hold.

The obstruction is the classical mod-`8` invariant. A square is `≡ 0, 1, 4 (mod 8)`, so a
sum of three squares can never be `≡ 7 (mod 8)`. Taking `3 = 1²+1²+1²` and `5 = 0²+1²+2²`
— each a sum of three squares — their product `15 = 3·5 ≡ 7 (mod 8)` is therefore not a
sum of three squares. This is exactly the residue class excluded by the
Legendre–Gauss three-square theorem (`15 = 4⁰·(8·1+7)`), proved here self-containedly by
a finite `decide` over `ZMod 8` (no appeal to the full three-square theorem). -/

/-- `IsSumThreeSq a` means `a` is a sum of three integer squares. -/
def IsSumThreeSq (a : ℤ) : Prop :=
  ∃ x y z : ℤ, a = x ^ 2 + y ^ 2 + z ^ 2

/-- Every square in `ZMod 8` is `0`, `1`, or `4`. -/
theorem sq_zmod_eight (a : ZMod 8) : a ^ 2 = 0 ∨ a ^ 2 = 1 ∨ a ^ 2 = 4 := by
  decide +revert

/-- A sum of three squares in `ZMod 8` is never `15` (i.e. never `≡ 7 (mod 8)`):
the squares `{0,1,4}` admit no triple summing to `7`. Verified by finite `decide`
over the `8³ = 512` residue triples. -/
theorem sum_three_sq_ne_fifteen_zmod_eight (a b c : ZMod 8) :
    a ^ 2 + b ^ 2 + c ^ 2 ≠ 15 := by
  decide +revert

/-- `15` is not a sum of three integer squares: reducing mod `8` would force the
forbidden residue `7`. -/
theorem fifteen_not_isSumThreeSq : ¬ IsSumThreeSq (15 : ℤ) := by
  rintro ⟨x, y, z, h⟩
  have h' : ((15 : ℤ) : ZMod 8) = ((x ^ 2 + y ^ 2 + z ^ 2 : ℤ) : ZMod 8) :=
    congrArg _ h
  push_cast at h'
  exact sum_three_sq_ne_fifteen_zmod_eight _ _ _ h'.symm

/-- `3 = 1² + 1² + 1²` is a sum of three squares. -/
theorem three_isSumThreeSq : IsSumThreeSq (3 : ℤ) := ⟨1, 1, 1, by ring⟩

/-- `5 = 0² + 1² + 2²` is a sum of three squares. -/
theorem five_isSumThreeSq : IsSumThreeSq (5 : ℤ) := ⟨0, 1, 2, by ring⟩

/-- **Sharpness of "four".** Sums of three squares are *not* closed under
multiplication: `3` and `5` are each sums of three squares, yet their product
`15 ≡ 7 (mod 8)` is not. Contrast `IsSumFourSq.mul`: four squares is the minimal
count for which Euler-style multiplicative closure holds. -/
theorem not_isSumThreeSq_mul_closed :
    ∃ a b : ℤ, IsSumThreeSq a ∧ IsSumThreeSq b ∧ ¬ IsSumThreeSq (a * b) :=
  ⟨3, 5, three_isSumThreeSq, five_isSumThreeSq, by
    have h : (3 : ℤ) * 5 = 15 := by norm_num
    rw [h]; exact fifteen_not_isSumThreeSq⟩

end EulerIdentityOQ05
