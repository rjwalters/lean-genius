/-
  Cauchy–Schwarz for finite sums from a sum-of-squares argument.

  The `sqrt2-examples` family isolates the single fact `0 ≤ x²` (`sq_nonneg`,
  the parent's `square_nonneg_general`) and traces its consequences.  Its parent
  entry `sqrt2-examples-oq-01` asks, as its third open question, whether the
  Cauchy–Schwarz inequality

      (∑ᵢ aᵢ bᵢ)²  ≤  (∑ᵢ aᵢ²)(∑ᵢ bᵢ²)

  can be obtained *directly* from square-positivity for finite sums in a
  linearly ordered field.  This file answers that: yes, and via an exact
  identity strictly stronger than the inequality — the **Lagrange identity**

      2·[(∑ᵢ aᵢ²)(∑ⱼ bⱼ²) − (∑ᵢ aᵢ bᵢ)²]  =  ∑ᵢ ∑ⱼ (aᵢ bⱼ − aⱼ bᵢ)².

  The right-hand side is a sum of squares, hence `≥ 0` by `sq_nonneg` applied
  termwise, and Cauchy–Schwarz drops out by dividing by the positive constant 2.
  The identity holds over any commutative ring; only the final inequality needs
  the order.  Nothing here uses Mathlib's `Finset.sum_mul_sq_le_sq_mul_sq`; the
  whole point is to expose the sum-of-squares certificate — the antisymmetric
  Gram determinants `aᵢ bⱼ − aⱼ bᵢ` — that makes the inequality true.

  Everything is 0-axiom.  (Order hypotheses are written in the current unbundled
  Mathlib spelling `[Field α] [LinearOrder α] [IsStrictOrderedRing α]`, the
  replacement for the former `LinearOrderedField`.)
-/
import Mathlib

open scoped BigOperators
open Finset

namespace Sqrt2OQ01OQ03

variable {ι : Type*}

/-- The family's guiding fact, stated locally: a square is non-negative in any
linearly ordered ring.  (This is `sq_nonneg`; the parent entry names it
`square_nonneg_general`.) -/
theorem square_nonneg_general {α : Type*} [Ring α] [LinearOrder α]
    [IsStrictOrderedRing α] (x : α) : 0 ≤ x ^ 2 := sq_nonneg x

/-- **Lagrange's identity** (doubled form), over an arbitrary commutative ring.
The difference `(∑ aᵢ²)(∑ bⱼ²) − (∑ aᵢ bᵢ)²`, doubled, is the sum over all pairs
`(i, j)` of the squares of the `2×2` "cross" determinants `aᵢ bⱼ − aⱼ bᵢ`.
This is the algebraic heart of Cauchy–Schwarz: the defect is *literally* a sum
of squares. -/
theorem two_mul_lagrange {α : Type*} [CommRing α] (s : Finset ι) (a b : ι → α) :
    2 * ((∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) - (∑ i ∈ s, a i * b i) ^ 2)
      = ∑ i ∈ s, ∑ j ∈ s, (a i * b j - a j * b i) ^ 2 := by
  have e : ∀ i j : ι, (a i * b j - a j * b i) ^ 2
      = a i ^ 2 * b j ^ 2 + a j ^ 2 * b i ^ 2 - 2 * ((a i * b i) * (a j * b j)) :=
    fun i j => by ring
  have h1 : ∑ i ∈ s, ∑ j ∈ s, a i ^ 2 * b j ^ 2
      = (∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) := (sum_mul_sum s s _ _).symm
  have h2 : ∑ i ∈ s, ∑ j ∈ s, a j ^ 2 * b i ^ 2
      = (∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) := by
    rw [Finset.sum_comm]; exact (sum_mul_sum s s _ _).symm
  have h3 : ∑ i ∈ s, ∑ j ∈ s, 2 * ((a i * b i) * (a j * b j))
      = 2 * (∑ i ∈ s, a i * b i) ^ 2 := by
    rw [sq, sum_mul_sum s s _ _, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  symm
  calc ∑ i ∈ s, ∑ j ∈ s, (a i * b j - a j * b i) ^ 2
      = ∑ i ∈ s, ∑ j ∈ s,
          (a i ^ 2 * b j ^ 2 + a j ^ 2 * b i ^ 2 - 2 * ((a i * b i) * (a j * b j))) :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => e i j))
    _ = (∑ i ∈ s, ∑ j ∈ s, a i ^ 2 * b j ^ 2)
          + (∑ i ∈ s, ∑ j ∈ s, a j ^ 2 * b i ^ 2)
          - (∑ i ∈ s, ∑ j ∈ s, 2 * ((a i * b i) * (a j * b j))) := by
        simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = 2 * ((∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) - (∑ i ∈ s, a i * b i) ^ 2) := by
        rw [h1, h2, h3]; ring

/-- The doubled Cauchy–Schwarz defect is non-negative in a linearly ordered
field: it is a sum of squares, each `≥ 0` by `square_nonneg_general`. -/
theorem two_mul_defect_nonneg {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] (s : Finset ι) (a b : ι → α) :
    0 ≤ 2 * ((∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) - (∑ i ∈ s, a i * b i) ^ 2) := by
  rw [two_mul_lagrange]
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => square_nonneg_general _

/-- **Cauchy–Schwarz inequality** for finite sums in a linearly ordered field,
proved from the sum-of-squares Lagrange identity: dividing the non-negative
doubled defect by `2 > 0` gives `(∑ aᵢ bᵢ)² ≤ (∑ aᵢ²)(∑ bᵢ²)`. -/
theorem inner_sq_le_sum_sq_mul_sum_sq {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] (s : Finset ι) (a b : ι → α) :
    (∑ i ∈ s, a i * b i) ^ 2 ≤ (∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) := by
  have h := two_mul_defect_nonneg s a b
  linarith

/-- The defect `(∑ aᵢ²)(∑ bᵢ²) − (∑ aᵢ bᵢ)²` is itself non-negative — the same
statement rearranged. -/
theorem sum_sq_mul_sum_sq_sub_inner_sq_nonneg {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] (s : Finset ι) (a b : ι → α) :
    0 ≤ (∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) - (∑ i ∈ s, a i * b i) ^ 2 := by
  have := inner_sq_le_sum_sq_mul_sum_sq s a b
  linarith

/-- **Absolute-value form.** Since `|x|² = x²`, the squared Cauchy–Schwarz
inequality is unchanged by taking the absolute value of the inner sum:
`|∑ aᵢ bᵢ|² ≤ (∑ aᵢ²)(∑ bᵢ²)`. -/
theorem abs_inner_sq_le {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] (s : Finset ι) (a b : ι → α) :
    |∑ i ∈ s, a i * b i| ^ 2 ≤ (∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) := by
  rw [sq_abs]
  exact inner_sq_le_sum_sq_mul_sum_sq s a b

end Sqrt2OQ01OQ03

/-!
### Concrete specialisations

The inequality holds verbatim over `ℚ` and `ℝ`; and the parent's `x ↦ x²`
motivation reappears as the two-term case `n = 2`, where the cross determinant is
the single quantity `a₁ b₂ − a₂ b₁` and Lagrange's identity reads
`(a₁² + a₂²)(b₁² + b₂²) − (a₁ b₁ + a₂ b₂)² = (a₁ b₂ − a₂ b₁)²`.
-/

namespace Sqrt2OQ01OQ03

/-- Cauchy–Schwarz over the rationals. -/
theorem cauchy_schwarz_rat (s : Finset ι) (a b : ι → ℚ) :
    (∑ i ∈ s, a i * b i) ^ 2 ≤ (∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) :=
  inner_sq_le_sum_sq_mul_sum_sq s a b

/-- Cauchy–Schwarz over the reals. -/
theorem cauchy_schwarz_real (s : Finset ι) (a b : ι → ℝ) :
    (∑ i ∈ s, a i * b i) ^ 2 ≤ (∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) :=
  inner_sq_le_sum_sq_mul_sum_sq s a b

/-- The two-variable Lagrange identity, the `n = 2` shadow of `two_mul_lagrange`
and the exact source of the classical `(a₁² + a₂²)(b₁² + b₂²) ≥ (a₁ b₁ + a₂ b₂)²`. -/
theorem lagrange_two {α : Type*} [CommRing α] (a₁ a₂ b₁ b₂ : α) :
    (a₁ ^ 2 + a₂ ^ 2) * (b₁ ^ 2 + b₂ ^ 2) - (a₁ * b₁ + a₂ * b₂) ^ 2
      = (a₁ * b₂ - a₂ * b₁) ^ 2 := by
  ring

end Sqrt2OQ01OQ03
