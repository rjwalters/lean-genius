/-
# Pythagorean Triples OQ-05: The Brahmagupta–Fibonacci two-square identity

The identity
  (a² + b²)(c² + d²) = (ac − bd)² + (ad + bc)²
shows that the set of sums of two squares is closed under multiplication.
Over ℕ this is Mathlib's `Nat.sq_add_sq_mul` (used by the sibling entry
`pythagorean-triples-oq-04`); the natural-number statement, however, cannot even
express the cross term `ac − bd`, which requires subtraction. The honest home of
the identity is therefore an arbitrary commutative *ring*, where it is a single
`ring` computation, and where its two conjugate forms both make sense.

The structural content is that the identity is exactly the multiplicativity of
the **Gaussian-integer norm** `N(a + bi) = a² + b²`. Writing a Gaussian integer
as `⟨a, b⟩ : ℤ[i] = ℤ√(-1)`, one has `N(zw) = N(z)·N(w)` (Mathlib's
`Zsqrtd.norm_mul`); unfolding `(zw).re = ac − bd` and `(zw).im = ad + bc`
recovers the Brahmagupta–Fibonacci identity on the nose. So the algebraic
identity is the "shadow" of a homomorphism `ℤ[i]ˣ → ℤˣ` between norm forms.

This entry records:
* the identity over a general commutative ring, in both forms;
* the predicate `IsSumOfTwoSquares` and its closure under multiplication
  (and the unit `1 = 1² + 0²`), exhibiting the sums of two squares as a
  multiplicative submonoid — over ℤ, unlike the ℕ-only `Nat.sq_add_sq_mul`;
* the derivation of the identity from `Zsqrtd.norm_mul`, identifying it with
  the multiplicativity of the Gaussian norm.

All proofs are elementary (`ring` and the Gaussian-integer API); zero axioms,
zero sorries.
-/

import Mathlib

namespace PythagoreanTriplesOQ05

/-! ## Part I: The identity over a commutative ring -/

variable {R : Type*} [CommRing R]

/-- **Brahmagupta–Fibonacci identity** (first form), over any commutative ring.
A product of two sums of two squares is again a sum of two squares. -/
theorem brahmagupta_fibonacci (a b c d : R) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 := by
  ring

/-- **Brahmagupta–Fibonacci identity** (second, conjugate form). Swapping the sign
of the cross terms gives the other representation `(ac + bd)² + (ad − bc)²`. -/
theorem brahmagupta_fibonacci' (a b c d : R) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 := by
  ring

/-! ## Part II: Sums of two squares form a multiplicative submonoid -/

/-- A ring element is a *sum of two squares* if it equals `a² + b²` for some `a, b`. -/
def IsSumOfTwoSquares (n : R) : Prop := ∃ a b : R, n = a ^ 2 + b ^ 2

/-- `1 = 1² + 0²` is a sum of two squares: the submonoid contains the identity. -/
theorem isSumOfTwoSquares_one : IsSumOfTwoSquares (1 : R) :=
  ⟨1, 0, by ring⟩

/-- `0 = 0² + 0²` is a sum of two squares. -/
theorem isSumOfTwoSquares_zero : IsSumOfTwoSquares (0 : R) :=
  ⟨0, 0, by ring⟩

/-- **Closure under multiplication.** The sums of two squares are closed under
products, via the Brahmagupta–Fibonacci identity — the witness for `m * n` is the
explicit pair `(ac − bd, ad + bc)`. -/
theorem IsSumOfTwoSquares.mul {m n : R}
    (hm : IsSumOfTwoSquares m) (hn : IsSumOfTwoSquares n) :
    IsSumOfTwoSquares (m * n) := by
  obtain ⟨a, b, rfl⟩ := hm
  obtain ⟨c, d, rfl⟩ := hn
  exact ⟨a * c - b * d, a * d + b * c, brahmagupta_fibonacci a b c d⟩

/-! ## Part III: The Gaussian-norm shadow

The identity is the multiplicativity of the norm `N` on the Gaussian integers
`ℤ[i] = ℤ√(-1)`, where `N⟨a, b⟩ = a² + b²`. -/

open Zsqrtd

/-- The norm of a Gaussian integer `⟨a, b⟩ = a + bi` is `a² + b²`. -/
theorem gaussianInt_norm (a b : ℤ) : (⟨a, b⟩ : GaussianInt).norm = a ^ 2 + b ^ 2 := by
  rw [Zsqrtd.norm_def]; ring

/-- The product of `⟨a, b⟩` and `⟨c, d⟩` in `ℤ[i]` is `⟨ac − bd, ad + bc⟩`. -/
theorem gaussianInt_mk_mul (a b c d : ℤ) :
    (⟨a, b⟩ : GaussianInt) * ⟨c, d⟩ = ⟨a * c - b * d, a * d + b * c⟩ := by
  ext
  · simp only [Zsqrtd.re_mul]; ring
  · simp only [Zsqrtd.im_mul]

/-- **The identity is the Gaussian norm being multiplicative.** Specialising
`Zsqrtd.norm_mul` to `z = ⟨a, b⟩`, `w = ⟨c, d⟩` in `ℤ[i]` and unfolding the norms
and the product `⟨ac − bd, ad + bc⟩` recovers the Brahmagupta–Fibonacci identity. -/
theorem brahmagupta_fibonacci_via_gaussianInt (a b c d : ℤ) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 := by
  have h := Zsqrtd.norm_mul (⟨a, b⟩ : GaussianInt) ⟨c, d⟩
  rw [gaussianInt_mk_mul, gaussianInt_norm, gaussianInt_norm, gaussianInt_norm] at h
  exact h.symm

end PythagoreanTriplesOQ05
