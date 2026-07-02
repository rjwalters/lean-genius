import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-
# Brahmagupta–Fibonacci Identity and Multiplicativity of Sums of Two Squares

## Open Question OQ-09 (parent: Fermat's Two-Square Theorem)

Fermat's theorem tells us *which primes* are sums of two squares
(`p = a² + b² ↔ p = 2 ∨ p ≡ 1 mod 4`).  Extending the characterization from primes
to composites rests on a single structural fact, flagged in the parent's open
questions:

> This requires Brahmagupta's identity `(a²+b²)(c²+d²) = (ac-bd)² + (ad+bc)²`
> and the multiplicativity of the norm in `ℤ[i]`.

This file formalizes exactly that building block: the **Brahmagupta–Fibonacci
identity** (both branches), the resulting closure of "is a sum of two squares" under
multiplication (over `ℤ` and over `ℕ`), and the conceptual source of the identity —
it *is* the multiplicativity of the Gaussian-integer norm `N(a+bi) = a²+b²`.

## Contribution

1. `brahmagupta_fibonacci` / `brahmagupta_fibonacci'` — the two-square identity and its
   sister form, over an arbitrary commutative ring (a pure `ring` identity).
2. `IsSumSq` and `IsSumSq.mul` — sums of two integer squares are closed under
   multiplication, the direct payoff of the identity.
3. `IsSumSqNat` / `isSumSqNat_iff` / `IsSumSqNat.mul` — the classical `ℕ` statement,
   bridged to the `ℤ` version through `Int.natAbs` (a natural number is a sum of two
   natural squares iff it is a sum of two integer squares).
4. `gaussianInt_norm_eq`, `isSumSq_iff_gaussianNorm`, `IsSumSq.mul'` — the identity
   read as norm multiplicativity in `ℤ[i]`: `IsSumSq n ↔ ∃ z : ℤ[i], N z = n`, and the
   *same* closure re-derived from `Zsqrtd.norm_mul`.  This exhibits Brahmagupta's
   identity as the coordinate form of `N(zw) = N(z)·N(w)`.

## Mathematical Context

Writing `a² + b² = N(a + bi)` for the Gaussian norm, the identity
`(a²+b²)(c²+d²) = (ac-bd)² + (ad+bc)²` is precisely `N(z)N(w) = N(zw)` with
`z = a+bi`, `w = c+di`, since `zw = (ac-bd) + (ad+bc)i`.  The sister branch comes from
using `w̄ = c-di` instead.  Multiplicativity of the norm is what powers the composite
characterization of sums of two squares and, via unique factorization in `ℤ[i]`, the
uniqueness of prime representations.

## Axioms: 0 | Sorries: 0
-/

namespace FermatTwoSquaresOQ09

/-! ### The Brahmagupta–Fibonacci identity -/

/-- **Brahmagupta–Fibonacci identity.**  In any commutative ring,
    `(a² + b²)(c² + d²) = (ac - bd)² + (ad + bc)²`.  A product of two sums of two
    squares is again a sum of two squares. -/
theorem brahmagupta_fibonacci {R : Type*} [CommRing R] (a b c d : R) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 := by
  ring

/-- **Sister form** of the identity, obtained by conjugating the second factor
    (`d ↦ -d`): `(a² + b²)(c² + d²) = (ac + bd)² + (ad - bc)²`.  The two branches
    give the (generically) two distinct representations of the product. -/
theorem brahmagupta_fibonacci' {R : Type*} [CommRing R] (a b c d : R) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 := by
  ring

/-! ### Closure over the integers -/

/-- `n` is a sum of two integer squares. -/
def IsSumSq (n : ℤ) : Prop := ∃ a b : ℤ, n = a ^ 2 + b ^ 2

/-- The set of sums of two integer squares is closed under multiplication — the direct
    consequence of the Brahmagupta–Fibonacci identity. -/
theorem IsSumSq.mul {m n : ℤ} (hm : IsSumSq m) (hn : IsSumSq n) : IsSumSq (m * n) := by
  obtain ⟨a, b, rfl⟩ := hm
  obtain ⟨c, d, rfl⟩ := hn
  exact ⟨a * c - b * d, a * d + b * c, brahmagupta_fibonacci a b c d⟩

/-- `1 = 1² + 0²` is a sum of two squares, so the sums of two squares form a
    multiplicative submonoid of `ℤ`. -/
theorem IsSumSq.one : IsSumSq 1 := ⟨1, 0, by ring⟩

/-! ### The classical statement over the naturals -/

/-- `n : ℕ` is a sum of two natural squares. -/
def IsSumSqNat (n : ℕ) : Prop := ∃ a b : ℕ, n = a ^ 2 + b ^ 2

/-- A natural number is a sum of two natural squares iff, viewed in `ℤ`, it is a sum of
    two integer squares.  (Signs are immaterial: `a² = (|a|)²`.) -/
theorem isSumSqNat_iff (n : ℕ) : IsSumSqNat n ↔ IsSumSq (n : ℤ) := by
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, by push_cast; ring⟩
  · rintro ⟨a, b, h⟩
    refine ⟨a.natAbs, b.natAbs, ?_⟩
    have : (n : ℤ) = (a.natAbs : ℤ) ^ 2 + (b.natAbs : ℤ) ^ 2 := by
      rw [h, Int.natCast_natAbs, Int.natCast_natAbs, sq_abs, sq_abs]
    exact_mod_cast this

/-- Sums of two *natural* squares are closed under multiplication — the classical
    number-theoretic statement, reduced to the integer version. -/
theorem IsSumSqNat.mul {m n : ℕ} (hm : IsSumSqNat m) (hn : IsSumSqNat n) :
    IsSumSqNat (m * n) := by
  rw [isSumSqNat_iff] at hm hn ⊢
  push_cast
  exact hm.mul hn

/-! ### The Gaussian-integer norm interpretation -/

/-- The Gaussian norm of `z = re + im·i` is `re² + im²`.  (`GaussianInt` is
    `Zsqrtd (-1)`, so `Zsqrtd.norm_def` gives `re·re - (-1)·im·im`.) -/
theorem gaussianInt_norm_eq (z : GaussianInt) :
    Zsqrtd.norm z = z.re ^ 2 + z.im ^ 2 := by
  rw [Zsqrtd.norm_def]; ring

/-- `n` is a sum of two integer squares iff it is the norm of a Gaussian integer. -/
theorem isSumSq_iff_gaussianNorm (n : ℤ) :
    IsSumSq n ↔ ∃ z : GaussianInt, Zsqrtd.norm z = n := by
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨⟨a, b⟩, by rw [gaussianInt_norm_eq]⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z.re, z.im, (gaussianInt_norm_eq z)⟩

/-- Closure under multiplication, re-derived as multiplicativity of the Gaussian norm
    `N(zw) = N(z)·N(w)` (`Zsqrtd.norm_mul`).  This exhibits Brahmagupta's identity as
    the coordinate expression of a ring homomorphism property. -/
theorem IsSumSq.mul' {m n : ℤ} (hm : IsSumSq m) (hn : IsSumSq n) : IsSumSq (m * n) := by
  rw [isSumSq_iff_gaussianNorm] at hm hn ⊢
  obtain ⟨z, rfl⟩ := hm
  obtain ⟨w, rfl⟩ := hn
  exact ⟨z * w, Zsqrtd.norm_mul z w⟩

/-! ### Concrete verifications -/

/-- `5 = 1² + 2²`, `13 = 2² + 3²`, and their product `65 = 1² + 8² = 4² + 7²`,
    the two branches of the identity. -/
example : (5 : ℤ) * 13 = (1 * 2 - 2 * 3) ^ 2 + (1 * 3 + 2 * 2) ^ 2 := by decide
example : (5 : ℤ) * 13 = (1 * 2 + 2 * 3) ^ 2 + (1 * 3 - 2 * 2) ^ 2 := by decide
/-- `65` is genuinely a sum of two squares in two ways. -/
example : (65 : ℤ) = 1 ^ 2 + 8 ^ 2 := by decide
example : (65 : ℤ) = 4 ^ 2 + 7 ^ 2 := by decide

end FermatTwoSquaresOQ09
