import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic

/-!
# Pythagorean triples via the Gaussian-integer norm (pythagorean-theorem-oq-04)

## What this proves

The `(m, n)`-parameterization of Pythagorean triples is *exactly* the statement that
squaring in the Gaussian integers `ℤ[i]` produces triples, and that the multiplicative
norm `N(a + bi) = a² + b²` turns Pythagoras' equation `x² + y² = z²` into
`N(x + yi) = z²`.

Two layers:

* **Soundness (norm route).** For every Gaussian integer `g = m + ni`,
  `g² = (m² - n²) + (2mn)i`, and because the norm is multiplicative,
  `N(g²) = N(g)² = (m² + n²)²`. Reading off real/imaginary parts gives
  `(m² - n²)² + (2mn)² = (m² + n²)²`, i.e. `(m² - n², 2mn, m² + n²)` is a
  Pythagorean triple. This is the Brahmagupta–Fibonacci identity *as* norm
  multiplicativity, not as a brute `ring` identity.

* **Completeness (Gaussian factorization).** Conversely, every *primitive*
  Pythagorean triple `(x, y, z)` with `x` odd and `z > 0` is the square of a
  Gaussian integer: there exist coprime `m, n` with
  `(x + yi) = (m + ni)²` in `ℤ[i]` and `z = N(m + ni)`. So the parameterization is
  not just a source of triples — it captures *all* primitive triples, and the
  hypotenuse is literally the Gaussian norm of the generating integer.

## Relation to the existing gallery entry

`PythagoreanTriples.lean` derives the same parameterization from the *rational
parametrization of the unit circle* (Mathlib's `coprime_classification`). This file
gives the orthogonal, algebraic-number-theory viewpoint: the parameterization is the
arithmetic of `ℤ[i]`. The completeness theorem `gaussian_completeness` is proved by
transporting Mathlib's classification through the identity `gaussianInt_sq`.

## Status

- [x] Complete proof, no sorries
- [x] 0 `axiom` declarations, no structure-encoded assumptions
- [x] Soundness derived from norm multiplicativity (`Zsqrtd.norm_mul`)
- [x] Completeness: primitive triples are Gaussian squares
-/

namespace PythagoreanTheoremOQ04

open Zsqrtd

local notation "ℤ[i]" => GaussianInt

/-! ## The Gaussian-integer norm and squaring -/

/-- The norm of a Gaussian integer is the sum of squares of its components:
`N(m + ni) = m² + n²`. -/
theorem gaussianInt_norm (m n : ℤ) :
    (⟨m, n⟩ : ℤ[i]).norm = m * m + n * n := by
  simp [Zsqrtd.norm_def]

/-- Squaring in `ℤ[i]` realizes the parameterization map:
`(m + ni)² = (m² - n²) + (2mn)i`. -/
theorem gaussianInt_sq (m n : ℤ) :
    (⟨m, n⟩ : ℤ[i]) ^ 2 = ⟨m * m - n * n, 2 * m * n⟩ := by
  rw [sq]
  apply Zsqrtd.ext <;> simp <;> ring

/-- The norm of the square equals the square of the norm — multiplicativity applied to
`g²`. This is the engine behind the Pythagorean identity. -/
theorem norm_gaussianInt_sq (m n : ℤ) :
    ((⟨m, n⟩ : ℤ[i]) ^ 2).norm = (m * m + n * n) ^ 2 := by
  rw [sq, Zsqrtd.norm_mul, gaussianInt_norm, ← sq]

/-! ## Soundness: the parameterization yields triples (via norm multiplicativity) -/

/-- The Brahmagupta–Fibonacci identity, obtained from the multiplicativity of the
Gaussian norm rather than by direct expansion:
`(m² - n²)² + (2mn)² = (m² + n²)²`. -/
theorem param_norm_identity (m n : ℤ) :
    (m * m - n * n) * (m * m - n * n) + (2 * m * n) * (2 * m * n)
      = (m * m + n * n) * (m * m + n * n) := by
  -- LHS is `N((m+ni)²)` read off coordinates; RHS is `N(m+ni)²`.
  have hcoord : ((⟨m, n⟩ : ℤ[i]) ^ 2).norm
      = (m * m - n * n) * (m * m - n * n) + (2 * m * n) * (2 * m * n) := by
    rw [gaussianInt_sq]; simp [Zsqrtd.norm_def]
  have hmul : ((⟨m, n⟩ : ℤ[i]) ^ 2).norm = (m * m + n * n) * (m * m + n * n) := by
    rw [norm_gaussianInt_sq]; ring
  rw [hcoord] at hmul
  exact hmul

/-- The parameterized triple `(m² - n², 2mn, m² + n²)` is a Pythagorean triple.
The proof routes through the Gaussian-norm identity `param_norm_identity`. -/
theorem param_is_triple (m n : ℤ) :
    PythagoreanTriple (m ^ 2 - n ^ 2) (2 * m * n) (m ^ 2 + n ^ 2) := by
  -- The triple identity is exactly `param_norm_identity`, itself derived from
  -- norm multiplicativity; feed it to `PythagoreanTriple` via `linear_combination`.
  unfold PythagoreanTriple
  linear_combination param_norm_identity m n

/-! ## Completeness: every primitive triple is a Gaussian square -/

/-- **Completeness via Gaussian integers.** A primitive Pythagorean triple `(x, y, z)`
with `x` odd and `z > 0` is the square of a Gaussian integer: there are coprime `m, n`
with `(x + yi) = (m + ni)²` in `ℤ[i]`, and the hypotenuse is the Gaussian norm
`z = N(m + ni) = m² + n²`.

This shows the `(m, n)`-parameterization is *complete*: it is not merely one way to
manufacture triples, every primitive triple arises this way, and does so as an honest
factorization in `ℤ[i]`. -/
theorem gaussian_completeness {x y z : ℤ} (h : PythagoreanTriple x y z)
    (hco : Int.gcd x y = 1) (hodd : x % 2 = 1) (hpos : 0 < z) :
    ∃ m n : ℤ,
      (⟨x, y⟩ : ℤ[i]) = (⟨m, n⟩ : ℤ[i]) ^ 2 ∧
        z = (⟨m, n⟩ : ℤ[i]).norm ∧
        Int.gcd m n = 1 := by
  obtain ⟨m, n, hx, hy, hz, hmn, _, _⟩ := h.coprime_classification' hco hodd hpos
  refine ⟨m, n, ?_, ?_, hmn⟩
  · -- (x + yi) = (m + ni)²
    rw [gaussianInt_sq]
    apply Zsqrtd.ext
    · simp [hx]; ring
    · simp [hy]
  · -- z = N(m + ni)
    rw [gaussianInt_norm, hz]; ring

/-! ## Worked examples -/

/-- `(3, 4, 5)` from `m = 2, n = 1`: `(2 + i)² = 3 + 4i`, `N(2 + i) = 5`. -/
example : (⟨2, 1⟩ : ℤ[i]) ^ 2 = ⟨3, 4⟩ := by
  rw [gaussianInt_sq]; norm_num

example : (⟨2, 1⟩ : ℤ[i]).norm = 5 := by
  rw [gaussianInt_norm]; norm_num

/-- `(5, 12, 13)` from `m = 3, n = 2`: `(3 + 2i)² = 5 + 12i`, `N(3 + 2i) = 13`. -/
example : (⟨3, 2⟩ : ℤ[i]) ^ 2 = ⟨5, 12⟩ := by
  rw [gaussianInt_sq]; norm_num

example : (⟨3, 2⟩ : ℤ[i]).norm = 13 := by
  rw [gaussianInt_norm]; norm_num

/-- The `(3,4,5)` triple, derived through `param_is_triple` (`m = 2, n = 1`). -/
example : PythagoreanTriple 3 4 5 := by
  have := param_is_triple 2 1
  norm_num at this
  exact this

end PythagoreanTheoremOQ04
