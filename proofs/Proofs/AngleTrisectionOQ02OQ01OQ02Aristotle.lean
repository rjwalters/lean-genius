/-
  Aristotle targets for AngleTrisectionOQ02OQ01OQ02
  Routine supporting lemmas for automated proof search.
  See AngleTrisectionOQ02OQ01OQ02.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main impossibility theorem or Galois characterization
  - Known mathematical results: polynomial degree computations, Eisenstein criterion
  - No definition sorries
  - No axioms

  Included targets (4):
  - cube_root_2_minpoly_irred: X³ - 2 is irreducible over ℚ (Eisenstein at p=2)
  - cos20_minpoly_degree: natDegree of 8X³ - 6X - 1 is 3
  - regular_7gon_poly_degree: natDegree of 8X³ + 4X² - 4X - 1 is 3
  - regular_7gon_impossible_degree: 8X³+4X²-4X-1 does not have degree 2^k

  NOT included (too complex for Aristotle):
  - not_constructible_of_bad_degree: requires tower degree theory
  - wantzel_galois_iff: requires full Galois correspondence
-/
import Mathlib

open Polynomial

namespace AngleTrisectionOQ02OQ01OQ02Aristotle

/-- A polynomial over ℚ has degree equal to a power of 2. -/
def DegreePowerOfTwo (p : ℚ[X]) : Prop :=
  ∃ k : ℕ, p.natDegree = 2 ^ k

-- Routine: x³ - 2 is irreducible over ℚ.
-- Proof: Eisenstein criterion at prime p = 2.
-- The coefficient of x³ is 1 (not divisible by 2), the coefficient of x² is 0
-- (divisible by 2), the coefficient of x is 0 (divisible by 2), and the
-- constant term is -2 (divisible by 2 but not by 4).
theorem cube_root_2_minpoly_irred : Irreducible (X ^ 3 - C 2 : ℚ[X]) := by
  sorry

-- Routine: the degree of 8X³ - 6X - 1 over ℚ is 3.
-- The leading monomial is 8X³ with nonzero coefficient 8 ≠ 0 in ℚ.
theorem cos20_minpoly_degree : (8 * X ^ 3 - 6 * X - 1 : ℚ[X]).natDegree = 3 := by
  sorry

-- Routine: the degree of 8X³ + 4X² - 4X - 1 over ℚ is 3.
-- The leading monomial is 8X³ with nonzero coefficient 8 ≠ 0 in ℚ.
-- (This is the minimal polynomial of cos(2π/7).)
theorem regular_7gon_poly_degree :
    (8 * X ^ 3 + 4 * X ^ 2 - 4 * X - 1 : ℚ[X]).natDegree = 3 := by
  sorry

-- Routine: 8X³ + 4X² - 4X - 1 does not have degree equal to a power of 2.
-- Since the degree is 3 and 3 is not a power of 2 (2^0=1, 2^1=2, 2^k≥4 for k≥2),
-- this polynomial fails the Wantzel degree criterion.
theorem regular_7gon_impossible_degree :
    ¬ DegreePowerOfTwo (8 * X ^ 3 + 4 * X ^ 2 - 4 * X - 1 : ℚ[X]) := by
  intro ⟨k, hk⟩
  rw [regular_7gon_poly_degree] at hk
  interval_cases k <;> simp_all

end AngleTrisectionOQ02OQ01OQ02Aristotle
