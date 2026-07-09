/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9f346174-4581-4d17-be96-26ce5913bece

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem coprime_not_both_even {m n : ℕ} (h : Nat.Coprime m n) :
    ¬(Even m ∧ Even n)

- theorem both_odd_even_diff {m n : ℕ} (hm : Odd m) (hn : Odd n) (hle : n ≤ m) :
    ¬Odd (m - n)

- theorem diff_parity_odd_diff {m n : ℕ} (hle : n ≤ m)
    (h : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n)) :
    Odd (m - n)

- theorem coprime_parity_cases {m n : ℕ} (hcop : Nat.Coprime m n) :
    (Even m ∧ Odd n) ∨ (Odd m ∧ Even n) ∨ (Odd m ∧ Odd n)

- theorem density_factors_product :
    (π / 8 : ℝ) * (6 / π ^ 2) * (2 / 3) = 1 / (2 * π)

- theorem density_algebra (N : ℝ) (hN : 0 < N) :
    π * N / 8 * (6 / π ^ 2) * (2 / 3) = N / (2 * π)

- theorem tripleDensityConstant_pos : 0 < (1 : ℝ) / (2 * π)

- theorem parametric_triple (m n : ℤ) :
    PythagoreanTriple (m ^ 2 - n ^ 2) (2 * m * n) (m ^ 2 + n ^ 2)

- theorem coprime_triple_classified {x y z : ℤ}
    (h : PythagoreanTriple x y z) (hcop : Int.gcd x y = 1) :
    h.IsPrimitiveClassified

- theorem triple_classified {x y z : ℤ}
    (h : PythagoreanTriple x y z) :
    h.IsClassified

- theorem even_odd_of_coprime {x y z : ℤ}
    (h : PythagoreanTriple x y z) (hcoprime : Int.gcd x y = 1) :
    (x % 2 = 0 ∧ y % 2 = 1) ∨ (x % 2 = 1 ∧ y % 2 = 0)

- theorem count_div_nonneg (a b : ℕ) :
    0 ≤ (a : ℝ) / (b : ℝ)
-/

/-
  Aristotle targets for Pythagorean Triples Density (OQ-01)
  Routine supporting lemmas for automated proof search.
  See PythagoreanTriplesOQ01.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture or density axioms
  - Known results likely in Mathlib (monotonicity, cardinality, bounds, etc.)
  - Clean theorem statements with no definition sorries
  - No axioms (use theorem ... := by sorry instead)
-/
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic


open Finset Filter Real Topology

namespace PythagoreanTriplesOQ01Aristotle

/-
## Coprimality and Parity Lemmas
-/

/-- Coprime integers cannot both be even. -/
theorem coprime_not_both_even {m n : ℕ} (h : Nat.Coprime m n) :
    ¬(Even m ∧ Even n) := by
      exact fun h' => by have := Nat.dvd_gcd ( even_iff_two_dvd.mp h'.1 ) ( even_iff_two_dvd.mp h'.2 ) ; aesop;

/-- Both-odd coprime pairs have even difference (not primitive). -/
theorem both_odd_even_diff {m n : ℕ} (hm : Odd m) (hn : Odd n) (hle : n ≤ m) :
    ¬Odd (m - n) := by
      grind

/-- Different parity implies odd difference. -/
theorem diff_parity_odd_diff {m n : ℕ} (hle : n ≤ m)
    (h : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n)) :
    Odd (m - n) := by
      grind +ring

/-- For coprime pairs: exactly 3 parity combinations are possible (not both-even).
Of these, 2 give odd difference (primitive) and 1 gives even difference. -/
theorem coprime_parity_cases {m n : ℕ} (hcop : Nat.Coprime m n) :
    (Even m ∧ Odd n) ∨ (Odd m ∧ Even n) ∨ (Odd m ∧ Odd n) := by
      rcases Nat.even_or_odd' m with ⟨ m, rfl | rfl ⟩ <;> rcases Nat.even_or_odd' n with ⟨ n, rfl | rfl ⟩ <;> simp_all +decide [ Nat.Coprime ];
      norm_num [ Nat.gcd_mul_left ] at hcop

/-
## Density Algebra
-/

/-- The key algebraic identity: the three density factors multiply to 1/(2π). -/
theorem density_factors_product :
    (π / 8 : ℝ) * (6 / π ^ 2) * (2 / 3) = 1 / (2 * π) := by
      -- Simplify the expression by cancelling out common terms.
      field_simp
      ring

/-- Equivalent form with N. -/
theorem density_algebra (N : ℝ) (hN : 0 < N) :
    π * N / 8 * (6 / π ^ 2) * (2 / 3) = N / (2 * π) := by
      -- Combine and simplify the fractions.
      field_simp
      ring

/-- The density constant 1/(2π) is positive. -/
theorem tripleDensityConstant_pos : 0 < (1 : ℝ) / (2 * π) := by
  positivity

/-
## Parametrization Properties
-/

/-- The parametric formula always produces a Pythagorean triple. -/
theorem parametric_triple (m n : ℤ) :
    PythagoreanTriple (m ^ 2 - n ^ 2) (2 * m * n) (m ^ 2 + n ^ 2) := by
      -- By expanding and simplifying, we can directly verify the identity.
      simp [PythagoreanTriple] at *; ring;

/-- Every coprime Pythagorean triple is primitively classified. -/
theorem coprime_triple_classified {x y z : ℤ}
    (h : PythagoreanTriple x y z) (hcop : Int.gcd x y = 1) :
    h.IsPrimitiveClassified :=
  h.isPrimitiveClassified_of_coprime hcop

/-- Every Pythagorean triple is classified. -/
theorem triple_classified {x y z : ℤ}
    (h : PythagoreanTriple x y z) :
    h.IsClassified :=
  h.classified

/-- In a primitive triple, one leg is even and one is odd. -/
theorem even_odd_of_coprime {x y z : ℤ}
    (h : PythagoreanTriple x y z) (hcoprime : Int.gcd x y = 1) :
    (x % 2 = 0 ∧ y % 2 = 1) ∨ (x % 2 = 1 ∧ y % 2 = 0) := by
      cases Int.emod_two_eq_zero_or_one x <;> cases Int.emod_two_eq_zero_or_one y <;> cases Int.emod_two_eq_zero_or_one z <;> have := Int.emod_nonneg y two_ne_zero <;> have := Int.emod_nonneg z two_ne_zero <;> simp_all +decide only [PythagoreanTriple];
      · exact absurd ( Int.dvd_coe_gcd ( Int.dvd_of_emod_eq_zero ‹x % 2 = 0› ) ( Int.dvd_of_emod_eq_zero ‹y % 2 = 0› ) ) ( by norm_num [ hcoprime ] );
      · exact absurd ( Int.dvd_coe_gcd ( Int.dvd_of_emod_eq_zero ‹x % 2 = 0› ) ( Int.dvd_of_emod_eq_zero ‹y % 2 = 0› ) ) ( by norm_num [ hcoprime ] );
      · exact absurd ( congr_arg ( · % 4 ) h ) ( by rcases Int.even_or_odd' x with ⟨ k, rfl | rfl ⟩ <;> rcases Int.even_or_odd' y with ⟨ l, rfl | rfl ⟩ <;> rcases Int.even_or_odd' z with ⟨ m, rfl | rfl ⟩ <;> ring_nf <;> norm_num [ Int.add_emod, Int.mul_emod ] at * );
      · exact absurd ( congr_arg ( · % 4 ) h ) ( by rcases Int.even_or_odd' x with ⟨ k, rfl | rfl ⟩ <;> rcases Int.even_or_odd' y with ⟨ l, rfl | rfl ⟩ <;> rcases Int.even_or_odd' z with ⟨ m, rfl | rfl ⟩ <;> ring_nf <;> norm_num [ Int.add_emod, Int.mul_emod ] at * )

/-
## Ratio Non-negativity
-/

/-- Division of natural casts is non-negative. -/
theorem count_div_nonneg (a b : ℕ) :
    0 ≤ (a : ℝ) / (b : ℝ) := by
      positivity

end PythagoreanTriplesOQ01Aristotle