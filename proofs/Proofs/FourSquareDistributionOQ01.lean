import Proofs.FourSquareDistribution
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

/-
# Jacobi's Four-Square Formula (OQ-01 of FourSquareDistribution)

## Open Question (Gallery OQ-01 of `four-square-distribution`)
"Can Jacobi's four-square formula r₄(n) = 8·∑_{4∤d|n} d be formally
proved in Lean 4?"

## What This Provides

This file is the **OBSERVE/ORIENT contribution** for OQ-01:

1. Defines Jacobi's modified divisor sum σ*(n) := Σ_{d|n, 4∤d} d.
2. Defines the brute-force enumeration r₄(n) over signed integer 4-tuples.
3. Proves the conjecture *numerically* for n = 1..10 via `native_decide`.
4. States Jacobi's formula as `axiom jacobi_r4_formula` — the precise open
   target whose general proof requires modular form theory.
5. Connects the small-case verification to the type-decomposition results
   in `FourSquareDistribution.lean` so that the same numerical content is
   independently checkable from two different combinatorial definitions.

## Mathematical Background

For each n ≥ 1, define
$$
  r_4(n) = \#\{(a,b,c,d) \in \mathbb{Z}^4 : a^2+b^2+c^2+d^2 = n\}
$$
$$
  \sigma^*(n) = \sum_{\substack{d \mid n \\ 4 \nmid d}} d.
$$
**Jacobi (1834)**: r₄(n) = 8·σ*(n) for all n ≥ 1.

The classical proof uses θ(q)⁴ where θ(q) = ∑_{k∈ℤ} q^{k²}. Jacobi shows
θ(q)⁴ is a weight-2 modular form of level 4 and identifies its
q-expansion with 1 + 8∑_{n≥1} σ*(n) q^n.

Mathlib infrastructure already present (as of 4.26.0, 2026-05):
* `Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable` — defines
  `jacobiTheta` on the upper half-plane, with the modular transformations
  `jacobiTheta_T_sq_smul` and `jacobiTheta_S_smul`.
* `Mathlib.NumberTheory.ModularForms.EisensteinSeries.*` — defines the
  Eisenstein series with bounded-at-cusp / modular invariance lemmas.
* `Mathlib.NumberTheory.SumFourSquares` — Lagrange's existence theorem.

What is **missing** for a full Lean proof:
* Fourier coefficients / q-expansion of `jacobiTheta`.
* Identification of `jacobiTheta^4` with a specific Eisenstein-series
  combination (e.g. E₂(τ) - 4·E₂(4τ), up to normalization).
* The arithmetic identity expressing the n-th Fourier coefficient as
  8·σ*(n).

## File Status
* axioms: 1 (`jacobi_r4_formula`)
* sorries: 0
* numerically verified: n = 1..10
-/

namespace FourSquareDistributionOQ01

open Finset Nat

-- =====================================================================
-- PART 1: Jacobi's modified divisor sum σ*(n)
-- =====================================================================

/-- Jacobi's modified divisor sum: σ*(n) = Σ_{d|n, 4∤d} d.

    Drops every divisor of n that is divisible by 4. The factor of 8
    in Jacobi's r₄ formula relates to this via 8 = 2³ and the
    sign/permutation symmetry group acting on a 4-tuple. -/
def sigmaStar (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, if 4 ∣ d then 0 else d

-- σ*(n) values for n = 1..10:
theorem sigmaStar_1  : sigmaStar 1  = 1  := by native_decide
theorem sigmaStar_2  : sigmaStar 2  = 3  := by native_decide
theorem sigmaStar_3  : sigmaStar 3  = 4  := by native_decide
theorem sigmaStar_4  : sigmaStar 4  = 3  := by native_decide
theorem sigmaStar_5  : sigmaStar 5  = 6  := by native_decide
theorem sigmaStar_6  : sigmaStar 6  = 12 := by native_decide
theorem sigmaStar_7  : sigmaStar 7  = 8  := by native_decide
theorem sigmaStar_8  : sigmaStar 8  = 3  := by native_decide
theorem sigmaStar_9  : sigmaStar 9  = 13 := by native_decide
theorem sigmaStar_10 : sigmaStar 10 = 18 := by native_decide

/-- Jacobi's prediction: r₄(n) = 8·σ*(n). -/
def jacobiR4 (n : ℕ) : ℕ := 8 * sigmaStar n

theorem jacobiR4_1  : jacobiR4 1  = 8   := by native_decide
theorem jacobiR4_2  : jacobiR4 2  = 24  := by native_decide
theorem jacobiR4_3  : jacobiR4 3  = 32  := by native_decide
theorem jacobiR4_4  : jacobiR4 4  = 24  := by native_decide
theorem jacobiR4_5  : jacobiR4 5  = 48  := by native_decide
theorem jacobiR4_6  : jacobiR4 6  = 96  := by native_decide
theorem jacobiR4_7  : jacobiR4 7  = 64  := by native_decide
theorem jacobiR4_8  : jacobiR4 8  = 24  := by native_decide
theorem jacobiR4_9  : jacobiR4 9  = 104 := by native_decide
theorem jacobiR4_10 : jacobiR4 10 = 144 := by native_decide

-- =====================================================================
-- PART 2: Brute-force enumeration of integer 4-tuples
-- =====================================================================

/-- Bound a tuple component to [-n, n] via offset by n. -/
def shiftedRange (n : ℕ) : List ℤ :=
  (List.range (2 * n + 1)).map (fun k => (k : ℤ) - n)

/-- Brute-force count of integer 4-tuples (a, b, c, d) ∈ ℤ⁴ with
    a² + b² + c² + d² = n.

    Since a² ≤ n implies |a| ≤ √n ≤ n, enumerating each component over
    [-n, n] is correct (over-counts the bound but stays correct). -/
def r4Count (n : ℕ) : ℕ :=
  let R := shiftedRange n
  R.foldl (fun acc a =>
    R.foldl (fun acc b =>
      R.foldl (fun acc c =>
        R.foldl (fun acc d =>
          if a^2 + b^2 + c^2 + d^2 = (n : ℤ) then acc + 1 else acc)
          acc) acc) acc) 0

-- =====================================================================
-- PART 3: Numerical verification of Jacobi's formula for n = 1..10
-- =====================================================================

theorem r4Count_1  : r4Count 1  = 8   := by native_decide
theorem r4Count_2  : r4Count 2  = 24  := by native_decide
theorem r4Count_3  : r4Count 3  = 32  := by native_decide
theorem r4Count_4  : r4Count 4  = 24  := by native_decide
theorem r4Count_5  : r4Count 5  = 48  := by native_decide
theorem r4Count_6  : r4Count 6  = 96  := by native_decide
theorem r4Count_7  : r4Count 7  = 64  := by native_decide
theorem r4Count_8  : r4Count 8  = 24  := by native_decide
theorem r4Count_9  : r4Count 9  = 104 := by native_decide
theorem r4Count_10 : r4Count 10 = 144 := by native_decide

/-- The brute-force count agrees with Jacobi's prediction r₄(n) = 8 σ*(n)
    for n = 1..10. -/
theorem jacobi_holds_1  : r4Count 1  = jacobiR4 1  := by native_decide
theorem jacobi_holds_2  : r4Count 2  = jacobiR4 2  := by native_decide
theorem jacobi_holds_3  : r4Count 3  = jacobiR4 3  := by native_decide
theorem jacobi_holds_4  : r4Count 4  = jacobiR4 4  := by native_decide
theorem jacobi_holds_5  : r4Count 5  = jacobiR4 5  := by native_decide
theorem jacobi_holds_6  : r4Count 6  = jacobiR4 6  := by native_decide
theorem jacobi_holds_7  : r4Count 7  = jacobiR4 7  := by native_decide
theorem jacobi_holds_8  : r4Count 8  = jacobiR4 8  := by native_decide
theorem jacobi_holds_9  : r4Count 9  = jacobiR4 9  := by native_decide
theorem jacobi_holds_10 : r4Count 10 = jacobiR4 10 := by native_decide

-- =====================================================================
-- PART 4: Connection to the FourSquareDistribution type-decomposition
-- =====================================================================

open FourSquareDistribution

/-- The single-type cases (n = 1, 2, 3, 5, 6, 7) match Jacobi's prediction
    via the parent file's `distribution_complete_*`. -/
theorem distribution_matches_jacobi_1 : type_1_a.contribution = jacobiR4 1 := by
  rw [type_1_contribution, jacobiR4_1]
theorem distribution_matches_jacobi_2 : type_2_a.contribution = jacobiR4 2 := by
  rw [type_2_contribution, jacobiR4_2]
theorem distribution_matches_jacobi_3 : type_3_a.contribution = jacobiR4 3 := by
  rw [type_3_contribution, jacobiR4_3]
theorem distribution_matches_jacobi_5 : type_5_a.contribution = jacobiR4 5 := by
  rw [type_5_contribution, jacobiR4_5]
theorem distribution_matches_jacobi_6 : type_6_a.contribution = jacobiR4 6 := by
  rw [type_6_contribution, jacobiR4_6]
theorem distribution_matches_jacobi_7 : type_7_a.contribution = jacobiR4 7 := by
  rw [type_7_contribution, jacobiR4_7]

/-- The multi-type cases (n = 4, 9, 10) match Jacobi's prediction via the
    parent file's two-type decomposition theorems. -/
theorem distribution_matches_jacobi_4 :
    type_4_a.contribution + type_4_b.contribution = jacobiR4 4 := by
  rw [r₄_4_distribution, jacobiR4_4]
theorem distribution_matches_jacobi_9 :
    type_9_a.contribution + type_9_b.contribution = jacobiR4 9 := by
  rw [r₄_9_distribution, jacobiR4_9]
theorem distribution_matches_jacobi_10 :
    type_10_a.contribution + type_10_b.contribution = jacobiR4 10 := by
  rw [r₄_10_distribution, jacobiR4_10]

-- =====================================================================
-- PART 5: Jacobi's general theorem (open conjecture, axiomatized)
-- =====================================================================

/-- **Jacobi's Four-Square Theorem** (Jacobi 1834).

    For every n ≥ 1, the count of integer 4-tuples (a, b, c, d) summing
    to n in squares equals 8·σ*(n):
    $$ r_4(n) = 8 \sum_{\substack{d \mid n \\ 4 \nmid d}} d. $$

    **Status**: Numerically verified above for n = 1..10. The general
    proof requires modular form theory not yet in Mathlib (specifically:
    Fourier coefficients of `jacobiTheta`, identification of θ⁴ with
    weight-2 Eisenstein series E₂(τ) - 4 E₂(4τ), up to constants). -/
axiom jacobi_r4_formula :
    ∀ n : ℕ, 0 < n → r4Count n = jacobiR4 n

/-- The boundary case n = 0: only the all-zero tuple contributes. -/
theorem r4Count_zero : r4Count 0 = 1 := by native_decide

/-- σ*(0) = 0 (the divisors of 0 are empty in Mathlib). -/
theorem sigmaStar_zero : sigmaStar 0 = 0 := by native_decide

end FourSquareDistributionOQ01
