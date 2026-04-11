/-
  Erdős Problem #990: Polynomial Root Distribution and the Erdős-Turán Inequality

  Source: https://erdosproblems.com/990
  Status: DISPROVED (Alexeev-Putterman-Sawhney-Sellke-Valiant 2026,
  arXiv:2604.06609)

  Statement:
  Let f = a₀ + a₁x + ⋯ + aₐxᵈ ∈ ℂ[x] be a polynomial with roots z₁,...,zₐ
  having arguments θ₁,...,θₐ ∈ [0,2π]. Is it true that for all intervals I ⊆ [0,2π]:

    |#{θᵢ ∈ I} - |I|d/(2π)| ≪ (n log M)^{1/2}

  where n is the number of nonzero coefficients and
  M = (|a₀| + ⋯ + |aₐ|)/√(|a₀||aₐ|)?

  DISPROVED: Explicit lacunary polynomials with ν(f) = N+2 nonzero terms,
  M(f) < 3, and a positive real root of multiplicity N+1 show that no
  bound of order √(ν(f) log M(f)) can hold uniformly. Hayman's bound
  discrepancy ≤ ν(f)-1 (1972) remains the best possible sparse bound.

  Background:
  - Erdős-Turán (1950): Proved the bound with n replaced by d (the degree)
  - APSSV (2026): Disproved the sparse strengthening
  - Hayman (1972): discrepancy ≤ ν(f)-1 (best possible for sparse case)

  Tags: analysis, polynomials, equidistribution, discrepancy
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Topology.MetricSpace.Basic

namespace Erdos990

open Complex Real Polynomial

/-
## Part 1: Basic Definitions

Setting up polynomials and their roots in the complex plane.
-/

/-- A complex polynomial of degree at most d -/
abbrev ComplexPoly (d : ℕ) := Fin (d + 1) → ℂ

/-- The degree of a polynomial (highest nonzero coefficient) -/
noncomputable def polyDegree (d : ℕ) (p : ComplexPoly d) : ℕ :=
  d -- Simplified; actual definition would find highest nonzero term

/-- Number of nonzero coefficients (sparsity) -/
def nonzeroCoeffCount (d : ℕ) (p : ComplexPoly d) : ℕ :=
  (Finset.univ.filter (fun i => p i ≠ 0)).card

/-- The argument (angle) of a complex number in [0, 2π) -/
noncomputable def argument (z : ℂ) : ℝ :=
  if z = 0 then 0 else arg z + (if arg z < 0 then 2 * π else 0)

/-
## Part 2: The Mahler Measure

The quantity M appears in the Erdős-Turán bound.
-/

/-- Sum of absolute values of coefficients -/
noncomputable def coeffSum (d : ℕ) (p : ComplexPoly d) : ℝ :=
  ∑ i : Fin (d + 1), Complex.abs (p i)

/-- The normalization factor M = (|a₀| + ⋯ + |aₐ|)/√(|a₀||aₐ|) -/
noncomputable def mahlerM (d : ℕ) (p : ComplexPoly d) (hd : 0 < d) : ℝ :=
  let a0 := Complex.abs (p 0)
  let ad := Complex.abs (p ⟨d, Nat.lt_succ_self d⟩)
  if a0 * ad = 0 then 1 else coeffSum d p / Real.sqrt (a0 * ad)

/-
## Part 3: Root Counting and Discrepancy

Counting roots in angular intervals.
-/

/-- Roots of a polynomial (axiomatized) -/
axiom rootSet (d : ℕ) (p : ComplexPoly d) : Finset ℂ

/-- Count roots with argument in interval [α, β] -/
noncomputable def rootsInInterval (d : ℕ) (p : ComplexPoly d) (α β : ℝ) : ℕ :=
  ((rootSet d p).filter (fun z => α ≤ argument z ∧ argument z ≤ β)).card

/-- Expected count if roots were uniformly distributed -/
noncomputable def expectedCount (d : ℕ) (α β : ℝ) : ℝ :=
  (β - α) * d / (2 * π)

/-- The discrepancy: deviation from uniform distribution -/
noncomputable def discrepancy (d : ℕ) (p : ComplexPoly d) (α β : ℝ) : ℝ :=
  |(rootsInInterval d p α β : ℝ) - expectedCount d α β|

/-- Maximum discrepancy over all intervals -/
noncomputable def maxDiscrepancy (d : ℕ) (p : ComplexPoly d) : ℝ :=
  sSup {discrepancy d p α β | (α : ℝ) (β : ℝ) (_hαβ : 0 ≤ α ∧ α ≤ β ∧ β ≤ 2 * π)}

/-
## Part 4: The Classical Erdős-Turán Inequality (1950)

The original bound in terms of degree d.
-/

/-- Erdős-Turán (1950): Classical bound with degree d -/
axiom erdos_turan_classical (d : ℕ) (p : ComplexPoly d) (hd : 0 < d)
    (hp : p ⟨d, Nat.lt_succ_self d⟩ ≠ 0) (h0 : p 0 ≠ 0) :
    ∃ C : ℝ, C > 0 ∧ maxDiscrepancy d p ≤ C * Real.sqrt (d * Real.log (mahlerM d p hd))

/-- The constant C in Erdős-Turán can be made explicit -/
axiom erdos_turan_explicit_constant :
    ∃ C : ℝ, C > 0 ∧ ∀ (d : ℕ) (p : ComplexPoly d) (hd : 0 < d)
      (hp : p ⟨d, Nat.lt_succ_self d⟩ ≠ 0) (h0 : p 0 ≠ 0),
      maxDiscrepancy d p ≤ C * Real.sqrt (d * Real.log (mahlerM d p hd))

/-
## Part 5: The Sparse Conjecture (Erdős Problem #990)

Can we replace d with n (number of nonzero coefficients)?
-/

/-- The conjectured sparse bound -/
def sparseConjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ (d : ℕ) (p : ComplexPoly d) (hd : 0 < d)
    (hp : p ⟨d, Nat.lt_succ_self d⟩ ≠ 0) (h0 : p 0 ≠ 0),
    maxDiscrepancy d p ≤ C * Real.sqrt ((nonzeroCoeffCount d p : ℝ) * Real.log (mahlerM d p hd))

/-- If true, this would be a significant improvement for sparse polynomials -/
theorem sparse_improves_dense (d : ℕ) (p : ComplexPoly d) :
    nonzeroCoeffCount d p ≤ d + 1 := by
  simp only [nonzeroCoeffCount]
  exact Finset.card_filter_le _ _

/-
## Part 6: Sharp Constant

Recent work on the optimal constant in Erdős-Turán.
-/

/-
## Part 7: Special Cases

Polynomials where root distribution is well-understood.
-/

/-- Littlewood polynomials (coefficients ±1): special structure -/
def isLittlewood (d : ℕ) (p : ComplexPoly d) : Prop :=
  ∀ i : Fin (d + 1), Complex.abs (p i) = 1 ∨ p i = 0

/-
## Part 8: Generalizations

Extensions beyond the unit circle.
-/

/-
## Part 9: Applications

Where the Erdős-Turán inequality is used.
-/

/-
## Part 10: Lower Bounds

The Erdős-Turán bound is essentially tight.
-/

/-
## Part 11: One-Sided Improvements

Erdélyi's refinement.
-/

/-
## Part 12: Summary

Erdős Problem #990 status: The classical Erdős-Turán (1950) is proved.
The sparse case (replacing d with n) remains OPEN.
-/

/-- What is known: Classical Erdős-Turán with degree d -/
theorem erdos_turan_known (d : ℕ) (p : ComplexPoly d) (hd : 0 < d)
    (hp : p ⟨d, Nat.lt_succ_self d⟩ ≠ 0) (h0 : p 0 ≠ 0) :
    ∃ C : ℝ, C > 0 ∧ maxDiscrepancy d p ≤ C * Real.sqrt (d * Real.log (mahlerM d p hd)) :=
  erdos_turan_classical d p hd hp h0

/-- DISPROVED: The sparse conjecture is FALSE.
    Alexeev-Putterman-Sawhney-Sellke-Valiant (2026, arXiv:2604.06609)
    constructed lacunary polynomials with ν(f) = N+2, M(f) < 3, and a
    positive real root of multiplicity N+1, yielding discrepancy ≥ N+1/2
    while √(ν(f) log M(f)) = O(√N). -/
axiom erdos_990_sparse_disproof : ¬ sparseConjecture

/-- Summary of Erdős Problem #990:
    The classical Erdős-Turán inequality with degree d is PROVED.
    The sparse strengthening (replacing d with ν(f)) is DISPROVED. -/
theorem erdos_990_summary :
    ∃ C : ℝ, C > 0 ∧ ∀ (d : ℕ) (p : ComplexPoly d) (hd : 0 < d)
      (hp : p ⟨d, Nat.lt_succ_self d⟩ ≠ 0) (h0 : p 0 ≠ 0),
      maxDiscrepancy d p ≤ C * Real.sqrt (d * Real.log (mahlerM d p hd)) :=
  erdos_turan_explicit_constant

end Erdos990
