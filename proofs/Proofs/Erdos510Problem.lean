/-
# Erdős Problem #510 — Chowla's Cosine Problem

For a finite set A ⊂ ℕ of size N > 0, does there exist an absolute
constant c > 0 such that for every such A, there exists θ with
  ∑_{n ∈ A} cos(nθ) < −c√N?

The example A = B − B for a Sidon set B shows √N is best possible.

Known: Bedert (2025) proved a −cN^{1/7} lower bound. The gap between
N^{1/7} and N^{1/2} remains open.

Status: OPEN
Reference: https://erdosproblems.com/510
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/- ## Definition -/

/-- The cosine sum of a finite set A ⊂ ℕ at angle θ. -/
noncomputable def cosineSum (A : Finset ℕ) (θ : ℝ) : ℝ :=
  ∑ n ∈ A, Real.cos (n * θ)

/-- The minimum cosine sum over all angles θ. -/
noncomputable def minCosineSum (A : Finset ℕ) : ℝ :=
  iInf (cosineSum A)

/- ## Main Conjecture -/

/-- **Chowla's Cosine Problem (Erdős Problem #510)**: There exists
    c > 0 such that for every finite A ⊂ ℕ⁺ of size N, there
    exists θ with ∑_{n ∈ A} cos(nθ) < −c√N. -/
/- ## Known Bounds -/

/-- **Bedert (2025)**: There exists c > 0 such that for all finite
    A ⊂ ℕ⁺ of size N, min_θ ∑ cos(nθ) < −cN^{1/7}. -/
/- **Ruzsa (2004)**: Improved Bourgain's (1986) bound. The minimum
    cosine sum is at most −exp(O(√(log N))). -/

/- **Bourgain (1986)**: First non-trivial bound for the cosine
    problem, later improved by Ruzsa. -/

/- ## Optimality -/

/-- **Sidon Set Construction**: For A = B − B where B is a Sidon set
    of size ≈ √N, the set A has size N and the minimum cosine sum
    is ≈ −√N. This shows √N is the best possible exponent. -/
/- ## Observations -/

/- **Connection to Additive Combinatorics**: The cosine problem is
    intimately related to the structure of difference sets and
    exponential sums in additive number theory. -/

/- **Green's Problem 81**: This appears as Problem 81 on Ben Green's
    list of open problems in additive combinatorics. -/

/- **Polynomial Progress (2025)**: Both Bedert and Jin–Milojević–
    Tomon–Zhang independently achieved polynomial bounds,
    representing major progress toward the √N conjecture. -/
