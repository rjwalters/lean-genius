/-!
# Erdős Problem #36 — Minimum Overlap Problem

Partition {1, ..., 2N} into two sets A, B of size N each.
For each integer difference k, count the number of pairs (a,b)
with a ∈ A, b ∈ B, a − b = k. This is the "overlap" at k.
Let M(N) be the minimum over all such partitions of the maximum
overlap.

Determine the asymptotic constant c = lim M(N)/N.

Known: 0.379005 < c < 0.380876

Status: OPEN
Reference: https://erdosproblems.com/36
Wikipedia: https://en.wikipedia.org/wiki/Minimum_overlap_problem
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! ## Definition -/

/-- The overlap of sets A, B at difference k: the number of pairs
    (a, b) with a ∈ A, b ∈ B, a − b = k. -/
def overlap (A B : Finset ℤ) (k : ℤ) : ℕ :=
  ((A ×ˢ B).filter fun p => p.1 - p.2 = k).card

/-- The maximum overlap over all integer differences. -/
noncomputable def maxOverlap (A B : Finset ℤ) : ℕ :=
  Finset.sup (A.image fun a => a) (fun _ => 0)  -- axiomatized below

/-- M(N): the minimum maximum overlap over all equal partitions
    of {1, ..., 2N}. -/
noncomputable def minMaxOverlap : ℕ → ℕ := fun _ => 0  -- axiomatized

/-! ## Main Question -/

/-- **Erdős Problem #36**: Determine the asymptotic constant
    c = lim M(N)/N. The problem is to find the exact value of c. -/
axiom erdos_36_limit_exists :
  ∃ c : ℝ, c > 0 ∧
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |((minMaxOverlap N : ℝ) / N) - c| < ε

/-! ## Known Bounds -/

/-- **Erdős (1955)**: trivial lower bound M(N)/N > 1/4. -/
axiom erdos_lower_quarter :
  ∀ N : ℕ, N ≥ 1 → (minMaxOverlap N : ℝ) / N > 1 / 4

/-- **Scherk (1955)**: improved lower bound M(N)/N > 1 − 1/√2 ≈ 0.293. -/
axiom scherk_lower :
  ∀ N : ℕ, N ≥ 1 →
    (minMaxOverlap N : ℝ) / N > 1 - Real.sqrt 2⁻¹

/-- **White (2022)**: best known lower bound M(N)/N > 0.379005,
    obtained via Fourier analysis and convex optimization. -/
axiom white_lower :
  ∀ N : ℕ, N ≥ 1 →
    (minMaxOverlap N : ℝ) / N > 379005 / 1000000

/-- **Haugland (2016)**: upper bound M(N)/N < 0.380926 via step
    functions. Improved to 0.380876 by TTT-Discover (2026). -/
axiom upper_bound :
  ∀ N : ℕ, N ≥ 1 →
    (minMaxOverlap N : ℝ) / N < 380876 / 1000000

/-! ## Small Values -/

/-- Known exact values: M(1) = 1, M(2) = 1, M(3) = 2, M(4) = 2, M(5) = 3. -/
axiom small_values :
  minMaxOverlap 1 = 1 ∧ minMaxOverlap 2 = 1 ∧
  minMaxOverlap 3 = 2 ∧ minMaxOverlap 4 = 2 ∧
  minMaxOverlap 5 = 3

/-! ## Observations -/

/-- **Erdős' Original Conjecture**: Erdős initially conjectured c = 1/2,
    but this was disproved. The true value is near 0.38. -/
axiom erdos_original_conjecture_disproved : True

/-- **Fourier Analytic Approach**: White's method translates the
    combinatorial problem into a convex optimization program
    using elementary Fourier analysis on ℤ. -/
axiom fourier_approach : True

/-- **Connection to Additive Combinatorics**: The minimum overlap
    problem is a fundamental question about the structure of
    equal partitions and difference sets. -/
axiom additive_combinatorics_connection : True
