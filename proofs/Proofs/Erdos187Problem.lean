/-
# Erdős Problem #187: Arithmetic Progressions in 2-Colorings

Find the optimal function f(d) such that in any 2-coloring of ℤ,
at least one color class contains an arithmetic progression of length
f(d) with common difference d, for infinitely many d.

Known:
- f(d) → ∞ as d → ∞ (van der Waerden's theorem)
- f(d) ≤ (1 + o(1)) log₂ d (Beck, 1980)
- f(d) ≫ d from Erdős's √2-coloring construction

Status: OPEN.

Reference: https://erdosproblems.com/187
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic

/- ## Definitions -/

/-- A 2-coloring of ℕ. -/
def TwoColoring := ℕ → Fin 2

/-- An arithmetic progression of length k with common difference d
    starting at a: the set {a, a+d, a+2d, ..., a+(k-1)d}. -/
def IsMonoAP (χ : TwoColoring) (a d k : ℕ) : Prop :=
  0 < d ∧ 0 < k ∧ ∃ c : Fin 2, ∀ i : Fin k, χ (a + i.val * d) = c

/-- The optimal function f(d) = inf over all 2-colorings of the
    supremum of monochromatic AP lengths with difference d,
    required to hold for infinitely many d. Axiomatized. -/
axiom optAPBound (d : ℕ) : ℕ

/- ## Known Results -/

/-- Van der Waerden's theorem implies f(d) → ∞: for every k, there exists
    d such that optAPBound d ≥ k. Follows from van der Waerden's theorem: any
    2-coloring of [1, W(2,k)] contains a monochromatic k-AP. -/
axiom optAPBound_unbounded : ∀ k : ℕ, ∃ d : ℕ, k ≤ optAPBound d

/-- Beck's upper bound (1980): there exists C > 0 such that for all sufficiently
    large d, optAPBound d ≤ C * (Nat.log 2 d + 1). Gives f(d) = O(log d).
    Beck's proof uses a discrepancy argument to construct an explicit 2-coloring
    where no monochromatic AP with difference d exceeds O(log d) in length. -/
axiom beck_upper_bound : ∃ C : ℕ, 0 < C ∧ ∃ D₀ : ℕ, ∀ d : ℕ, D₀ ≤ d →
    optAPBound d ≤ C * (Nat.log 2 d + 1)

/- ## The Open Question -/

/-- **Erdős Problem #187 (open):** Is f(d) = Θ(log d)?
    Asks for a matching lower bound: does there exist c > 0 such that
    c * log₂ d ≤ optAPBound d for all sufficiently large d?
    Beck's O(log d) upper bound is believed tight, but no lower bound
    better than f(d) → ∞ is known. -/
axiom erdos_187_conjecture : ∃ c : ℕ, 0 < c ∧ ∃ D₀ : ℕ, ∀ d : ℕ, D₀ ≤ d →
    c * Nat.log 2 d ≤ optAPBound d
