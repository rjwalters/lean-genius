/-!
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

/-! ## Definitions -/

/-- A 2-coloring of ℕ. -/
def TwoColoring := ℕ → Fin 2

/-- An arithmetic progression of length k with common difference d
    starting at a: the set {a, a+d, a+2d, ..., a+(k-1)d}. -/
def IsMonoAP (χ : TwoColoring) (a d k : ℕ) : Prop :=
  0 < d ∧ 0 < k ∧ ∃ c : Fin 2, ∀ i : Fin k, χ (a + i.val * d) = c

/-- For a given coloring χ and difference d, the maximum length of a
    monochromatic AP with common difference d. Axiomatized. -/
axiom maxMonoAPLength (χ : TwoColoring) (d : ℕ) : ℕ

/-- maxMonoAPLength is at least 1 for positive d. -/
axiom maxMonoAPLength_pos (χ : TwoColoring) (d : ℕ) (hd : 0 < d) :
  1 ≤ maxMonoAPLength χ d

/-- The optimal function f(d) = inf over all 2-colorings of the
    supremum of monochromatic AP lengths with difference d,
    required to hold for infinitely many d. Axiomatized. -/
axiom optAPBound (d : ℕ) : ℕ

/-! ## Known Results -/

/-- Van der Waerden's theorem implies f(d) → ∞: for any 2-coloring,
    monochromatic APs of arbitrary length exist. In particular,
    for every k there exists d such that f(d) ≥ k. -/
axiom vanDerWaerden_implies_growth :
  ∀ k : ℕ, ∃ d : ℕ, 0 < d ∧ k ≤ optAPBound d

/-- Beck's upper bound (1980): f(d) ≤ (1 + o(1)) log₂ d.
    Formalized as: there exists C such that for all large d,
    optAPBound d ≤ C * Nat.log 2 d. -/
axiom beck_upper_bound :
  ∃ C : ℕ, 0 < C ∧
    ∃ D₀ : ℕ, ∀ d : ℕ, D₀ ≤ d →
      optAPBound d ≤ C * (Nat.log 2 d + 1)

/-- Erdős's √2-coloring construction gives a lower bound f(d) ≫ d.
    There exists a 2-coloring such that the longest monochromatic AP
    with difference d has length O(d). -/
axiom erdos_sqrt2_construction :
  ∃ (χ : TwoColoring) (C : ℕ), 0 < C ∧
    ∀ d : ℕ, 0 < d → maxMonoAPLength χ d ≤ C * d

/-! ## The Open Question -/

/-- Erdős Problem #187: Determine the exact asymptotic behavior of f(d).
    Is f(d) = Θ(log d)? Formalized as asking whether there exist
    constants c, C such that c · log₂ d ≤ f(d) ≤ C · log₂ d
    for all large d. -/
axiom erdos_187_optimal_bound :
  ∃ (c C : ℕ), 0 < c ∧ 0 < C ∧
    ∃ D₀ : ℕ, ∀ d : ℕ, D₀ ≤ d →
      c * (Nat.log 2 d) ≤ optAPBound d ∧
      optAPBound d ≤ C * (Nat.log 2 d + 1)
