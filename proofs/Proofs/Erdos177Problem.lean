/-
Erdős Problem #177: Discrepancy of Arithmetic Progressions

Source: https://erdosproblems.com/177
Status: OPEN

Statement:
Find the smallest function h(d) such that there exists f : ℕ → {-1, 1} where
for every d ≥ 1, the maximum absolute partial sum over arithmetic progressions
with common difference d is at most h(d).

Known bounds:
- Lower: h(d) ≫ d^{1/2} (from Roth's discrepancy theorem)
- Upper: h(d) ≤ d^{8+ε} (Beck)
- Cantor, Erdős, Schreiber, Straus: h(d) ≤ d! is achievable

References:
- Erdős (1966): Original problem
- Roth: Discrepancy lower bound
- Beck: Upper bound improvement
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

namespace Erdos177

/-
## Part I: Definitions
-/

/-- A coloring function f : ℕ → {-1, 1}. -/
def Coloring := ℕ → Int

/-- A coloring takes values in {-1, 1}. -/
def IsValidColoring (f : Coloring) : Prop :=
  ∀ n, f n = 1 ∨ f n = -1

/-- The partial sum of f along an arithmetic progression {a, a+d, ..., a+(k-1)d}. -/
def apSum (f : Coloring) (a d k : ℕ) : Int :=
  (Finset.range k).sum (fun i => f (a + i * d))

/--
The discrepancy of f with respect to common difference d:
the supremum of |∑ f(n)| over all finite APs with common difference d.
-/
noncomputable def discrepancy (f : Coloring) (d : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a n : ℕ, n ≥ 1 ∧ (apSum f a d n).natAbs = k}

/--
h(d) = the minimum discrepancy achievable over all valid colorings.
-/
noncomputable def h (d : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ f : Coloring, IsValidColoring f ∧ discrepancy f d = k}

/-
## Part II: Known Bounds
-/

/--
**Lower bound**: h(d) ≫ √d.
From Roth's discrepancy theorem: no coloring can have discrepancy
smaller than c√d for arithmetic progressions of common difference d.
-/
axiom roth_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ d : ℕ, d ≥ 1 →
      (h d : ℝ) ≥ c * Real.sqrt d

/--
**Beck's upper bound**: h(d) ≤ d^{8+ε}.
For every ε > 0, there exists a coloring achieving this bound.
-/
axiom beck_upper_bound :
    ∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧ ∀ d : ℕ, d ≥ 1 →
      (h d : ℝ) ≤ C * (d : ℝ) ^ (8 + ε)

/--
**Cantor-Erdős-Schreiber-Straus**: h(d) ≤ d! is achievable.
The earliest quantitative bound.
-/
axiom factorial_bound :
    ∀ d : ℕ, d ≥ 1 → h d ≤ Nat.factorial d

/-
## Part III: Main Theorem
-/

/--
**Erdős Problem #177: OPEN**

Known bounds: c√d ≤ h(d) ≤ C·d^{8+ε}.
The exact order of growth remains unknown.
-/
theorem erdos_177 :
    ∃ c : ℝ, c > 0 ∧ ∀ d : ℕ, d ≥ 1 →
      (h d : ℝ) ≥ c * Real.sqrt d :=
  roth_lower_bound

end Erdos177
