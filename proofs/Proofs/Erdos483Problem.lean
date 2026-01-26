/-!
# Erdős Problem #483: Growth Rate of Schur Numbers

The Schur number f(k) is the minimal N such that every k-coloring of
{1, ..., N} contains a monochromatic solution to a + b = c.

Question: Is f(k) < c^k for some constant c > 0?

Known:
- f(1) = 2, f(2) = 5, f(3) = 14, f(4) = 45, f(5) = 161
- Lower bound: f(k) ≥ 380^{k/5} - O(1) (Ageron et al.)
- Upper bound: f(k) ≤ ⌊(e - 1/24)k!⌋ - 1 (Whitehead, 1973)
- Schur's theorem (1916): f(k) is finite for all k

Status: OPEN.

Reference: https://erdosproblems.com/483
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

/-! ## Definitions -/

/-- A k-coloring of {1, ..., N}. -/
def Coloring (N k : ℕ) := Fin N → Fin k

/-- A coloring has a monochromatic sum-free triple a + b = c if
    there exist a, b, c in {1,...,N} with the same color and a + b = c. -/
def HasMonochromaticSum {N k : ℕ} (χ : Coloring N k) : Prop :=
  ∃ (a b : Fin N), a.val + 1 + (b.val + 1) ≤ N ∧
    χ a = χ b ∧
    ∃ c : Fin N, c.val + 1 = (a.val + 1) + (b.val + 1) ∧ χ a = χ c

/-- The Schur number f(k): smallest N such that every k-coloring of {1,...,N}
    has a monochromatic solution to a + b = c. Axiomatized. -/
axiom schurNumber (k : ℕ) : ℕ

/-- schurNumber k is positive for k ≥ 1. -/
axiom schurNumber_pos (k : ℕ) (hk : 1 ≤ k) : 1 ≤ schurNumber k

/-! ## Known Values -/

/-- f(1) = 2: any 1-coloring of {1, 2} has 1 + 1 = 2. -/
axiom schur_1 : schurNumber 1 = 2

/-- f(2) = 5. -/
axiom schur_2 : schurNumber 2 = 5

/-- f(3) = 14. -/
axiom schur_3 : schurNumber 3 = 14

/-- f(4) = 45. -/
axiom schur_4 : schurNumber 4 = 45

/-- f(5) = 161. -/
axiom schur_5 : schurNumber 5 = 161

/-! ## Bounds -/

/-- Lower bound: f(k) ≥ 380^{k/5} - O(1).
    Simplified: f(k) grows at least exponentially. -/
axiom schur_lower_bound :
  ∃ C : ℝ, 1 < C ∧ ∀ k : ℕ, 1 ≤ k →
    C ^ k ≤ (schurNumber k : ℝ)

/-- Upper bound: f(k) ≤ ⌊(e - 1/24)k!⌋ - 1 (Whitehead 1973).
    Simplified: f(k) ≤ C · k! for some constant C. -/
axiom schur_upper_bound :
  ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k →
    (schurNumber k : ℝ) ≤ C * (Nat.factorial k : ℝ)

/-! ## The Conjecture -/

/-- Erdős Problem #483: Is f(k) < c^k for some constant c > 0?
    That is, are Schur numbers bounded by a simple exponential? -/
axiom erdos_483_conjecture :
  ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
    (schurNumber k : ℝ) < c ^ k
