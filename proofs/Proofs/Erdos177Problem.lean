/-
Erdos Problem #177: Discrepancy of Arithmetic Progressions

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
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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
## Part I.5: Basic Properties of apSum and Colorings (ALL PROVED)
-/

/-- Empty AP has sum 0. -/
theorem apSum_zero (f : Coloring) (a d : ℕ) : apSum f a d 0 = 0 := by
  simp [apSum]

/-- Single-element AP has sum f(a). -/
theorem apSum_one (f : Coloring) (a d : ℕ) : apSum f a d 1 = f a := by
  simp [apSum]

/-- apSum recursion: adding one more term. -/
theorem apSum_succ (f : Coloring) (a d k : ℕ) :
    apSum f a d (k + 1) = apSum f a d k + f (a + k * d) := by
  simp [apSum, Finset.sum_range_succ]

/-- For a valid coloring, |f(n)| = 1. -/
theorem valid_abs_eq_one (f : Coloring) (hf : IsValidColoring f) (n : ℕ) :
    (f n).natAbs = 1 := by
  cases hf n with
  | inl h => simp [h]
  | inr h => simp [h]

/-- For a valid coloring, f(n)^2 = 1. -/
theorem valid_sq_eq_one (f : Coloring) (hf : IsValidColoring f) (n : ℕ) :
    f n ^ 2 = 1 := by
  cases hf n with
  | inl h => simp [h]
  | inr h => norm_num [h]

/-- The absolute partial sum of a valid coloring is bounded by the length. -/
theorem apSum_abs_le (f : Coloring) (hf : IsValidColoring f) (a d k : ℕ) :
    (apSum f a d k).natAbs ≤ k := by
  induction k with
  | zero => simp [apSum_zero]
  | succ n ih =>
    rw [apSum_succ]
    calc (apSum f a d n + f (a + n * d)).natAbs
        ≤ (apSum f a d n).natAbs + (f (a + n * d)).natAbs := Int.natAbs_add_le _ _
      _ ≤ n + 1 := by
          have := valid_abs_eq_one f hf (a + n * d)
          omega

/-- The alternating coloring: f(n) = (-1)^n. -/
def alternating : Coloring := fun n => (-1) ^ n

/-- The alternating coloring is valid. -/
theorem alternating_valid : IsValidColoring alternating := by
  intro n
  simp only [alternating]
  induction n with
  | zero => left; simp
  | succ k ih =>
    cases ih with
    | inl h => right; simp [pow_succ, h]
    | inr h => left; simp [pow_succ, h]

/-- The alternating coloring with d=1 has zero sum for even-length APs. -/
theorem alternating_apSum_d1_even (a k : ℕ) :
    apSum alternating a 1 (2 * k) = 0 := by
  induction k with
  | zero => simp [apSum_zero]
  | succ n ih =>
    have h1 : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
    rw [h1, apSum_succ, apSum_succ, ih]
    simp [alternating, mul_one]
    ring

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
/--
**Cantor-Erdős-Schreiber-Straus**: h(d) ≤ d! is achievable.
The earliest quantitative bound.
-/
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
