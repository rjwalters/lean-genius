/-
  Aristotle targets for Erdos901Problem
  Routine supporting lemmas for automated proof search.
  See Stubs/Erdos901Problem.lean for the main formalization.
-/
import Mathlib.Combinatorics.SetFamily.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Erdos901.Aristotle

open Finset Real

/-- A 2-coloring of vertices. -/
def TwoColoring (V : Type*) := V → Fin 2

/-- An edge is monochromatic under a coloring if all vertices have the same color. -/
def IsMonochromatic {V : Type*} (c : TwoColoring V) (e : Finset V) : Prop :=
  (∀ v ∈ e, c v = 0) ∨ (∀ v ∈ e, c v = 1)

/-- If all vertices get color 0, the edge is monochromatic. -/
theorem all_zero_monochromatic {V : Type*} (e : Finset V) (c : TwoColoring V)
    (h : ∀ v ∈ e, c v = 0) : IsMonochromatic c e := by sorry

/-- If all vertices get color 1, the edge is monochromatic. -/
theorem all_one_monochromatic {V : Type*} (e : Finset V) (c : TwoColoring V)
    (h : ∀ v ∈ e, c v = 1) : IsMonochromatic c e := by sorry

/-- A non-monochromatic edge has both colors. -/
theorem not_mono_has_both_colors {V : Type*} (e : Finset V) (c : TwoColoring V)
    (hne : e.Nonempty) (h : ¬IsMonochromatic c e) :
    (∃ v ∈ e, c v = 0) ∧ (∃ v ∈ e, c v = 1) := by sorry

/-- The probability computation: 2^(1-n) = 2/2^n for n ≥ 1. -/
theorem monochromatic_prob (n : ℕ) (hn : n ≥ 1) :
    (2 : ℝ) ^ (1 - (n : ℤ)) = 2 / 2 ^ n := by sorry

/-- Basic: 2^n > 0 for any n. -/
theorem two_pow_pos (n : ℕ) : (2 : ℝ) ^ n > 0 := by sorry

/-- Basic: 2^n ≥ 1 for any n. -/
theorem two_pow_ge_one (n : ℕ) : (2 : ℝ) ^ n ≥ 1 := by sorry

/-- Basic: 2^n is strictly increasing. -/
theorem two_pow_strict_mono {a b : ℕ} (h : a < b) : (2 : ℝ) ^ a < (2 : ℝ) ^ b := by sorry

/-- n * 2^n > 2^n for n ≥ 2. -/
theorem n_times_two_pow_gt (n : ℕ) (hn : n ≥ 2) :
    (n : ℝ) * 2 ^ n > 2 ^ n := by sorry

/-- n² * 2^n > n * 2^n for n ≥ 2. -/
theorem n_sq_times_two_pow_gt (n : ℕ) (hn : n ≥ 2) :
    (n : ℝ) ^ 2 * 2 ^ n > (n : ℝ) * 2 ^ n := by sorry

/-- √(n/log n) < n for n ≥ 3. -/
theorem sqrt_n_log_lt_n (n : ℕ) (hn : n ≥ 3) :
    Real.sqrt ((n : ℝ) / Real.log n) < n := by sorry

/-- For a Fin 2 value, it is either 0 or 1. -/
theorem fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by sorry

/-- Pigeonhole for 2 colors: in a set of n+1 elements colored with 2 colors,
    some color appears at least ⌈(n+1)/2⌉ times. -/
theorem pigeonhole_two_colors {V : Type*} [DecidableEq V]
    (s : Finset V) (c : V → Fin 2) (hs : s.card ≥ 1) :
    (s.filter (fun v => c v = 0)).card ≥ 1 ∨
    (s.filter (fun v => c v = 1)).card ≥ 1 := by sorry

end Erdos901.Aristotle
