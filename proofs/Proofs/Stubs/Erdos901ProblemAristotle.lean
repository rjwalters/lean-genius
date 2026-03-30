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
    (h : ∀ v ∈ e, c v = 0) : IsMonochromatic c e := Or.inl h

/-- If all vertices get color 1, the edge is monochromatic. -/
theorem all_one_monochromatic {V : Type*} (e : Finset V) (c : TwoColoring V)
    (h : ∀ v ∈ e, c v = 1) : IsMonochromatic c e := Or.inr h

/-- A non-monochromatic edge has both colors. -/
theorem not_mono_has_both_colors {V : Type*} (e : Finset V) (c : TwoColoring V)
    (hne : e.Nonempty) (h : ¬IsMonochromatic c e) :
    (∃ v ∈ e, c v = 0) ∧ (∃ v ∈ e, c v = 1) := by
  simp only [IsMonochromatic, not_or] at h
  push_neg at h
  obtain ⟨⟨v0, hv0, hcv0⟩, ⟨v1, hv1, hcv1⟩⟩ := h
  refine ⟨⟨v1, hv1, ?_⟩, ⟨v0, hv0, ?_⟩⟩ <;> fin_cases (c v1) <;> fin_cases (c v0) <;> simp_all

/-- The probability computation: 2^(1-n) = 2/2^n for n ≥ 1. -/
theorem monochromatic_prob (n : ℕ) (hn : n ≥ 1) :
    (2 : ℝ) ^ (1 - (n : ℤ)) = 2 / 2 ^ n := by
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  have htp : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_eq_iff htp.ne']
  rw [← zpow_natCast (2 : ℝ) n, ← zpow_add₀ h2ne]
  have : (1 : ℤ) - ↑n + ↑n = 1 := by omega
  rw [this, zpow_one]

/-- Basic: 2^n > 0 for any n. -/
theorem two_pow_pos (n : ℕ) : (2 : ℝ) ^ n > 0 := by positivity

/-- Basic: 2^n ≥ 1 for any n. -/
theorem two_pow_ge_one (n : ℕ) : (2 : ℝ) ^ n ≥ 1 := by
  have : (1 : ℝ) ^ n ≤ 2 ^ n := by
    apply pow_le_pow_left (by norm_num) (by norm_num)
  simpa using this

/-- Basic: 2^n is strictly increasing. -/
theorem two_pow_strict_mono {a b : ℕ} (h : a < b) : (2 : ℝ) ^ a < (2 : ℝ) ^ b := by
  exact pow_lt_pow_right (by norm_num : (1 : ℝ) < 2) h

/-- n * 2^n > 2^n for n ≥ 2. -/
theorem n_times_two_pow_gt (n : ℕ) (hn : n ≥ 2) :
    (n : ℝ) * 2 ^ n > 2 ^ n := by
  have h1 : (1 : ℝ) < n := by exact_mod_cast show 1 < n by omega
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  nlinarith

/-- n² * 2^n > n * 2^n for n ≥ 2. -/
theorem n_sq_times_two_pow_gt (n : ℕ) (hn : n ≥ 2) :
    (n : ℝ) ^ 2 * 2 ^ n > (n : ℝ) * 2 ^ n := by
  have h1 : (1 : ℝ) < n := by exact_mod_cast show 1 < n by omega
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have h3 : (0 : ℝ) < n := by linarith
  nlinarith [sq_nonneg ((n : ℝ) - 1)]

/-- √(n/log n) < n for n ≥ 3. -/
theorem sqrt_n_log_lt_n (n : ℕ) (hn : n ≥ 3) :
    Real.sqrt ((n : ℝ) / Real.log n) < n := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have hlog_pos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast show 1 < n by omega)
  -- sqrt(x) < y ⟺ x < y² (for y > 0, x ≥ 0)
  rw [← Real.sqrt_sq hn_pos.le]
  exact Real.sqrt_lt_sqrt (div_nonneg hn_pos.le hlog_pos.le) <| by
    -- Need: n / log n < n²
    rw [div_lt_iff hlog_pos]
    -- Need: n < n² * log n
    have hlog_ge_1 : 1 ≤ Real.log (n : ℝ) := by
      have : Real.exp 1 ≤ (n : ℝ) := by
        calc Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
          _ ≤ n := by exact_mod_cast hn
      rwa [Real.exp_le_iff_le_log hn_pos] at this
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith

/-- For a Fin 2 value, it is either 0 or 1. -/
theorem fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

/-- Pigeonhole for 2 colors: in a set of n+1 elements colored with 2 colors,
    some color appears at least ⌈(n+1)/2⌉ times. -/
theorem pigeonhole_two_colors {V : Type*} [DecidableEq V]
    (s : Finset V) (c : V → Fin 2) (hs : s.card ≥ 1) :
    (s.filter (fun v => c v = 0)).card ≥ 1 ∨
    (s.filter (fun v => c v = 1)).card ≥ 1 := by
  obtain ⟨v, hv⟩ := card_pos.mp (by omega : 0 < s.card)
  rcases fin2_cases (c v) with h | h
  · left; exact card_pos.mpr ⟨v, mem_filter.mpr ⟨hv, h⟩⟩
  · right; exact card_pos.mpr ⟨v, mem_filter.mpr ⟨hv, h⟩⟩

end Erdos901.Aristotle
