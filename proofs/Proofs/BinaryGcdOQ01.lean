/-
Binary GCD OQ-01: Formal Step Count Comparison

Compares the number of steps taken by the Binary GCD (Stein's algorithm)
versus the Euclidean algorithm, with formal asymptotic bounds.

References:
  - Stein (1967), Lamé (1844), Knuth TAOCP 4.5.2
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Proofs.GCDAlgorithmOQ01

open Nat

namespace BinaryGcdOQ01

/-- Steps in the Euclidean algorithm (handles symmetry internally). -/
def euclidSteps (a b : ℕ) : ℕ :=
  match a, b with
  | 0, _ => 0
  | _, 0 => 0
  | a' + 1, b' + 1 =>
    if b' + 1 ≤ a' then
      1 + euclidSteps (b' + 1) ((a' + 1) % (b' + 1))
    else
      1 + euclidSteps (a' + 1) ((b' + 1) % (a' + 1))
  termination_by a + b
  decreasing_by
    · have := Nat.mod_lt (a' + 1) (show b' + 1 > 0 by omega); omega
    · have := Nat.mod_lt (b' + 1) (show a' + 1 > 0 by omega); omega

/-- Steps in the Binary GCD algorithm. -/
def binaryGcdSteps (a b : ℕ) : ℕ :=
  match a, b with
  | 0, _ => 0
  | _, 0 => 0
  | a' + 1, b' + 1 =>
    if (a' + 1) % 2 = 0 then
      if (b' + 1) % 2 = 0 then
        1 + binaryGcdSteps ((a' + 1) / 2) ((b' + 1) / 2)
      else
        1 + binaryGcdSteps ((a' + 1) / 2) (b' + 1)
    else if (b' + 1) % 2 = 0 then
      1 + binaryGcdSteps (a' + 1) ((b' + 1) / 2)
    else if a' + 1 > b' + 1 then
      1 + binaryGcdSteps ((a' + 1 - (b' + 1)) / 2) (b' + 1)
    else
      1 + binaryGcdSteps (a' + 1) ((b' + 1 - (a' + 1)) / 2)
  termination_by a + b
  decreasing_by all_goals omega

@[simp] theorem binaryGcdSteps_zero_right (a : ℕ) : binaryGcdSteps a 0 = 0 := by
  cases a with
  | zero => exact binaryGcdSteps.eq_1 0
  | succ a' => exact binaryGcdSteps.eq_2 _ (by omega)

/-! ## Concrete step counts -/

example : euclidSteps 12 8 = 2 := by native_decide
example : binaryGcdSteps 12 8 = 5 := by native_decide
example : euclidSteps 21 15 = 3 := by native_decide
example : binaryGcdSteps 21 15 = 4 := by native_decide
example : euclidSteps 100 37 = 6 := by native_decide
example : binaryGcdSteps 100 37 = 10 := by native_decide
example : euclidSteps 89 55 = 9 := by native_decide
example : binaryGcdSteps 89 55 = 8 := by native_decide

/-! ## Lamé's Theorem -/

/-- euclidSteps(a,b) = euclideanSteps(max a b, min a b) for positive inputs.
    Proof: both recur as f(b, a mod b) when a ≥ b; euclidSteps handles the
    a < b case directly while euclideanSteps needs an extra swap step. -/
private theorem euclidSteps_eq_ordered :
    ∀ n a b : ℕ, a + b ≤ n → 0 < a → 0 < b →
    euclidSteps a b = GCDAlgorithmOQ01.euclideanSteps (max a b) (min a b) := by
  intro n
  induction n with
  | zero => intro a b hab ha hb; omega
  | succ n ih =>
    intro a b hab ha hb
    obtain ⟨a', rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
    rw [euclidSteps.eq_3]
    split
    · -- b' + 1 ≤ a': a > b, so max = a, min = b
      rename_i h_ge
      rw [show max (a' + 1) (b' + 1) = a' + 1 from by omega,
          show min (a' + 1) (b' + 1) = b' + 1 from by omega,
          GCDAlgorithmOQ01.euclideanSteps_pos_eq _ _ (by omega)]
      -- Goal: 1 + euclidSteps (b'+1) ((a'+1)%(b'+1)) = euclideanSteps (b'+1) ((a'+1)%(b'+1)) + 1
      have hmod_lt := Nat.mod_lt (a' + 1) (show b' + 1 > 0 by omega)
      by_cases hr : (a' + 1) % (b' + 1) = 0
      · -- remainder = 0
        rw [hr]; simp [euclidSteps, GCDAlgorithmOQ01.euclideanSteps]
      · -- remainder > 0
        have hr_pos : 0 < (a' + 1) % (b' + 1) := Nat.pos_of_ne_zero hr
        have ih' := ih (b' + 1) ((a' + 1) % (b' + 1)) (by omega) (by omega) hr_pos
        -- max(b'+1, r) = b'+1 since r < b'+1; min = r
        rw [show max (b' + 1) ((a' + 1) % (b' + 1)) = b' + 1 from by omega,
            show min (b' + 1) ((a' + 1) % (b' + 1)) = (a' + 1) % (b' + 1) from by omega] at ih'
        omega
    · -- ¬(b' + 1 ≤ a'): a ≤ b, so max = b, min = a
      rename_i h_lt
      rw [show max (a' + 1) (b' + 1) = b' + 1 from by omega,
          show min (a' + 1) (b' + 1) = a' + 1 from by omega,
          GCDAlgorithmOQ01.euclideanSteps_pos_eq _ _ (by omega)]
      -- euclideanSteps(b'+1, a'+1) unfolds to euclideanSteps(a'+1, (b'+1)%(a'+1)) + 1
      -- Goal: 1 + euclidSteps (a'+1) ((b'+1)%(a'+1)) = euclideanSteps (a'+1) ((b'+1)%(a'+1)) + 1
      have hmod_lt := Nat.mod_lt (b' + 1) (show a' + 1 > 0 by omega)
      by_cases hr : (b' + 1) % (a' + 1) = 0
      · rw [hr]; simp [euclidSteps, GCDAlgorithmOQ01.euclideanSteps]
      · have hr_pos : 0 < (b' + 1) % (a' + 1) := Nat.pos_of_ne_zero hr
        have ih' := ih (a' + 1) ((b' + 1) % (a' + 1)) (by omega) (by omega) hr_pos
        rw [show max (a' + 1) ((b' + 1) % (a' + 1)) = a' + 1 from by omega,
            show min (a' + 1) ((b' + 1) % (a' + 1)) = (b' + 1) % (a' + 1) from by omega] at ih'
        omega

/-- Lamé's bound: Euclidean steps ≤ 2 * log₂(min(a,b)) + 2. -/
theorem euclidSteps_le_log (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    euclidSteps a b ≤ 2 * Nat.log 2 (min a b) + 2 := by
  rw [euclidSteps_eq_ordered (a + b) a b le_rfl ha hb]
  exact GCDAlgorithmOQ01.euclideanSteps_log_bound (max a b) (min a b) (by omega)

/-! ## Binary GCD step bound -/

/-- Binary GCD steps ≤ 2 * (log₂(a) + log₂(b)) + 2.
    Each step reduces log₂ of at least one argument by ≥1. -/
theorem binaryGcdSteps_le_log (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    binaryGcdSteps a b ≤ 2 * (Nat.log 2 a + Nat.log 2 b) + 2 := by
  suffices h : ∀ n : ℕ, ∀ a b : ℕ, a + b ≤ n → 0 < a → 0 < b →
    binaryGcdSteps a b ≤ 2 * (Nat.log 2 a + Nat.log 2 b) + 2 from
    h (a + b) a b le_rfl ha hb
  intro n
  induction n with
  | zero => intro a b hab ha hb; omega
  | succ n ih =>
    intro a b hab ha hb
    obtain ⟨a', rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
    set la := Nat.log 2 (a' + 1) with hla_def
    set lb := Nat.log 2 (b' + 1) with hlb_def
    rw [binaryGcdSteps.eq_3]
    split
    · -- a'+1 even
      rename_i ha_even
      have hla1 : 1 ≤ la := Nat.log_pos (by omega) (by omega)
      split
      · -- both even
        rename_i hb_even
        have hlb1 : 1 ≤ lb := Nat.log_pos (by omega) (by omega)
        by_cases ha2 : (a' + 1) / 2 = 0; · omega
        by_cases hb2 : (b' + 1) / 2 = 0; · omega
        have ih' := ih ((a' + 1) / 2) ((b' + 1) / 2) (by omega) (by omega) (by omega)
        have : Nat.log 2 ((a' + 1) / 2) = la - 1 := by simp [hla_def, Nat.log_div_base]
        have : Nat.log 2 ((b' + 1) / 2) = lb - 1 := by simp [hlb_def, Nat.log_div_base]
        omega
      · -- a even, b odd
        by_cases ha2 : (a' + 1) / 2 = 0; · omega
        have ih' := ih ((a' + 1) / 2) (b' + 1) (by omega) (by omega) (by omega)
        have : Nat.log 2 ((a' + 1) / 2) = la - 1 := by simp [hla_def, Nat.log_div_base]
        omega
    · split
      · -- a odd, b even
        rename_i ha_odd hb_even
        have hlb1 : 1 ≤ lb := Nat.log_pos (by omega) (by omega)
        by_cases hb2 : (b' + 1) / 2 = 0; · omega
        have ih' := ih (a' + 1) ((b' + 1) / 2) (by omega) (by omega) (by omega)
        have : Nat.log 2 ((b' + 1) / 2) = lb - 1 := by simp [hlb_def, Nat.log_div_base]
        omega
      · split
        · -- both odd, a > b
          rename_i ha_odd hb_odd hgt
          have hla1 : 1 ≤ la := Nat.log_pos (by omega) (by omega)
          -- (a'+1-(b'+1)) is even ≥ 2 (odd - odd, positive diff)
          have hdiff_ge : 2 ≤ a' + 1 - (b' + 1) := by omega
          have hd_pos : 0 < (a' + 1 - (b' + 1)) / 2 := by omega
          have ih' := ih ((a' + 1 - (b' + 1)) / 2) (b' + 1) (by omega) hd_pos (by omega)
          -- (a-b)/2 ≤ a/2, so log((a-b)/2) ≤ log(a/2) = la - 1
          have hd_le : (a' + 1 - (b' + 1)) / 2 ≤ (a' + 1) / 2 := by omega
          have : Nat.log 2 ((a' + 1 - (b' + 1)) / 2) ≤ la - 1 := by
            calc Nat.log 2 ((a' + 1 - (b' + 1)) / 2)
                ≤ Nat.log 2 ((a' + 1) / 2) := Nat.log_mono_right hd_le
              _ = la - 1 := by simp [hla_def, Nat.log_div_base]
          omega
        · -- both odd, a ≤ b
          rename_i ha_odd hb_odd hle
          by_cases hd : (b' + 1 - (a' + 1)) / 2 = 0
          · -- a = b
            have heq : a' = b' := by omega
            subst heq
            have : (a' + 1 - (a' + 1)) / 2 = 0 := by omega
            rw [this, binaryGcdSteps_zero_right]; omega
          · have hlb1 : 1 ≤ lb := Nat.log_pos (by omega) (by omega)
            have hd_pos : 0 < (b' + 1 - (a' + 1)) / 2 := by omega
            have ih' := ih (a' + 1) ((b' + 1 - (a' + 1)) / 2) (by omega) (by omega) hd_pos
            have hd_le : (b' + 1 - (a' + 1)) / 2 ≤ (b' + 1) / 2 := by omega
            have : Nat.log 2 ((b' + 1 - (a' + 1)) / 2) ≤ lb - 1 := by
              calc Nat.log 2 ((b' + 1 - (a' + 1)) / 2)
                  ≤ Nat.log 2 ((b' + 1) / 2) := Nat.log_mono_right hd_le
                _ = lb - 1 := by simp [hlb_def, Nat.log_div_base]
            omega

/-! ## Summary

**Proved (0 axioms, 0 sorries):**
1. Step counting definitions for both algorithms
2. Concrete examples via native_decide
3. Lamé's theorem: Euclidean steps ≤ 2·log₂(min(a,b)) + 2
4. Binary GCD: steps ≤ 2·(log₂(a) + log₂(b)) + 2
-/

end BinaryGcdOQ01
