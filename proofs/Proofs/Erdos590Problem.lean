/-
  Erdős Problem #590: Ordinal Ramsey Theory for ω^ω

  Source: https://erdosproblems.com/590
  Status: SOLVED (Chang 1972)
  Prize: $250 (paid)

  Statement:
  Let α = ω^ω. Is it true that in any red/blue coloring of the edges of K_α,
  there is either a red K_α or a blue K_3?

  Answer: YES — proved by Chang [Ch72]

  In arrow notation: ω^ω → (ω^ω, 3)²

  Background:
  - Specker [Sp57] proved this holds for α = ω²
  - Specker [Sp57] proved this FAILS for α = ω^n when 3 ≤ n < ω
  - Chang [Ch72] proved this holds for α = ω^ω (this problem)
  - Milner extended to K_m for any finite m; Larson [La73] gave a shorter proof

  References:
  [Ch72] Chang, "A partition theorem for the complete graph on ω^ω" (1972)
  [La73] Larson, "A short proof of a partition theorem for ω^ω" (1973/74)
  [Sp57] Specker, "Teilmengen von Mengen mit Relationen" (1957)

  Tags: set-theory, ramsey-theory, ordinals, combinatorics
-/

import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Erdos590

open Ordinal

/-! ## Part I: Ordinal Ramsey Theory Background -/

/-- The ordinal Ramsey property α → (β, n)²:
    Every 2-coloring of pairs from α contains either a monochromatic
    subset of order type β (color 1) or a monochromatic n-element set (color 2).

    We axiomatize this property since the full definition requires
    complex machinery involving order embeddings and colorings.
-/
axiom OrdinalRamseyProperty (α β : Ordinal.{0}) (n : ℕ) : Prop

/-- Notation for the arrow relation α → (β, n)². -/
notation:50 α " →ₒ (" β ", " n ")²" => OrdinalRamseyProperty α β n

/-! ## Part II: Specker's Results (1957) -/

/-- Specker's positive result: ω² → (ω², 3)² holds.

    Any 2-coloring of the complete graph on ω² vertices contains
    either a red copy of ω² or a blue triangle.
-/
axiom specker_omega_squared :
    (ω ^ 2) →ₒ (ω ^ 2, 3)²

/-- Specker's negative result: ω^n → (ω^n, 3)² FAILS for n ≥ 3.

    There exist 2-colorings of K_{ω^n} with no red K_{ω^n} and no blue K_3.
    This is surprising: larger ordinals can have worse Ramsey properties!
-/
axiom specker_omega_power_n_fails (n : ℕ) (hn : 3 ≤ n) :
    ¬ (ω ^ n) →ₒ (ω ^ n, 3)²

/-- Explicit failure for ω³. -/
theorem specker_omega_cubed_fails : ¬ (ω ^ 3) →ₒ (ω ^ 3, 3)² :=
  specker_omega_power_n_fails 3 (le_refl 3)

/-- Explicit failure for ω⁴. -/
theorem specker_omega_fourth_fails : ¬ (ω ^ 4) →ₒ (ω ^ 4, 3)² :=
  specker_omega_power_n_fails 4 (by norm_num)

/-! ## Part III: Chang's Theorem (1972) -/

/-- **Chang's Theorem (Erdős Problem #590, Prize: $250)**

    ω^ω → (ω^ω, 3)² holds.

    Despite the failure for all finite exponents n ≥ 3, the limit
    ordinal ω^ω restores the Ramsey property! This is the main result.

    Chang's proof appeared in J. Combinatorial Theory Ser. A (1972).
-/
axiom chang_omega_omega :
    (ω ^ ω) →ₒ (ω ^ ω, 3)²

/-- Erdős Problem #590 is solved: the answer is YES. -/
theorem erdos_590_solved : (ω ^ ω) →ₒ (ω ^ ω, 3)² := chang_omega_omega

/-! ## Part IV: Milner-Larson Extension -/

/-- Milner's extension: ω^ω → (ω^ω, m)² holds for ANY finite m.

    Not just triangles, but any finite clique size works!
    Larson (1973/74) gave a shorter proof of this result.
-/
axiom milner_larson_extension (m : ℕ) (hm : m ≥ 1) :
    (ω ^ ω) →ₒ (ω ^ ω, m)²

/-- Special case: ω^ω → (ω^ω, 4)². -/
theorem omega_omega_to_4 : (ω ^ ω) →ₒ (ω ^ ω, 4)² :=
  milner_larson_extension 4 (by norm_num)

/-- Special case: ω^ω → (ω^ω, 10)². -/
theorem omega_omega_to_10 : (ω ^ ω) →ₒ (ω ^ ω, 10)² :=
  milner_larson_extension 10 (by norm_num)

/-! ## Part V: The Ordinal Hierarchy -/

/-- ω is the first infinite ordinal, the order type of ℕ. -/
theorem omega_positive : 0 < ω := Ordinal.omega0_pos

/-- ω² = ω · ω is the order type of ℕ × ℕ (lexicographic). -/
theorem omega_squared_eq : ω ^ 2 = ω * ω := pow_two ω

/-- ω³ = ω · ω · ω. -/
theorem omega_cubed_eq : ω ^ 3 = ω * ω * ω := by
  rw [pow_succ, pow_two]

/-- ω^ω is the supremum of all ω^n for finite n.
    It's the first ordinal not reachable by finite exponentiation from ω. -/
theorem omega_omega_positive : 0 < ω ^ ω := by
  apply Ordinal.opow_pos
  exact Ordinal.omega0_pos

/-- ω^ω is a limit ordinal (not a successor). -/
theorem omega_omega_is_limit : (ω ^ ω).IsLimit := by
  apply Ordinal.isLimit_opow_left
  · exact Ordinal.omega0_isLimit
  · exact Ordinal.omega0_pos

/-- The sequence ω < ω² < ω³ < ... < ω^ω. -/
theorem omega_power_chain (n : ℕ) (hn : n ≥ 1) : ω ^ n < ω ^ ω := by
  apply Ordinal.opow_lt_opow_right
  · exact Ordinal.one_lt_omega0
  · exact Ordinal.nat_lt_omega0 n

/-! ## Part VI: The Pattern -/

/-- Summary of the Ramsey property α → (α, 3)²:

    | Ordinal α  | Property holds? | Reference |
    |------------|-----------------|-----------|
    | ω          | Yes             | Trivial   |
    | ω²         | Yes             | Specker   |
    | ω³         | No              | Specker   |
    | ω⁴         | No              | Specker   |
    | ...        | ...             | ...       |
    | ω^n (n≥3)  | No              | Specker   |
    | ω^ω        | Yes             | Chang     |
    | ω^(ω²)     | ?               | OPEN #591 |

    The pattern suggests that "limit" exponents might restore the property.
-/
theorem pattern_summary :
    -- ω² works
    (ω ^ 2) →ₒ (ω ^ 2, 3)² ∧
    -- ω³ fails
    ¬ (ω ^ 3) →ₒ (ω ^ 3, 3)² ∧
    -- ω^ω works
    (ω ^ ω) →ₒ (ω ^ ω, 3)² := by
  exact ⟨specker_omega_squared, specker_omega_cubed_fails, chang_omega_omega⟩

/-! ## Part VII: Connection to Related Problems -/

/-- Problem #591 asks about the next case: ω^(ω²) → (ω^(ω²), 3)².
    This remains OPEN with a $250 prize. -/
def problem_591_conjecture : Prop :=
  (ω ^ (ω ^ 2)) →ₒ (ω ^ (ω ^ 2), 3)²

/-- Problem #592 asks about even larger ordinals.
    The pattern continues to be investigated. -/
def problem_592_related : Prop :=
  ∀ α : Ordinal, α.IsLimit → (ω ^ α) →ₒ (ω ^ α, 3)²

/-! ## Part VIII: Ordinal Arithmetic Identities -/

/-- ω^ω is strictly larger than any ω^n. -/
theorem omega_omega_dominates (n : ℕ) : ω ^ n < ω ^ ω := by
  cases n with
  | zero =>
    simp only [pow_zero]
    apply Ordinal.one_lt_opow
    · exact Ordinal.one_lt_omega0
    · exact Ordinal.omega0_pos
  | succ m =>
    apply omega_power_chain (m + 1) (Nat.succ_pos m)

/-- ω^ω · ω^ω = ω^(ω + ω) = ω^(ω · 2). -/
theorem omega_omega_squared_form :
    ω ^ ω * ω ^ ω = ω ^ (ω + ω) := by
  rw [← Ordinal.opow_add]

end Erdos590

/-!
## Summary

This file formalizes Erdős Problem #590 on ordinal Ramsey theory for ω^ω.

**Status**: SOLVED (Chang 1972, Prize $250)

**The Problem**: Does ω^ω → (ω^ω, 3)² hold?
That is, must every 2-coloring of K_{ω^ω} contain a red K_{ω^ω} or a blue K_3?

**Answer**: YES (Chang 1972)

**Historical Context**:
- Specker (1957): ω² → (ω², 3)² holds
- Specker (1957): ω^n → (ω^n, 3)² FAILS for n ≥ 3
- Chang (1972): ω^ω → (ω^ω, 3)² holds (this problem)
- Milner/Larson: ω^ω → (ω^ω, m)² holds for all finite m

**The Surprising Pattern**:
The Ramsey property fails for ω³, ω⁴, ... (all finite exponents ≥ 3),
but is restored for the limit ordinal ω^ω. This suggests limit exponents
might generally restore the property.

**What we formalize**:
1. The ordinal Ramsey property α → (α, n)²
2. Specker's positive (ω²) and negative (ω^n) results
3. Chang's main theorem for ω^ω
4. Milner-Larson extension to arbitrary finite m
5. Ordinal arithmetic identities
6. Connection to Problem #591 (ω^(ω²), OPEN)

**Key axioms**:
- `specker_omega_squared`: The base case ω² works
- `specker_omega_power_n_fails`: The failure cases ω^n (n ≥ 3)
- `chang_omega_omega`: The main result - ω^ω works
- `milner_larson_extension`: Generalization to any finite m
-/
