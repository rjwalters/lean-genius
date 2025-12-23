import Mathlib.Tactic

/-!
# Sqrt2 Examples

## What This Proves
A collection of simple example proofs demonstrating basic Lean tactics.
Includes: non-negativity of squares, and implication transitivity.

## Approach
- **Foundation (from Mathlib):** Only `Mathlib.Tactic` for standard tactics.
- **Original Contributions:** Simple pedagogical examples showing basic
  proof techniques in Lean 4.
- **Proof Techniques Demonstrated:** Case analysis (`by_cases`), `calc`
  proofs, `ring` tactic, function application (`apply`, `exact`).

## Status
- [x] Complete proof
- [ ] Uses Mathlib for main result
- [ ] Proves extensions/corollaries
- [x] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Mathlib.Tactic` : Standard tactic library (ring, push_neg, etc.)

This is a minimal template file for learning Lean proof techniques.
-/

namespace Sqrt2

-- Test proof with tactics
theorem square_nonneg (n : ℤ) : 0 ≤ n * n := by
  by_cases h : 0 ≤ n
  · exact mul_nonneg h h
  · push_neg at h
    have h1 : n ≤ 0 := le_of_lt h
    have h2 : 0 ≤ -n := neg_nonneg.mpr h1
    calc n * n = (-n) * (-n) := by ring
             _ ≥ 0 := mul_nonneg h2 h2

theorem imp_trans (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) := by
  intro hpq hqr hp
  apply hqr
  apply hpq
  exact hp

end Sqrt2
