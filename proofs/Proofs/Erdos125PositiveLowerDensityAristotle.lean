/-
  Aristotle targets for Erdős Problem #125 (positive_lower_density variant):
  Routine supporting lemmas for automated proof search.
  See Erdos125PositiveLowerDensity.lean for the main formalization.

  Context: the positive_lower_density variant was resolved in the negative by
  DeepMind's AlphaProof Nexus (2026-05-21, arXiv:2605.22763v1): the sumset
  C = A + B has lower density 0. The main file states the supporting lemmas
  with `sorry` because the AlphaProof tactic proofs do not port cleanly to a
  pure Mathlib setup.

  Criteria for inclusion:
  - NOT the main result (AB_lowerDensity_eq_zero) and NOT the deep analytic
    machinery (irrationality of log 4 / log 3, Dirichlet approximation,
    the multi-scale density scale_step).
  - Routine digit-combinatorics facts about the base-3 / base-4 digit-restricted
    sets A and B and their pointwise sumset A + B.
  - No axioms, no definition sorries, no open conjectures.
  - Block comments only, never module docstrings.
-/
import Mathlib

namespace Erdos125Aristotle

open Nat Pointwise

/-
## Section 1: Digit-restricted sets A and B

A = naturals whose base-3 digits are all 0 or 1.
B = naturals whose base-4 digits are all 0 or 1.
These mirror the definitions in Erdos125PositiveLowerDensity.lean.
-/

/-- `A` = naturals whose base-3 digits are all `0` or `1`. -/
def A : Set ℕ := { x : ℕ | (Nat.digits 3 x).toFinset ⊆ {0, 1} }

/-- `B` = naturals whose base-4 digits are all `0` or `1`. -/
def B : Set ℕ := { x : ℕ | (Nat.digits 4 x).toFinset ⊆ {0, 1} }

/-
## Section 2: Membership anchors (proved)

Trivial membership facts that pin down the API of A, B, and A + B.
-/

/-- `0 ∈ A`. -/
theorem zero_in_A : 0 ∈ A := by
  simp [A]

/-- `0 ∈ B`. -/
theorem zero_in_B : 0 ∈ B := by
  simp [B]

/-- `0 ∈ A + B`. -/
theorem zero_in_A_plus_B : 0 ∈ A + B := by
  refine ⟨0, zero_in_A, 0, zero_in_B, ?_⟩
  simp

/-
## Section 3: Routine digit-combinatorics targets

These are the supporting lemmas the AlphaProof Nexus proof establishes about
the digit-restricted sets. Their statements are copied verbatim from the main
file; their proofs are left for automated search.
-/

/-- If `x < 3^k` and `x ∈ A` then `x ≤ (3^k - 1) / 2`. -/
theorem A_max_k (k x : ℕ) (hx : x < 3 ^ k) (hA : x ∈ A) : x ≤ (3 ^ k - 1) / 2 := by
  sorry

/-- If `y < 4^m` and `y ∈ B` then `y ≤ (4^m - 1) / 3`. -/
theorem B_max_m (m y : ℕ) (hy : y < 4 ^ m) (hB : y ∈ B) : y ≤ (4 ^ m - 1) / 3 := by
  sorry

/--
**Gap lemma.** If `(3^k - 1)/2 + (4^m - 1)/3 < x`, `x < 3^k`, and `x < 4^m`,
then `x ∉ A + B`.
-/
theorem A_B_gap (k m x : ℕ)
    (hx_gt : (3 ^ k - 1) / 2 + (4 ^ m - 1) / 3 < x)
    (hx_lt_A : x < 3 ^ k) (hx_lt_B : x < 4 ^ m) : x ∉ A + B := by
  sorry

/-- Decomposition: every `a ∈ A` factors as `a = a₁ · 3^k + a₀` with both pieces in `A`. -/
theorem A_decomp (k a : ℕ) (ha : a ∈ A) :
    ∃ a1 a0 : ℕ, a1 ∈ A ∧ a0 ∈ A ∧ a0 < 3 ^ k ∧ a = a1 * 3 ^ k + a0 := by
  sorry

/-- Decomposition: every `b ∈ B` factors as `b = b₁ · 4^m + b₀` with both pieces in `B`. -/
theorem B_decomp (m b : ℕ) (hb : b ∈ B) :
    ∃ b1 b0 : ℕ, b1 ∈ B ∧ b0 ∈ B ∧ b0 < 4 ^ m ∧ b = b1 * 4 ^ m + b0 := by
  sorry

/-
## Section 4: Algebraic identity (proved)

A self-contained Nat identity used in the scale-step rearrangement.
-/

/-- Algebraic identity used in the scale-step. -/
theorem hz_eq_lemma (x a b a1 a0 b1 b0 k m : ℕ)
    (h1 : 3 ^ k ≤ 4 ^ m) (h3 : x = a + b)
    (h4 : a = a1 * 3 ^ k + a0) (h5 : b = b1 * 4 ^ m + b0) :
    x = (a1 + b1) * 3 ^ k + (a0 + b0 + b1 * (4 ^ m - 3 ^ k)) := by
  have h2 : 4 ^ m = 3 ^ k + (4 ^ m - 3 ^ k) := by omega
  have h6 : b1 * 4 ^ m = b1 * 3 ^ k + b1 * (4 ^ m - 3 ^ k) := by
    calc
      b1 * 4 ^ m = b1 * (3 ^ k + (4 ^ m - 3 ^ k)) := congrArg (b1 * ·) h2
      _ = b1 * 3 ^ k + b1 * (4 ^ m - 3 ^ k) := Nat.mul_add b1 _ _
  have h7 : (a1 + b1) * 3 ^ k = a1 * 3 ^ k + b1 * 3 ^ k := Nat.add_mul a1 b1 _
  omega

end Erdos125Aristotle
