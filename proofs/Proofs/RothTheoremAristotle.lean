/-
  Aristotle targets for Roth's Theorem (roth-theorem-k3)
  Routine supporting lemmas for automated proof search.
  See RothTheorem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely in Mathlib (norm bounds, Parseval, etc.)
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)
-/
import Mathlib

namespace Szemeredi.Roth.Aristotle

-- ═══════════════════════════════════════════════════════════════════
-- Fourier coefficient bounds
-- ═══════════════════════════════════════════════════════════════════

/-- Fourier coefficient definition (duplicated for self-containment). -/
noncomputable def fourierCoeff {N : ℕ} (A : Finset (ZMod N)) (r : ZMod N) : ℂ :=
  A.sum fun x => Complex.exp (2 * Real.pi * Complex.I * (↑(ZMod.val (r * x)) / ↑N))

/-- Each exponential term in the Fourier coefficient has norm 1.
    exp(2πi·θ) lies on the unit circle for real θ. -/
theorem exp_term_norm_one {N : ℕ} (r x : ZMod N) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (↑(ZMod.val (r * x)) / ↑N))‖ = 1 := by
  sorry

/-- The Fourier coefficient at r is bounded by |A| (triangle inequality). -/
theorem fourierCoeff_norm_le {N : ℕ} (A : Finset (ZMod N)) (r : ZMod N) :
    ‖fourierCoeff A r‖ ≤ A.card := by
  sorry

/-- Cardinality of any subset of ZMod N is at most N. -/
theorem card_le_zmod {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    A.card ≤ N := by
  sorry

/-- Cardinality bound in ℝ: (A.card : ℝ) ≤ N. -/
theorem card_le_zmod_real {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    (A.card : ℝ) ≤ (N : ℝ) := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- Basic ZMod arithmetic for AP arguments
-- ═══════════════════════════════════════════════════════════════════

/-- If a + d = a then d = 0 in any additive group. -/
theorem add_right_eq_self {G : Type*} [AddGroup G] (a d : G) :
    a + d = a → d = 0 := by
  sorry

/-- In ZMod N with N ≥ 2, there exist distinct elements. -/
theorem zmod_nontrivial {N : ℕ} (hN : 2 ≤ N) :
    ∃ a b : ZMod N, a ≠ b := by
  sorry

end Szemeredi.Roth.Aristotle
