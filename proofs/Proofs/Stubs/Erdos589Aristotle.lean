/-
  Aristotle targets for Erdős Problem #589: Points in General Position
  Routine supporting lemmas for automated proof search.
  See Erdos589Problem.lean for the main formalization.

  This file provides routine supporting lemmas for the distinct
  general position subset problem.

  Key mathematical targets:
  1. nat_sqrt_le_rpow_half: (Nat.sqrt n : ℝ) ≤ n ^ (1/2 : ℝ)
     Needed for trivial_lower_bound in main file (Nat.sqrt ↔ Real.rpow bridge)
  2. collinear3_comm: symmetry of collinearity determinant
  3. collinear3_refl: every point is collinear with itself
  4. in_general_position_mono: general position is downward closed
  5. nat_sqrt_pos_of_pos: Nat.sqrt n > 0 when n ≥ 1
  6. rpow_half_nonneg: n ^ (1/2 : ℝ) ≥ 0

  Excluded (too deep for Aristotle):
  - erdos_belief_false (needs furedi_upper_bound contradiction structure)
  - trivial_lower_bound (depends on Nat.sqrt/greedy axiom structure)
  - g_kl definition sorry (definition sorry — Aristotle skips)
-/
import Mathlib

namespace Erdos589Aristotle

open Real

abbrev Point := ℝ × ℝ

/-- Three points are collinear if the signed-area determinant is zero -/
def Collinear3 (p q r : Point) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (r.1 - p.1) * (q.2 - p.2)

/-- A set of points is in general position if no three are collinear -/
def InGeneralPosition (S : Set Point) : Prop :=
  ∀ p q r : Point, p ∈ S → q ∈ S → r ∈ S →
    p ≠ q → q ≠ r → p ≠ r → ¬Collinear3 p q r

-- Routine: Collinear3 p p p holds (all differences vanish).
-- Strategy: simp [Collinear3] — both products become 0 * 0 = 0.
theorem collinear3_refl (p : Point) : Collinear3 p p p := by
  sorry

-- Routine: Collinear3 p q r ↔ Collinear3 q p r (swap first two points).
-- Strategy: unfold Collinear3 and use ring — the determinant formula is antisymmetric.
theorem collinear3_comm (p q r : Point) :
    Collinear3 p q r → Collinear3 q p r := by
  sorry

-- Routine: InGeneralPosition is monotone downward (subsets of gen-position sets are gen-position).
-- Strategy: intro h; apply S_gp; all subset assumptions follow from T ⊆ S.
theorem in_general_position_mono (S T : Set Point) (hST : T ⊆ S)
    (hS : InGeneralPosition S) : InGeneralPosition T := by
  sorry

-- Routine: The empty set is in general position (vacuously true).
-- Strategy: intro; exact absurd hp Set.not_mem_empty.
theorem in_general_position_empty : InGeneralPosition (∅ : Set Point) := by
  sorry

-- Routine: Any singleton is in general position.
-- Strategy: three elements from {p} all equal p, contradicting p ≠ q.
theorem in_general_position_singleton (p : Point) :
    InGeneralPosition ({p} : Set Point) := by
  sorry

-- Key bridge lemma: Nat.sqrt n ≤ (n : ℝ) ^ (1/2 : ℝ).
-- Strategy: Use Nat.sqrt_le_sqrt and Real.sqrt_eq_rpow combined with casts.
-- Nat.sqrt n ≤ ⌊√n⌋ + 1 and Nat.sqrt n ≤ √n (as real), √n = n^(1/2).
theorem nat_sqrt_le_rpow_half (n : ℕ) :
    (Nat.sqrt n : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
  sorry

-- Routine: Nat.sqrt n > 0 when n ≥ 1.
-- Strategy: Nat.sqrt_pos.mpr and Nat.cast_pos.
theorem nat_sqrt_pos_of_pos (n : ℕ) (hn : n ≥ 1) : (0 : ℝ) < Nat.sqrt n := by
  sorry

-- Routine: (n : ℝ) ^ (1/2 : ℝ) ≥ 0 for any n : ℕ.
-- Strategy: positivity (rpow of nonneg is nonneg).
theorem rpow_half_nonneg (n : ℕ) : (0 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
  sorry

end Erdos589Aristotle
