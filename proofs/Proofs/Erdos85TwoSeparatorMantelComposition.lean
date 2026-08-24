import Proofs.Erdos85TwoSeparatorLowSetEdgeUpper
import Proofs.Erdos85MinimumDefectCutNearMantelArithmetic

/-!
# Composing the two-separator Mantel bounds

The graph-facing wrappers naturally return two split parts whose sizes add
to `q-1`.  This small endpoint converts that existential form to the
arithmetic contradiction.
-/

namespace Erdos85

/-- An even `(q-1)`-vertex split upper bound is incompatible with the
near-Mantel lower bound. -/
theorem false_of_even_exists_split_edge_upper_and_nearMantel_lower
    (q e : ℕ) (hq : 8 ≤ q) (heven : Even q)
    (hsplit : ∃ p t : ℕ, p + t = q - 1 ∧ e ≤ p * t)
    (hlower : q * q - 4 ≤ 4 * e) : False := by
  obtain ⟨p, t, hsum, hu⟩ := hsplit
  have hp : p ≤ q - 1 := by omega
  have ht : t = q - 1 - p := by omega
  rw [ht] at hu
  exact false_of_even_split_edge_upper_and_nearMantel_lower
    q p e hq heven hp hu hlower

end Erdos85

#print axioms Erdos85.false_of_even_exists_split_edge_upper_and_nearMantel_lower
