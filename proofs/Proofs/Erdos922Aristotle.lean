/-
  Aristotle targets for Erdős Problem #922 (Folkman's Chromatic Number Bound)
  Routine supporting lemmas for automated proof search.
  See Erdos922Problem.lean for the main formalization.

  Criteria for inclusion:
  - bipartite_chromatic_le_two: IsBipartite → chromaticNumber ≤ 2 (Mathlib)
  - ratio_ge_of_two_card_bound: rational arithmetic from Folkman density bound
  - NOT chromaticNumber' definition sorry (definition sorry, line 65)
  - NOT folkman_zero_implies_bipartite (complex structural argument)
  - NOT folkman_theorem (deep result, axiomatized)
-/
import Mathlib

namespace Erdos922Aristotle

open SimpleGraph

-- Routine: A bipartite graph has chromatic number ≤ 2.
-- Bipartite means Colorable 2, and Colorable n → chromaticNumber ≤ n.
theorem bipartite_chromatic_le_two {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hbip : G.IsBipartite) :
    G.chromaticNumber ≤ 2 := hbip.chromaticNumber_le

-- Routine: Rational arithmetic for the Folkman density bound.
-- Given 2 * S ≥ W - k in ℕ (natural subtraction) and W > 0,
-- show (S : ℚ) / W ≥ ((W : ℚ) - k) / (2 * W).
-- Key: cast the hypothesis to ℚ and use field_simp + linarith.
theorem ratio_ge_of_two_card_bound (S W k : ℕ) (hW : 0 < W)
    (h : 2 * S ≥ W - k) :
    (S : ℚ) / W ≥ ((W : ℚ) - k) / (2 * W) := by
  have hWQ : (0 : ℚ) < W := by exact_mod_cast hW
  rw [ge_iff_le, div_le_div_iff (by positivity) hWQ]
  -- (W - k) * W ≤ S * (2 * W) follows from (W - k : ℚ) ≤ 2 * S
  have hkey : (W : ℚ) - k ≤ 2 * S := by
    rcases Nat.le_or_lt k W with hle | hlt
    · have h1 : ((W - k : ℕ) : ℚ) ≤ 2 * S := by exact_mod_cast h
      rwa [Nat.cast_sub hle] at h1
    · have hWkQ : (W : ℚ) - k ≤ 0 := by
        have : (W : ℚ) ≤ k := by exact_mod_cast hlt.le
        linarith
      linarith [show (0 : ℚ) ≤ 2 * S from by positivity]
  nlinarith

end Erdos922Aristotle
