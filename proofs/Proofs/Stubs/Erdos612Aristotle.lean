/-
  Aristotle targets for Erdős Problem #612
  Routine supporting lemmas for automated proof search.
  See Erdos612Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open/disproved conjectures (OriginalConjecture1/2, AmendedConjecture)
  - NOT theorems depending on def-sorries (diameter)
  - Routine supporting facts: amended_alpha coefficient computations, basic graph properties
  - No definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos612Aristotle

open SimpleGraph

/-- The amended coefficient: (3 - 2/k) for K_{k+1}-free graphs. -/
noncomputable def amended_alpha (k : ℕ) : ℝ :=
  3 - 2 / k

/-- The coefficient for K_{2r}-free original conjecture. -/
noncomputable def alpha_2r (r : ℕ) : ℝ :=
  (2 * (r - 1) * (3 * r + 2)) / (2 * r^2 - 1)

/-- The coefficient for K_{2r+1}-free original conjecture. -/
noncomputable def alpha_2r1 (r : ℕ) : ℝ :=
  (3 * r - 1) / r

-- Routine: amended_alpha 2 = 2.
-- 3 - 2/2 = 3 - 1 = 2. Already proved in main file with simp + ring.
theorem amended_k2 : amended_alpha 2 = 2 := by
  simp [amended_alpha]
  ring

-- Routine: amended_alpha 3 = 7/3.
-- 3 - 2/3 = 7/3. Already proved in main file with simp + ring.
theorem amended_k3 : amended_alpha 3 = 7/3 := by
  simp [amended_alpha]
  ring

-- Routine: amended_alpha 4 = 5/2.
-- 3 - 2/4 = 3 - 1/2 = 5/2.
theorem amended_k4 : amended_alpha 4 = 5/2 := by
  sorry

-- Routine: amended_alpha 5 = 13/5.
-- 3 - 2/5 = 15/5 - 2/5 = 13/5.
theorem amended_k5 : amended_alpha 5 = 13/5 := by
  sorry

-- Routine: For k ≥ 2, amended_alpha k ≥ 2.
-- 3 - 2/k ≥ 2 iff 1 ≥ 2/k iff k ≥ 2.
theorem amended_alpha_ge_2 (k : ℕ) (hk : k ≥ 2) : amended_alpha k ≥ 2 := by
  sorry

-- Routine: For k ≥ 3, amended_alpha k > 2.
-- 3 - 2/k > 2 iff 1 > 2/k iff k > 2, i.e., k ≥ 3.
theorem amended_alpha_gt_2 (k : ℕ) (hk : k ≥ 3) : amended_alpha k > 2 := by
  sorry

-- Routine: For k ≥ 2, amended_alpha k < 3.
-- 3 - 2/k < 3 iff -2/k < 0, which holds since k > 0.
theorem amended_alpha_lt_3 (k : ℕ) (hk : k ≥ 2) : amended_alpha k < 3 := by
  sorry

-- Routine: For k ≥ 2, amended_alpha k > 0.
-- amended_alpha k ≥ 2 > 0 for k ≥ 2.
theorem amended_alpha_pos (k : ℕ) (hk : k ≥ 2) : amended_alpha k > 0 := by
  sorry

-- Routine: amended_alpha is increasing in k (for k ≥ 2).
-- amended_alpha k = 3 - 2/k; as k increases, 2/k decreases, so the expression increases.
theorem amended_alpha_mono (k₁ k₂ : ℕ) (hk₁ : k₁ ≥ 2) (h : k₁ ≤ k₂) :
    amended_alpha k₁ ≤ amended_alpha k₂ := by
  sorry

-- Routine: alpha_2r1 1 = 2.
-- (3*1 - 1)/1 = 2/1 = 2.
theorem alpha_2r1_one : alpha_2r1 1 = 2 := by
  sorry

-- Routine: alpha_2r1 2 = 5/2.
-- (3*2 - 1)/2 = 5/2.
theorem alpha_2r1_two : alpha_2r1 2 = 5/2 := by
  sorry

-- Routine: For r ≥ 1, alpha_2r1 r ≥ 2.
-- (3r - 1)/r = 3 - 1/r ≥ 3 - 1 = 2 when r ≥ 1.
theorem alpha_2r1_ge_2 (r : ℕ) (hr : r ≥ 1) : alpha_2r1 r ≥ 2 := by
  sorry

end Erdos612Aristotle
