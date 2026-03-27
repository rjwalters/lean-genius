/-
# S₂, S₃, S₄ Are Solvable (Abel-Ruffini OQ-04-OQ-02)

Open Question from abel-ruffini-oq-04:
"Prove S₂, S₃, S₄ solvable explicitly (not just S₀, S₁)
to complete the degree-by-degree picture."

Answer: YES. All three are solvable.

**S₂** (order 2): Commutative (abelian), hence solvable.
  Derived series: S₂ ⊵ {e}  (1 step)

**S₃** (order 6): Solvable via A₃.
  Derived series: S₃ ⊵ A₃ ⊵ {e}  (2 steps)
  A₃ ≅ ℤ/3ℤ is abelian, S₃/A₃ ≅ ℤ/2ℤ is abelian.

**S₄** (order 24): Solvable via the chain S₄ ⊵ A₄ ⊵ V₄ ⊵ {e}.
  V₄ = {e, (12)(34), (13)(24), (14)(23)} is the Klein four-group (abelian).
  Each quotient in the chain is abelian.

Together with AbelRuffiniOQ04.lean (S₅ not solvable), this gives the
complete picture: Sₙ is solvable iff n ≤ 4.

The proofs use:
- S₂: CommGroup instance (decide verifies commutativity)
- S₃, S₄: Mathlib's IsSolvable decidability for finite groups

References:
- Hungerford, "Algebra" (1974), §II.8
- Mathlib: GroupTheory.Solvable, GroupTheory.SpecificGroups.Alternating
-/

import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

open Equiv

namespace AbelRuffiniOQ04OQ02

-- ============================================================
-- PART 1: S₂ Is Solvable (Abelian)
-- ============================================================

/-- S₂ is commutative: all permutations of {0, 1} commute.
    |S₂| = 2, so it's isomorphic to ℤ/2ℤ. -/
instance s2_comm : CommGroup (Perm (Fin 2)) where
  mul_comm := by decide

/-- S₂ is solvable (abelian groups are solvable). -/
theorem s2_solvable : IsSolvable (Perm (Fin 2)) := inferInstance

-- ============================================================
-- PART 2: S₃ Is Solvable
-- ============================================================

/-- S₃ is solvable (order 6).
    Derived series: S₃ ⊵ A₃ ≅ ℤ/3ℤ ⊵ {e}. Both quotients are abelian. -/
theorem s3_solvable : IsSolvable (Perm (Fin 3)) := by
  -- S₃ has 6 elements; we can verify solvability computationally
  -- The derived subgroup [S₃, S₃] = A₃ (cyclic of order 3)
  -- [A₃, A₃] = {e} (A₃ is abelian)
  -- So derivedSeries 2 = ⊥
  rw [isSolvable_def]
  exact ⟨2, by decide⟩

-- ============================================================
-- PART 3: S₄ Is Solvable
-- ============================================================

/-- S₄ is solvable (order 24).
    Derived series: S₄ ⊵ A₄ ⊵ V₄ ⊵ {e}. (3 steps)
    V₄ = {e, (12)(34), (13)(24), (14)(23)} is the Klein four-group. -/
theorem s4_solvable : IsSolvable (Perm (Fin 4)) := by
  -- S₄ has 24 elements; computationally verify solvability
  -- derivedSeries 3 = ⊥
  rw [isSolvable_def]
  exact ⟨3, by native_decide⟩

-- ============================================================
-- PART 4: The Complete Classification
-- ============================================================

/-- **Sₙ is solvable iff n ≤ 4**: The exact solvability threshold.
    This combines the results from this file (n ≤ 4) with
    AbelRuffiniOQ04.lean (n ≥ 5 not solvable). -/
theorem solvable_iff_le_four (n : ℕ) :
    IsSolvable (Perm (Fin n)) ↔ n ≤ 4 := by
  constructor
  · -- If solvable, then n ≤ 4 (contrapositive of n ≥ 5 → not solvable)
    intro h
    by_contra h_gt
    push_neg at h_gt
    have h5 : 5 ≤ n := by omega
    have h_card : 5 ≤ Cardinal.mk (Fin n) := by
      simp only [Cardinal.mk_fintype, Fintype.card_fin]
      exact_mod_cast h5
    exact Equiv.Perm.not_solvable (Fin n) h_card h
  · -- If n ≤ 4, then solvable (case split on n = 0, 1, 2, 3, 4)
    intro h
    interval_cases n
    · exact inferInstance  -- S₀
    · exact inferInstance  -- S₁
    · exact s2_solvable    -- S₂
    · exact s3_solvable    -- S₃
    · exact s4_solvable    -- S₄

-- ============================================================
-- PART 5: Degree-by-Degree Picture
-- ============================================================

/-- For degrees 1-4, the symmetric group is solvable.
    Combined with the Galois theory bridge, this explains why
    polynomial equations of degree ≤ 4 are solvable by radicals. -/
theorem small_symmetric_solvable (n : ℕ) (hn : n ≤ 4) :
    IsSolvable (Perm (Fin n)) :=
  (solvable_iff_le_four n).mpr hn

/-- For degree ≥ 5, the symmetric group is NOT solvable.
    Combined with the Galois theory bridge, this explains why
    no general radical formula exists for degree ≥ 5. -/
theorem large_symmetric_not_solvable (n : ℕ) (hn : 5 ≤ n) :
    ¬IsSolvable (Perm (Fin n)) :=
  fun h => absurd h ((solvable_iff_le_four n).not.mpr (by omega))

-- ============================================================
-- Summary
-- ============================================================

/-
## Complete Solvability Classification for Symmetric Groups

| n | |Sₙ| | Solvable? | Derived Series Length | Proof |
|---|------|-----------|----------------------|-------|
| 0 | 1   | Yes ✓     | 0 (trivial)          | inferInstance |
| 1 | 1   | Yes ✓     | 0 (trivial)          | inferInstance |
| 2 | 2   | Yes ✓     | 1 (S₂ abelian)       | CommGroup + decide |
| 3 | 6   | Yes ✓     | 2 (S₃ ⊵ A₃ ⊵ {e})   | decide |
| 4 | 24  | Yes ✓     | 3 (S₄ ⊵ A₄ ⊵ V₄ ⊵ {e}) | native_decide |
| ≥5| ≥120| **No** ✗  | ∞ (stuck at Aₙ)     | Equiv.Perm.not_solvable |

**Why 5?** A₅ is the smallest non-abelian simple group (order 60).
Its derived series is A₅ = [A₅, A₅], which never reaches {e}.
For n < 5, all composition factors are cyclic of prime order.

This file proves Sₙ solvable for n ≤ 4, and `solvable_iff_le_four`
gives the complete bidirectional classification.
-/

end AbelRuffiniOQ04OQ02
