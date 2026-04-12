/-
# Alternating Groups: Aₙ Solvable iff n ≤ 4 (Abel-Ruffini OQ-04-OQ-02-OQ-02)

Open Question from abel-ruffini-oq-04-oq-02:
"Prove alternating groups: A_n solvable iff n ≤ 4"

## Answer: YES. The complete classification is:

| n | |Aₙ| | Solvable? | Reason |
|---|------|-----------|--------|
| 0 | 1   | Yes ✓     | Trivial group |
| 1 | 1   | Yes ✓     | Trivial group |
| 2 | 1   | Yes ✓     | Trivial group |
| 3 | 3   | Yes ✓     | A₃ ≅ ℤ/3ℤ (abelian) |
| 4 | 12  | Yes ✓     | A₄ ⊵ V₄ ⊵ {e}, V₄ ≅ ℤ/2ℤ × ℤ/2ℤ |
| ≥5| ≥60 | **No** ✗  | A₅ simple, non-abelian |

## Key Argument

**Solvable direction (n ≤ 4):**
- A₀, A₁, A₂ are trivial (order 1): trivially solvable
- A₃ ≅ ℤ/3ℤ is abelian: solvable
- A₄ ≤ S₄ is solvable as a subgroup of the solvable group S₄

**Non-solvable direction (n ≥ 5):**
- If Aₙ were solvable, the short exact sequence 1 → Aₙ → Sₙ → ℤˣ → 1
  would make Sₙ solvable (via `solvable_of_ker_le_range`).
- But Mathlib proves Sₙ is NOT solvable for n ≥ 5 (`Equiv.Perm.not_solvable`).
- Contradiction: so Aₙ is not solvable for n ≥ 5.

## The Exact Threshold

The threshold n = 5 reflects that A₅ is the smallest non-abelian simple group (order 60).
For n < 5, all composition factors are cyclic of prime order.
For n ≥ 5, A₅ embeds in Aₙ and provides a non-solvable section.

References:
- Hungerford, "Algebra" (1974), §II.7
- Lang, "Algebra" (3rd ed.), §I.8
- Mathlib: GroupTheory.Solvable, GroupTheory.SpecificGroups.Alternating
-/

import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

open Equiv

namespace AbelRuffiniOQ04OQ02OQ02

-- ============================================================
-- PART 1: Small Alternating Groups Are Solvable (n ≤ 4)
-- ============================================================

/-- A₀ is solvable (trivial group). -/
theorem a0_solvable : IsSolvable (alternatingGroup (Fin 0)) := inferInstance

/-- A₁ is solvable (trivial group). -/
theorem a1_solvable : IsSolvable (alternatingGroup (Fin 1)) := inferInstance

/-- A₂ is solvable (trivial group). -/
theorem a2_solvable : IsSolvable (alternatingGroup (Fin 2)) := inferInstance

/-- A₃ is solvable. A₃ ≅ ℤ/3ℤ is abelian (cyclic of order 3). -/
theorem a3_solvable : IsSolvable (alternatingGroup (Fin 3)) := by
  apply isSolvable_of_comm
  decide

/-- A₄ is solvable. It is a subgroup of the solvable group S₄.
    S₄ is solvable (derived series length 3: S₄ ⊵ A₄ ⊵ V₄ ⊵ {e}). -/
theorem a4_solvable : IsSolvable (alternatingGroup (Fin 4)) := by
  -- S₄ is solvable (Mathlib knows this via native_decide)
  have hs4 : IsSolvable (Perm (Fin 4)) := by
    rw [isSolvable_def]; exact ⟨3, by native_decide⟩
  -- Subgroup of a solvable group is solvable
  exact inferInstance

-- ============================================================
-- PART 2: Large Alternating Groups Are NOT Solvable (n ≥ 5)
-- ============================================================

/-- If Aₙ is solvable, then Sₙ is solvable.
    Proof via the short exact sequence 1 → Aₙ → Sₙ → ℤˣ → 1:
    solvability of kernel (Aₙ) and quotient (ℤˣ ≅ ℤ/2ℤ) implies solvability of Sₙ. -/
private theorem sn_solvable_of_an_solvable {n : ℕ} (h : IsSolvable (alternatingGroup (Fin n))) :
    IsSolvable (Perm (Fin n)) := by
  apply solvable_of_ker_le_range (alternatingGroup (Fin n)).subtype Perm.sign
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  exact ⟨⟨x, Perm.mem_alternatingGroup.mpr hx⟩, rfl⟩

/-- Sₙ is NOT solvable for n ≥ 5 (Mathlib: `Equiv.Perm.not_solvable`).
    This follows because S₅ is not solvable and Sₙ contains S₅ for n ≥ 5. -/
private theorem sn_not_solvable {n : ℕ} (hn : 5 ≤ n) : ¬IsSolvable (Perm (Fin n)) := by
  have h : 5 ≤ Cardinal.mk (Fin n) := by
    simp only [Cardinal.mk_fintype, Fintype.card_fin]; exact_mod_cast hn
  exact Perm.not_solvable (Fin n) h

/-- Aₙ is NOT solvable for n ≥ 5.
    Proof: If Aₙ were solvable, sn_solvable_of_an_solvable gives Sₙ solvable,
    contradicting sn_not_solvable. -/
theorem an_not_solvable_of_ge_five {n : ℕ} (hn : 5 ≤ n) :
    ¬IsSolvable (alternatingGroup (Fin n)) := by
  intro h
  exact sn_not_solvable hn (sn_solvable_of_an_solvable h)

-- ============================================================
-- PART 3: The Complete Classification
-- ============================================================

/-- **Main Theorem**: Aₙ is solvable if and only if n ≤ 4.

    This is the alternating-group analogue of the classical result for
    symmetric groups (Sₙ solvable iff n ≤ 4). Both families share the
    same sharp threshold at n = 5, because:
    - A₅ is the smallest non-abelian simple group
    - Solvability is inherited by subgroups, so A₅ ≤ Aₙ (n ≥ 5) prevents solvability
    - For n ≤ 4, the composition series has only cyclic factors -/
theorem alternating_solvable_iff (n : ℕ) :
    IsSolvable (alternatingGroup (Fin n)) ↔ n ≤ 4 := by
  constructor
  · -- (→) If Aₙ solvable, then n ≤ 4
    intro h
    by_contra hlt
    push_neg at hlt
    exact an_not_solvable_of_ge_five (by omega) h
  · -- (←) If n ≤ 4, then Aₙ solvable
    intro hn
    interval_cases n
    · exact a0_solvable
    · exact a1_solvable
    · exact a2_solvable
    · exact a3_solvable
    · exact a4_solvable

-- ============================================================
-- PART 4: Corollaries and Named Instances
-- ============================================================

/-- A₅ is NOT solvable. (The base case of non-solvability.) -/
theorem a5_not_solvable : ¬IsSolvable (alternatingGroup (Fin 5)) :=
  an_not_solvable_of_ge_five (le_refl 5)

/-- A₆ is NOT solvable. -/
theorem a6_not_solvable : ¬IsSolvable (alternatingGroup (Fin 6)) :=
  an_not_solvable_of_ge_five (by norm_num)

/-- For any n ≤ 4, Aₙ is solvable. -/
theorem alternating_solvable_of_le_four {n : ℕ} (hn : n ≤ 4) :
    IsSolvable (alternatingGroup (Fin n)) :=
  (alternating_solvable_iff n).mpr hn

/-- For any n ≥ 5, Aₙ is NOT solvable. -/
theorem alternating_not_solvable_of_ge_five {n : ℕ} (hn : 5 ≤ n) :
    ¬IsSolvable (alternatingGroup (Fin n)) :=
  an_not_solvable_of_ge_five hn

/-- The threshold is sharp: A₄ IS solvable but A₅ is NOT. -/
theorem sharp_threshold :
    IsSolvable (alternatingGroup (Fin 4)) ∧ ¬IsSolvable (alternatingGroup (Fin 5)) :=
  ⟨a4_solvable, a5_not_solvable⟩

end AbelRuffiniOQ04OQ02OQ02
