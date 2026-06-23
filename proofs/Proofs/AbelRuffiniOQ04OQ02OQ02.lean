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

/-- A₂ is solvable (trivial group, hence commutative). -/
theorem a2_solvable : IsSolvable (alternatingGroup (Fin 2)) := by
  apply isSolvable_of_comm
  decide

/-- A₃ is solvable. A₃ ≅ ℤ/3ℤ is abelian (cyclic of order 3). -/
theorem a3_solvable : IsSolvable (alternatingGroup (Fin 3)) := by
  apply isSolvable_of_comm
  decide

/-! ### A₄ is solvable, via its Klein four commutator subgroup

The previous proof discharged `derivedSeries (Perm (Fin 4)) 3 = ⊥` with
`native_decide`, relying on a `Decidable (derivedSeries … = ⊥)` instance that
current Mathlib no longer provides (subgroup equality of commutator closures is
not decidable by instance). We instead give a structural, `native_decide`-free
proof: the commutator subgroup of A₄ is contained in the Klein four-group
`V₄ = {g | g² = 1}`, which is abelian, so the second derived subgroup is trivial.
All `decide` calls below range over A₄ (12 elements) checking element-level
identities — no closure decidability is required. -/

/-- `V₄ ⊴ A₄`: the elements of order dividing two — the identity together with the
three double transpositions `(ab)(cd)`. (In A₄ every order-2 element is a product
of two disjoint transpositions, since single transpositions are odd.) -/
def A4V4 : Subgroup (alternatingGroup (Fin 4)) where
  carrier := {g | g ^ 2 = 1}
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

instance : DecidablePred (· ∈ A4V4) := fun x => inferInstanceAs (Decidable (x ^ 2 = 1))

set_option maxRecDepth 4000 in
/-- The commutator subgroup of A₄ is contained in the Klein four-group `V₄`:
every generator `⁅a, b⁆` has order dividing two. -/
theorem commutator_le_A4V4 : commutator (alternatingGroup (Fin 4)) ≤ A4V4 := by
  rw [commutator_def, Subgroup.commutator_le]
  simp only [Subgroup.mem_top, true_implies]
  decide

set_option maxRecDepth 4000 in
/-- `V₄` is abelian. -/
theorem A4V4_comm : ∀ a ∈ A4V4, ∀ b ∈ A4V4, b * a = a * b := by decide

/-- `⁅V₄, V₄⁆ = ⊥` since `V₄` is abelian. -/
theorem commutator_A4V4_eq_bot : ⁅A4V4, A4V4⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact A4V4_comm a ha b hb

/-- **A₄ has derived length exactly 2.** The second derived subgroup is trivial:
`D²(A₄) = ⁅[A₄,A₄], [A₄,A₄]⁆ ≤ ⁅V₄, V₄⁆ = ⊥`. -/
theorem a4_derivedSeries_two_eq_bot :
    derivedSeries (alternatingGroup (Fin 4)) 2 = ⊥ := by
  have h2 : derivedSeries (alternatingGroup (Fin 4)) 2
      = ⁅commutator (alternatingGroup (Fin 4)), commutator (alternatingGroup (Fin 4))⁆ := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, derivedSeries_succ, derivedSeries_one]
  rw [h2]
  refine le_bot_iff.mp ?_
  calc ⁅commutator (alternatingGroup (Fin 4)), commutator (alternatingGroup (Fin 4))⁆
      ≤ ⁅A4V4, A4V4⁆ := Subgroup.commutator_mono commutator_le_A4V4 commutator_le_A4V4
    _ = ⊥ := commutator_A4V4_eq_bot

/-- A₄ is solvable (derived length 2: A₄ ⊵ V₄ ⊵ {e}). -/
theorem a4_solvable : IsSolvable (alternatingGroup (Fin 4)) := by
  rw [isSolvable_def]
  exact ⟨2, a4_derivedSeries_two_eq_bot⟩

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
