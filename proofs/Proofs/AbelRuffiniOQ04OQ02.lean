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

import Mathlib

/- v4.31 compat (#38065 increment 6): `DivisionRing.toRatAlgebra` (default
priority) wins `Algebra ℚ K` synthesis over the structure-canonical instances
(defeq only at default transparency), breaking downstream `Normal`/
`IsSplittingField`/`IsGalois`/`IsCyclotomicExtension` synthesis. Demote it. -/
attribute [instance 10] DivisionRing.toRatAlgebra

set_option synthInstance.maxHeartbeats 80000

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

/-- Any group of prime cardinality is solvable (cyclic, hence abelian).
    v4.31 helper: the old `by decide` route lost its `Decidable` instances
    (subgroup equality over `derivedSeries` no longer synthesizes). -/
theorem solvable_of_prime_card {G : Type*} [Group G] (p : ℕ) [Fact p.Prime]
    (h : Nat.card G = p) : IsSolvable G := by
  haveI : IsCyclic G := isCyclic_of_prime_card h
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  refine isSolvable_of_comm fun a b => ?_
  obtain ⟨m, rfl⟩ := hg a
  obtain ⟨n, rfl⟩ := hg b
  rw [← zpow_add, ← zpow_add, add_comm]

/-- S₃ is solvable (order 6).
    Derived series: S₃ ⊵ A₃ ≅ ℤ/3ℤ ⊵ {e}. Both quotients are abelian. -/
theorem s3_solvable : IsSolvable (Perm (Fin 3)) := by
  -- A₃ has card 3!/2 = 3, prime → solvable; S₃/A₃ ↪ ℤˣ abelian.
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : IsSolvable ↥(alternatingGroup (Fin 3)) := by
    apply solvable_of_prime_card 3
    have h2 := two_mul_nat_card_alternatingGroup (α := Fin 3)
    have hc : Nat.card (Perm (Fin 3)) = 6 := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      decide
    omega
  apply solvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
  intro x hx
  exact ⟨⟨x, Equiv.Perm.mem_alternatingGroup.mpr hx⟩, rfl⟩

-- ============================================================
-- PART 3: S₄ Is Solvable
-- ============================================================

/-- S₄ is solvable (order 24).
    Derived series: S₄ ⊵ A₄ ⊵ V₄ ⊵ {e}. (3 steps)
    V₄ = {e, (12)(34), (13)(24), (14)(23)} is the Klein four-group. -/
theorem s4_solvable : IsSolvable (Perm (Fin 4)) := by
  -- v4.31: `native_decide` route lost its `Decidable` instances; prove the
  -- chain S₄ ⊵ A₄ ⊵ V₄ ⊵ {e} via Mathlib's `alternatingGroup.kleinFour` API.
  have hα4 : Nat.card (Fin 4) = 4 := by simp
  haveI : IsSolvable ↥(alternatingGroup (Fin 4)) := by
    -- V₄ is abelian (exponent 2), hence solvable
    haveI : IsSolvable ↥(alternatingGroup.kleinFour (Fin 4)) :=
      isSolvable_of_comm fun a b =>
        mul_comm_of_exponent_two
          (alternatingGroup.exponent_kleinFour_of_card_eq_four hα4) a b
    -- A₄/V₄ has card 12/4 = 3, prime → solvable
    haveI hnormal : (alternatingGroup.kleinFour (Fin 4)).Normal :=
      alternatingGroup.normal_kleinFour hα4
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    haveI : IsSolvable
        (↥(alternatingGroup (Fin 4)) ⧸ alternatingGroup.kleinFour (Fin 4)) := by
      apply solvable_of_prime_card 3
      have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (alternatingGroup.kleinFour (Fin 4))
      rw [alternatingGroup.card_of_card_eq_four hα4,
        alternatingGroup.kleinFour_card_of_card_eq_four hα4] at hmul
      omega
    exact solvable_of_ker_le_range (alternatingGroup.kleinFour (Fin 4)).subtype
      (QuotientGroup.mk' (alternatingGroup.kleinFour (Fin 4)))
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  apply solvable_of_ker_le_range (alternatingGroup (Fin 4)).subtype Equiv.Perm.sign
  intro x hx
  exact ⟨⟨x, Equiv.Perm.mem_alternatingGroup.mpr hx⟩, rfl⟩

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
