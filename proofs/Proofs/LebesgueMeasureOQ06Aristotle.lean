/-
  Aristotle targets for LebesgueMeasureOQ06 (Banach-Tarski Paradox)
  Routine supporting lemmas for automated proof search.
  See Proofs/LebesgueMeasureOQ06.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open results (banach_tarski, hausdorff_free_subgroup)
  - NOT theorems requiring the Axiom of Choice in essential ways
  - Routine ENNReal arithmetic and amenability structural helpers
  - No definition sorries
  - No axiom declarations

  Included targets (5):
  - ennreal_add_eq_self_iff: a + a = a ↔ a = 0 ∨ a = ⊤ (public non-private version)
  - ennreal_two_mul_ne_self: 0 < a → a ≠ ⊤ → a + a ≠ a
  - amenable_compl_sum: μ A + μ Aᶜ = μ univ for finitely-additive μ
  - freeGroup_generators_ne: generators 0 and 1 in FreeGroup (Fin 2) are distinct
  - freeGroup_nontrivial: FreeGroup (Fin 2) is nontrivial
-/
import Mathlib

open Set MeasureTheory ENNReal

namespace BanachTarskiAristotle

/-
  ## Section 1: ENNReal Arithmetic
  Key arithmetic facts for the amenability and paradoxicality arguments.
-/

/-- In ℝ≥0∞, a + a = a iff a = 0 or a = ⊤.
    This is the key "paradox equation": if a paradoxical set has a
    finite invariant measure μ, then μ(A) = 2·μ(A) forces μ(A) ∈ {0, ⊤}. -/
theorem ennreal_add_eq_self_iff {a : ℝ≥0∞} : a + a = a ↔ a = 0 ∨ a = ⊤ := by
  constructor
  · intro h
    rcases eq_or_ne a ⊤ with rfl | hneT
    · exact Or.inr rfl
    rcases eq_or_ne a 0 with rfl | hne0
    · exact Or.inl rfl
    exact absurd h (ENNReal.lt_add_right hneT hne0).ne'
  · rintro (rfl | rfl) <;> simp

/-- If 0 < a < ⊤ then a + a ≠ a (the paradox equation fails for finite positive measures). -/
theorem ennreal_two_mul_ne_self {a : ℝ≥0∞} (ha_pos : 0 < a) (ha_top : a ≠ ⊤) :
    a + a ≠ a :=
  (ENNReal.lt_add_right ha_top ha_pos.ne').ne'

/-- A + Aᶜ = Set.univ for any set. -/
theorem union_compl_eq_univ {α : Type*} (A : Set α) : A ∪ Aᶜ = Set.univ :=
  Set.union_compl_self A

/-- For a finitely-additive probability measure, μ A + μ Aᶜ = 1. -/
theorem amenable_compl_sum {G : Type*}
    (μ : Set G → ℝ≥0∞)
    (hμ_total : μ Set.univ = 1)
    (hμ_add : ∀ A B : Set G, Disjoint A B → μ (A ∪ B) = μ A + μ B)
    (A : Set G) : μ A + μ Aᶜ = 1 := by
  rw [← hμ_add A Aᶜ disjoint_compl_right, Set.union_compl_self, hμ_total]

/-
  ## Section 2: FreeGroup Basic Facts
  Elementary properties of FreeGroup (Fin 2) for the non-amenability proof.
-/

/-- The two generators of FreeGroup (Fin 2) are distinct elements. -/
theorem freeGroup_generators_ne :
    FreeGroup.of (0 : Fin 2) ≠ FreeGroup.of (1 : Fin 2) :=
  fun h => absurd (FreeGroup.of_injective h) (by decide)

/-- FreeGroup (Fin 2) is nontrivial (contains more than just the identity). -/
theorem freeGroup_nontrivial : Nontrivial (FreeGroup (Fin 2)) :=
  ⟨_, _, freeGroup_generators_ne⟩

end BanachTarskiAristotle
