/-
# Erdős Problem #848 OQ-01: Why Exactly {7, 18} mod 25?

The extremal sets for Erdős #848 are {n ≡ 7 (mod 25)} and {n ≡ 18 (mod 25)}.
This file gives the complete algebraic explanation:

**Answer**: 7 and 18 are the UNIQUE solutions to x² ≡ -1 (mod 25). For any
a ≡ b ≡ x (mod 25) with x² ≡ -1 (mod 25), we have ab + 1 ≡ x² + 1 ≡ 0 (mod 25),
so 5² | ab + 1. No other mod-25 residue class achieves this via prime 5.

The two classes are INCOMPATIBLE: if a ≡ 7 and b ≡ 18 (mod 25), then
ab + 1 ≡ 7·18 + 1 = 127 ≡ 2 (mod 25), so 5 ∤ ab + 1.

Main results:
1. 7 and 18 are the unique solutions to x² = -1 in ZMod 25 (decide)
2. For r < 25, exactly r ∈ {7, 18} satisfy 5² | r·r + 1 (decide / interval_cases)
3. Cross-residue incompatibility: 5² ∤ ab+1 for a ≡ 7, b ≡ 18 (mod 25) (ring+omega)
4. All non-extremal classes fail: for r ∉ {7,18}, r < 25 → 5² ∤ r·r+1 (omega)
5. Independent lower bound N/25 ≤ maxNonSqfreeSet N via the mod-18 witness
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Proofs.Erdos848Problem

namespace Erdos848OQ01

/-! ## Part I: Algebraic Explanation via ZMod 25

Why does 5² | ab + 1 for a ≡ b ≡ 7 (mod 25)? Because 7² ≡ -1 (mod 25).
The algebraic question is: which residues x mod 25 satisfy x² ≡ -1 (mod 25)?
Answer: exactly x = 7 and x = 18. -/

/-- 7² = 49 = 2·25 - 1, so 7 is a square root of -1 in ZMod 25. -/
theorem seven_sq_eq_neg_one_mod25 : (7 : ZMod 25) ^ 2 = -1 := by decide

/-- 18² = 324 = 13·25 - 1, so 18 is the second square root of -1 in ZMod 25. -/
theorem eighteen_sq_eq_neg_one_mod25 : (18 : ZMod 25) ^ 2 = -1 := by decide

/-- The two square roots are negatives of each other: 7 + 18 = 25 ≡ 0 (mod 25),
    so 18 = -7 in ZMod 25. This is the ±√(-1) symmetry. -/
theorem seven_eq_neg_eighteen_mod25 : (18 : ZMod 25) = -(7 : ZMod 25) := by decide

/-- UNIQUENESS: The only solutions to x² = -1 in ZMod 25 are 7 and 18.
    This is the algebraic reason why exactly these two residue classes are extremal. -/
theorem sq_neg_one_iff_seven_or_eighteen :
    ∀ x : ZMod 25, x ^ 2 = -1 ↔ x = 7 ∨ x = 18 := by decide

/-- Elementary ℕ form: for all r : Fin 25, 25 | r·r+1 iff r = 7 or r = 18. -/
theorem mod25_sq_succ_dvd_iff :
    ∀ r : Fin 25, 25 ∣ (r : ℕ) * (r : ℕ) + 1 ↔ (r : ℕ) = 7 ∨ (r : ℕ) = 18 := by
  decide

/-! ## Part II: Cross-Residue Incompatibility

The sets {n ≡ 7 (mod 25)} and {n ≡ 18 (mod 25)} cannot be combined: a set
containing both a ≡ 7 and b ≡ 18 (mod 25) fails the 5² | ab+1 condition. -/

/-- If a ≡ 7 (mod 25) and b ≡ 18 (mod 25), then 5² ∤ ab + 1.
    Proof: ab + 1 ≡ 7·18 + 1 = 127 ≡ 2 (mod 25), so 25 ∤ ab + 1. -/
theorem cross_residue_five_sq_fails (a b : ℕ)
    (ha : a % 25 = 7) (hb : b % 25 = 18) : ¬(5 * 5 ∣ a * b + 1) := by
  intro ⟨k, hk⟩
  obtain ⟨m, rfl⟩ : ∃ m, a = 25 * m + 7 := ⟨a / 25, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, b = 25 * n + 18 := ⟨b / 25, by omega⟩
  have : (25 * m + 7) * (25 * n + 18) + 1 =
         25 * (25 * m * n + 18 * m + 7 * n + 5) + 2 := by ring
  omega

/-- Symmetric: if a ≡ 18 (mod 25) and b ≡ 7 (mod 25), then 5² ∤ ab + 1. -/
theorem cross_residue_five_sq_fails' (a b : ℕ)
    (ha : a % 25 = 18) (hb : b % 25 = 7) : ¬(5 * 5 ∣ a * b + 1) := by
  intro h; exact cross_residue_five_sq_fails b a hb ha (mul_comm a b ▸ h)

/-- A set containing both a mod-7 and a mod-18 element cannot rely on prime 5
    for the non-squarefree property on cross pairs: some other prime p must
    satisfy p² | ab + 1 for such pairs. -/
theorem mixed_set_needs_other_prime (A : Finset ℕ)
    (ha : ∃ a ∈ A, a % 25 = 7) (hb : ∃ b ∈ A, b % 25 = 18)
    (hAB : HasNonSqfreeProductProp A) :
    ∃ a ∈ A, ∃ b ∈ A, ∃ p : ℕ, p.Prime ∧ p ≠ 5 ∧ p * p ∣ a * b + 1 := by
  obtain ⟨a, haA, ha7⟩ := ha
  obtain ⟨b, hbA, hb18⟩ := hb
  have hno5 : ¬(5 * 5 ∣ a * b + 1) := cross_residue_five_sq_fails a b ha7 hb18
  have hnsf : ¬IsSquarefree (a * b + 1) := hAB a haA b hbA
  unfold IsSquarefree at hnsf; push_neg at hnsf
  obtain ⟨p, hp, hdvd⟩ := hnsf
  exact ⟨a, haA, b, hbA, p, hp, fun heq => hno5 (heq ▸ hdvd), hdvd⟩

/-! ## Part III: Complete Classification of Mod-25 Classes

For any residue r < 25 with r ∉ {7, 18}, the class {n ≡ r (mod 25)} cannot
achieve the non-squarefree product property via prime 5 alone. -/

/-- For any r < 25 with r ≠ 7 and r ≠ 18, we have 5² ∤ r·r + 1.
    This means the class {n ≡ r (mod 25)} cannot use p = 5 for the property. -/
theorem non_extremal_class_five_sq_fails (r : ℕ) (hr : r < 25)
    (hr7 : r ≠ 7) (hr18 : r ≠ 18) : ¬(5 * 5 ∣ r * r + 1) := by
  interval_cases r <;> omega

/-- Biconditional: for r < 25, the class {n ≡ r (mod 25)} satisfies
    5² | r·r + 1 iff r = 7 or r = 18. Together with non_extremal_class_five_sq_fails,
    this completely characterizes the two extremal classes. -/
theorem extremal_iff_five_sq_divides (r : ℕ) (hr : r < 25) :
    (5 * 5 ∣ r * r + 1) ↔ r = 7 ∨ r = 18 := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    exact non_extremal_class_five_sq_fails r hr hc.1 hc.2 h
  · rintro (rfl | rfl)
    · exact ⟨2, by norm_num⟩
    · exact ⟨13, by norm_num⟩

/-! ## Part IV: Independent Lower Bound via Mod-18 Class

The parent file (`Erdos848Problem`) proved N/25 ≤ maxNonSqfreeSet N using the
mod-7 class. Here we give an independent proof using the mod-18 class. -/

private def mod18Set (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => n % 25 = 18)

private lemma mod18Set_sub (N : ℕ) : mod18Set N ⊆ Finset.Icc 1 N :=
  Finset.filter_subset _ _

private lemma mod18Set_residue {N n : ℕ} (hn : n ∈ mod18Set N) : n % 25 = 18 := by
  simp only [mod18Set, Finset.mem_filter] at hn; exact hn.2

private lemma mod18Set_prop (N : ℕ) : HasNonSqfreeProductProp (mod18Set N) :=
  mod18_set_has_property (mod18Set N) (fun _ h => mod18Set_residue h)

private lemma mod18Set_card_ge (N : ℕ) (hN : 25 ≤ N) : N / 25 ≤ (mod18Set N).card := by
  set f : ℕ → ℕ := fun k => 25 * k + 18 with hf_def
  have hf_mem : ∀ k, k ∈ Finset.range (N / 25) → f k ∈ mod18Set N := by
    intro k hk
    simp only [Finset.mem_range] at hk
    simp only [mod18Set, Finset.mem_filter, Finset.mem_Icc, hf_def]
    refine ⟨⟨by omega, ?_⟩, by omega⟩
    have := Nat.div_mul_le_self N 25; omega
  have hf_inj : Set.InjOn f (Finset.range (N / 25) : Set ℕ) := by
    intro a _ b _ hab; simp only [hf_def] at hab; omega
  calc N / 25 = (Finset.range (N / 25)).card := (Finset.card_range _).symm
    _ ≤ (mod18Set N).card := Finset.card_le_card_of_injOn f hf_mem hf_inj

/-- Independent lower bound: N/25 ≤ maxNonSqfreeSet N for N ≥ 25,
    proved using the mod-18 residue class as a second witness.
    This is independent of the mod-7 lower bound in the parent file. -/
theorem lower_bound_via_mod18 (N : ℕ) (hN : 25 ≤ N) :
    N / 25 ≤ maxNonSqfreeSet N := by
  classical
  unfold maxNonSqfreeSet
  have hmem : mod18Set N ∈
      (Finset.Icc 1 N).powerset.filter (fun A => HasNonSqfreeProductProp A) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr (mod18Set_sub N), mod18Set_prop N⟩
  calc N / 25 ≤ (mod18Set N).card := mod18Set_card_ge N hN
    _ ≤ _ := Finset.le_sup hmem

end Erdos848OQ01
