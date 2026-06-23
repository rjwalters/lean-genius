/-
  Erdős Problem #757: Sidon Sets in Almost-Sidon Families

  Let A ⊂ ℝ be a set of size n such that every subset B ⊆ A with |B| = 4
  has |B - B| ≥ 11. Find the best constant c > 0 such that A must always
  contain a Sidon set of size ≥ cn.

  For comparison, a Sidon set B of size 4 has |B - B| = 13 (all differences
  distinct, plus 0). So the condition says at most one difference is "missing"
  from any 4-element subset.

  **Known Bounds** (Gyárfás-Lehel 1995):
  - 1/2 < c ≤ 3/5 (the exact value is OPEN)

  References:
  - https://erdosproblems.com/757
  - Gyárfás, A., Lehel, J., "Linear sets with five distinct differences
    among any four elements", J. Combin. Theory Ser. B (1995), 108-118.
-/

import Mathlib

open scoped Pointwise
open Filter Set Finset

namespace Erdos757

/-
## Core Definitions

A **Sidon set** is a set where all pairwise sums are distinct. Equivalently,
all non-zero differences are distinct.
-/

/-- A set S is **Sidon** if all pairwise sums a + b (a ≤ b) are distinct.
Equivalently, if a + b = c + d with a ≤ b and c ≤ d, then {a,b} = {c,d}. -/
def IsSidon (S : Set ℝ) : Prop :=
  ∀ a b c d : ℝ, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    a + b = c + d → ({a, b} : Set ℝ) = {c, d}

/-- The difference set A - A = {a - a' : a, a' ∈ A}. -/
def differenceSet (A : Set ℝ) : Set ℝ := A - A

/-
## The Almost-Sidon Condition

A 4-element Sidon set has exactly 13 elements in its difference set:
- 0 (from a - a)
- 12 distinct non-zero differences (±(aᵢ - aⱼ) for i ≠ j)

The condition |B - B| ≥ 11 says we're "close" to being Sidon.
-/

/-- A set A has the **almost-Sidon property** if every 4-element subset B
has at least 11 elements in B - B. -/
def AlmostSidon (A : Set ℝ) : Prop :=
  ∀ B ⊆ A, B.ncard = 4 → (B - B).ncard ≥ 11

/-- A constant c is **admissible** if every finite almost-Sidon set A
contains a Sidon subset of size at least c * |A|. -/
def IsAdmissible (c : ℝ) : Prop :=
  ∀ {A : Set ℝ}, A.Finite → AlmostSidon A →
    ∃ S ⊆ A, IsSidon S ∧ c * A.ncard ≤ (S.ncard : ℝ)

/-
## Main Conjecture

Find the exact value of sup{c : IsAdmissible c}.
-/

/-- **Erdős Problem #757 (OPEN)**: What is the supremum of the set of
admissible constants?

Gyárfás-Lehel (1995) proved 1/2 < sSup {c | IsAdmissible c} < 3/5.
The exact value remains unknown. -/

/-
## Known Results (Gyárfás-Lehel 1995)
-/

/-- **Lower Bound** (Gyárfás-Lehel 1995): The supremum is strictly larger
than 1/2.

The proof constructs explicit Sidon subsets using a greedy algorithm. -/

/-- **Upper Bound** (Gyárfás-Lehel 1995): The supremum is strictly less
than 3/5.

The proof exhibits a family of almost-Sidon sets where the largest
Sidon subset has size just under 3n/5. -/

/-
## Properties of Sidon Sets
-/

/-- A Sidon set of size n has exactly n(n-1)/2 + 1 elements in its
difference set (the +1 is for 0). -/

/-- The empty set is Sidon. -/
theorem sidon_empty : IsSidon (∅ : Set ℝ) := by
  intro a b c d ha _ _ _
  exact absurd ha (Set.notMem_empty a)

/-- Singletons are Sidon. -/
theorem sidon_singleton (x : ℝ) : IsSidon ({x} : Set ℝ) := by
  intro a b c d ha hb hc hd _
  rw [Set.mem_singleton_iff] at ha hb hc hd
  subst ha hb hc hd
  rfl

/-
## Difference Sets
-/

/-- The difference set always contains 0. -/
theorem zero_mem_differenceSet (A : Set ℝ) (hA : A.Nonempty) :
    (0 : ℝ) ∈ differenceSet A := by
  obtain ⟨a, ha⟩ := hA
  exact ⟨a, ha, a, ha, sub_self a⟩

/-- The difference set is symmetric: x ∈ A - A ↔ -x ∈ A - A. -/
theorem differenceSet_symmetric (A : Set ℝ) (x : ℝ) :
    x ∈ differenceSet A ↔ -x ∈ differenceSet A := by
  constructor <;> intro ⟨a, ha, b, hb, hab⟩
  · exact ⟨b, hb, a, ha, by linarith⟩
  · exact ⟨b, hb, a, ha, by linarith⟩

/-
## The Condition |B - B| ≥ 11

This condition is a relaxation of the Sidon property. It says that
among any 4 elements, we can have at most one "collision" of differences.
-/

/-- The minimum size of |B - B| for a 4-element set B is 7
(arithmetic progression case). -/

/-- An almost-Sidon set has the property that no 4-element subset is
"too far" from being Sidon. -/
theorem almostSidon_of_sidon (A : Set ℝ) (hA : IsSidon A) : AlmostSidon A := by
  intro B hB hcard
  -- B is Sidon (subset of Sidon is Sidon)
  have hBSidon : IsSidon B := by
    intro a b c d ha hb hc hd hab
    exact hA a b c d (hB ha) (hB hb) (hB hc) (hB hd) hab
  -- B is finite (ncard = 4 implies finite)
  have hBfin : B.Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hBBfin : (B - B).Finite := Set.Finite.sub hBfin hBfin
  -- Convert B to Finset F
  set F := hBfin.toFinset with hF_def
  have hF_card : F.card = 4 := by rw [Set.Finite.toFinset_card]; exact hcard
  have hF_mem : ∀ x, x ∈ F ↔ x ∈ B := fun x => Set.Finite.mem_toFinset hBfin
  -- The difference map on off-diagonal pairs is injective (Sidon property)
  have hDiffInj : Set.InjOn (fun p : ℝ × ℝ => p.1 - p.2) ↑F.offDiag := by
    intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
    simp only [Finset.mem_coe, Finset.mem_offDiag] at h₁ h₂
    -- a₁ - b₁ = a₂ - b₂ implies a₁ + b₂ = a₂ + b₁
    have hab : a₁ + b₂ = a₂ + b₁ := by linarith
    -- By Sidon: {a₁, b₂} = {a₂, b₁}
    have hpair := hBSidon a₁ b₂ a₂ b₁
      ((hF_mem a₁).mp h₁.1) ((hF_mem b₂).mp h₂.2.1) ((hF_mem a₂).mp h₂.1)
      ((hF_mem b₁).mp h₁.2.1) hab
    rw [Set.pair_eq_pair_iff] at hpair
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd rfl h₁.2.2
  -- The off-diagonal has 12 pairs, so its image has 12 elements
  have hOD_card : F.offDiag.card = 12 := by
    rw [Finset.card_offDiag, hF_card]; norm_num
  have hImg_card : (F.offDiag.image (fun p : ℝ × ℝ => p.1 - p.2)).card = 12 := by
    rw [Finset.card_image_of_injOn hDiffInj, hOD_card]
  -- The image consists of nonzero elements in B - B
  have hImg_sub : ↑(F.offDiag.image (fun p : ℝ × ℝ => p.1 - p.2)) ⊆ (B - B) := by
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_offDiag] at hx
    obtain ⟨⟨a, b⟩, ⟨ha, hb, _⟩, rfl⟩ := hx
    exact ⟨a, (hF_mem a).mp ha, b, (hF_mem b).mp hb, rfl⟩
  have h0_notin_img : (0 : ℝ) ∉ (F.offDiag.image (fun p : ℝ × ℝ => p.1 - p.2) : Set ℝ) := by
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_offDiag]
    rintro ⟨⟨a, b⟩, ⟨_, _, hab⟩, h⟩
    exact hab (sub_eq_zero.mp h)
  -- Also 0 ∈ B - B
  have h0_mem : (0 : ℝ) ∈ B - B := by
    obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero (by omega : B.ncard ≠ 0)
    exact ⟨x, hx, x, hx, sub_self x⟩
  -- So B-B ⊇ {0} ∪ image, which has size 1 + 12 = 13 ≥ 11
  have hImgFin : (↑(F.offDiag.image (fun p : ℝ × ℝ => p.1 - p.2)) : Set ℝ).Finite :=
    Finset.finite_toSet _
  calc (B - B).ncard
      ≥ (insert (0 : ℝ) ↑(F.offDiag.image (fun p : ℝ × ℝ => p.1 - p.2))).ncard :=
        Set.ncard_le_ncard (Set.insert_subset h0_mem hImg_sub) hBBfin
    _ = (↑(F.offDiag.image (fun p : ℝ × ℝ => p.1 - p.2)) : Set ℝ).ncard + 1 :=
        Set.ncard_insert_of_not_mem h0_notin_img hImgFin
    _ = 12 + 1 := by rw [Set.ncard_coe_Finset, hImg_card]
    _ = 13 := by norm_num
    _ ≥ 11 := by norm_num

/-
## The Set of Admissible Constants
-/

/-- 0 is admissible (trivially, the empty set is Sidon). -/
theorem zero_admissible : IsAdmissible 0 := by
  intro A _ _
  use ∅
  constructor
  · exact Set.empty_subset A
  · constructor
    · exact sidon_empty
    · simp

/-- Negative numbers are admissible. -/
theorem neg_admissible (c : ℝ) (hc : c < 0) : IsAdmissible c := by
  intro A _ _
  use ∅
  constructor
  · exact Set.empty_subset A
  · constructor
    · exact sidon_empty
    · simp only [Set.ncard_empty, Nat.cast_zero]
      have h : c * A.ncard ≤ 0 := by
        apply mul_nonpos_of_nonpos_of_nonneg (le_of_lt hc) (Nat.cast_nonneg A.ncard)
      exact h

/-- The set of admissible constants is nonempty. -/
theorem admissible_nonempty : {c : ℝ | IsAdmissible c}.Nonempty :=
  ⟨0, zero_admissible⟩

/-
## Connection to Extremal Combinatorics

This problem is part of a family of questions about the structure of
sets with "few" arithmetic configurations.
-/

/-- A **B₂ sequence** is another name for a Sidon set (from the perspective
of additive combinatorics). -/
def IsB2Sequence (S : Set ℝ) : Prop := IsSidon S

/-- The Sidon set constant problem: what is the largest Sidon subset
guaranteed in a set of size n? This is asymptotically √n. -/

end Erdos757
