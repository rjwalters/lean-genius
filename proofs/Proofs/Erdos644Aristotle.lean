/-
  Aristotle targets for Erdos644 (Covering Families of Sets)
  Routine supporting lemmas for automated proof search.
  See Erdos644Problem.lean for the main formalization.

  All 19 sorries proved manually:
  - PairIntersects basic properties (symmetry, membership, monotonicity)
  - IsCoveringSetInf structural properties
  - Arithmetic helpers for floor expressions (all by omega)
  - Finset helpers (inter_nonempty, range_nonempty, range_card)
-/
import Mathlib

namespace Erdos644.Aristotle

open Finset Set

variable {α : Type*} [DecidableEq α]

/-
  ## Section 1: Inline Supporting Definitions
-/

/-- A pair {x, y} intersects a set A if x ∈ A or y ∈ A. -/
def PairIntersects (x y : α) (A : Finset α) : Prop :=
  x ∈ A ∨ y ∈ A

/-- A covering set intersects all sets in the family. -/
def IsCoveringSetInf (S : Finset α) (F : ℕ → Finset α) : Prop :=
  ∀ i, (S ∩ F i).Nonempty

/-
  ## Section 2: PairIntersects Properties
-/

/-- PairIntersects is symmetric -/
lemma pairIntersects_comm (x y : α) (A : Finset α) :
    PairIntersects x y A ↔ PairIntersects y x A := by
  simp [PairIntersects, or_comm]

/-- PairIntersects holds when x ∈ A -/
lemma pairIntersects_of_mem_left (x y : α) (A : Finset α) (h : x ∈ A) :
    PairIntersects x y A :=
  Or.inl h

/-- PairIntersects holds when y ∈ A -/
lemma pairIntersects_of_mem_right (x y : α) (A : Finset α) (h : y ∈ A) :
    PairIntersects x y A :=
  Or.inr h

/-- PairIntersects is monotone: if A ⊆ B then PairIntersects extends -/
lemma pairIntersects_mono (x y : α) (A B : Finset α) (hAB : A ⊆ B)
    (h : PairIntersects x y A) : PairIntersects x y B := by
  cases h with
  | inl h => exact Or.inl (hAB h)
  | inr h => exact Or.inr (hAB h)

/-- If x ∈ A and A ∩ S is nonempty only needs one witness -/
lemma mem_inter_nonempty_of_mem (x : α) (S A : Finset α) (hx : x ∈ S) (hA : x ∈ A) :
    (S ∩ A).Nonempty :=
  ⟨x, Finset.mem_inter.mpr ⟨hx, hA⟩⟩

/-
  ## Section 3: IsCoveringSetInf Properties
-/

/-- A covering set covers every index -/
lemma coveringInf_at (S : Finset α) (F : ℕ → Finset α)
    (h : IsCoveringSetInf S F) (i : ℕ) : (S ∩ F i).Nonempty :=
  h i

/-- Superset of a covering set is also covering -/
lemma coveringInf_superset (S T : Finset α) (F : ℕ → Finset α)
    (hST : S ⊆ T) (hS : IsCoveringSetInf S F) : IsCoveringSetInf T F := by
  intro i
  obtain ⟨x, hx⟩ := hS i
  exact ⟨x, Finset.mem_inter.mpr ⟨hST (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩⟩

/-- Union of a covering set with anything is still covering -/
lemma coveringInf_union_left (S T : Finset α) (F : ℕ → Finset α)
    (hS : IsCoveringSetInf S F) : IsCoveringSetInf (S ∪ T) F := by
  intro i
  obtain ⟨x, hx⟩ := hS i
  exact ⟨x, Finset.mem_inter.mpr
    ⟨Finset.mem_union_left T (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩⟩

/-
  ## Section 4: Arithmetic Helpers for Floor Expressions
-/

/-- k ≤ 2*k for natural numbers -/
lemma k_le_2k (k : ℕ) : k ≤ 2 * k := by omega

/-- ⌊3k/2⌋ ≤ 2k -/
lemma floor_3k2_le_2k (k : ℕ) : 3 * k / 2 ≤ 2 * k := by omega

/-- ⌊5k/4⌋ ≤ ⌊3k/2⌋ -/
lemma floor_5k4_le_3k2 (k : ℕ) : 5 * k / 4 ≤ 3 * k / 2 := by omega

/-- k ≤ ⌊3k/2⌋ for k ≥ 1 -/
lemma k_le_3k2 (k : ℕ) (hk : k ≥ 1) : k ≤ 3 * k / 2 := by omega

/-- ⌊3k/4⌋ ≤ k -/
lemma floor_3k4_le_k (k : ℕ) : 3 * k / 4 ≤ k := by omega

/-- ⌊5k/4⌋ ≤ k*2 -/
lemma floor_5k4_le_2k (k : ℕ) : 5 * k / 4 ≤ 2 * k := by omega

/-- k - k/10 ≤ k (trivial lower bound) -/
lemma k_minus_tenth_le_k (k : ℕ) : k - k / 10 ≤ k := by omega

/-- ⌊3k/4⌋ ≤ ⌊5k/4⌋ -/
lemma floor_3k4_le_5k4 (k : ℕ) : 3 * k / 4 ≤ 5 * k / 4 := by omega

/-
  ## Section 5: Finset Intersection Helpers
-/

/-- Finset intersection is nonempty when a common element exists -/
lemma inter_nonempty_of_common (S T : Finset α) (x : α) (hS : x ∈ S) (hT : x ∈ T) :
    (S ∩ T).Nonempty :=
  ⟨x, Finset.mem_inter.mpr ⟨hS, hT⟩⟩

/-- Finset.range k is nonempty for k ≥ 1 -/
lemma range_nonempty (k : ℕ) (hk : k ≥ 1) : (Finset.range k).Nonempty :=
  Finset.nonempty_range_iff.mpr (by omega)

/-- card of range k equals k -/
lemma range_card (k : ℕ) : (Finset.range k).card = k :=
  Finset.card_range k

end Erdos644.Aristotle
