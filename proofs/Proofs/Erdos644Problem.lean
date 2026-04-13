/-
  Erdős Problem #644: Covering Families of Sets

  Source: https://erdosproblems.com/644
  Status: OPEN

  Statement:
  Let f(k,r) be minimal such that if A₁, A₂, ... is a family of sets, all of size k,
  such that for every collection of r of the Aᵢs there is some pair {x,y} intersecting
  all of them, then some set of size f(k,r) intersects all Aᵢ.

  Known:
  - f(k,3) = 2k [EFKT92]
  - f(k,4) = ⌊3k/2⌋ [EFKT92]
  - f(k,5) = ⌊5k/4⌋ [EFKT92]
  - f(k,6) = k [EFKT92]

  Questions:
  1. Is f(k,7) = (1+o(1))(3/4)k?
  2. For any r ≥ 3, does there exist c_r with f(k,r) = (1+o(1))c_r·k?

  Tags: combinatorics, set-systems, covering
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite
import Mathlib.Combinatorics.SetFamily.Intersecting
import Mathlib.Tactic

namespace Erdos644

open Finset Set

variable {α : Type*} [DecidableEq α]

/- ## Part I: Basic Definitions -/

/-- A family of sets, each of cardinality k. -/
structure KFamily (α : Type*) [DecidableEq α] (k : ℕ) where
  family : ℕ → Finset α
  card_eq : ∀ i, (family i).card = k

/-- A pair {x, y} intersects a set A if x ∈ A or y ∈ A. -/
def PairIntersects (x y : α) (A : Finset α) : Prop :=
  x ∈ A ∨ y ∈ A

/-- A pair {x, y} intersects all sets in a collection. -/
def PairIntersectsAll (x y : α) (sets : Finset ℕ) (F : ℕ → Finset α) : Prop :=
  ∀ i ∈ sets, PairIntersects x y (F i)

/-- The r-wise pair intersection property: every r sets share a common pair. -/
def HasRWisePairProperty (F : KFamily α k) (r : ℕ) : Prop :=
  ∀ indices : Finset ℕ, indices.card = r →
    ∃ x y : α, x ≠ y ∧ PairIntersectsAll x y indices F.family

/-- A covering set: intersects all sets in the family. -/
def IsCoveringSet (S : Finset α) (F : KFamily α k) (n : ℕ) : Prop :=
  ∀ i, i < n → (S ∩ F.family i).Nonempty

/-- A covering set for an infinite family. -/
def IsCoveringSetInf (S : Finset α) (F : KFamily α k) : Prop :=
  ∀ i, (S ∩ F.family i).Nonempty

/- ## Part II: The Function f(k,r) -/

/-- f(k,r) = minimum size of a covering set for families with r-wise pair property. -/
noncomputable def f (k r : ℕ) : ℕ :=
  ⨅ (m : ℕ), if ∀ (F : KFamily ℕ k), HasRWisePairProperty F r →
    ∃ S : Finset ℕ, S.card ≤ m ∧ IsCoveringSetInf S F then m else k * r

/-- f(k,r) is well-defined and finite. -/
theorem f_finite (k r : ℕ) (hk : k ≥ 1) (hr : r ≥ 3) : f k r ≤ k * r := by
  sorry

/- ## Part III: Known Values (EFKT92) -/

/-- f(k,3) = 2k: Three-wise pair property requires 2k covering. -/
theorem f_k_3 (k : ℕ) (hk : k ≥ 1) : f k 3 = 2 * k := by
  sorry

/-- f(k,4) = ⌊3k/2⌋: Four-wise pair property. -/
theorem f_k_4 (k : ℕ) (hk : k ≥ 1) : f k 4 = (3 * k) / 2 := by
  sorry

/-- f(k,5) = ⌊5k/4⌋: Five-wise pair property. -/
theorem f_k_5 (k : ℕ) (hk : k ≥ 1) : f k 5 = (5 * k) / 4 := by
  sorry

/-- f(k,6) = k: Six-wise pair property. -/
theorem f_k_6 (k : ℕ) (hk : k ≥ 1) : f k 6 = k := by
  sorry

/- ## Part IV: Pattern in Known Values -/

/-- The sequence of coefficients c_r. -/
noncomputable def coefficientSequence : ℕ → ℚ
  | 3 => 2
  | 4 => 3/2
  | 5 => 5/4
  | 6 => 1
  | _ => 0  -- Unknown

/-- Known coefficients are decreasing. -/
theorem coefficients_decreasing :
    coefficientSequence 3 > coefficientSequence 4 ∧
    coefficientSequence 4 > coefficientSequence 5 ∧
    coefficientSequence 5 > coefficientSequence 6 := by
  simp [coefficientSequence]
  norm_num

/-- Pattern: c_r appears to decrease toward some limit. -/
theorem coefficient_pattern :
    coefficientSequence 3 = 2 ∧
    coefficientSequence 4 = 3/2 ∧
    coefficientSequence 5 = 5/4 ∧
    coefficientSequence 6 = 1 := by
  simp [coefficientSequence]

/- ## Part V: Question 1 - The Case r = 7 -/

/-- Conjecture: f(k,7) = (3/4 + o(1))k. -/
def Question1 : Prop :=
  ∃ ε : ℕ → ℝ, (∀ k, ε k ≥ 0) ∧ Filter.Tendsto ε Filter.atTop (nhds 0) ∧
    ∀ k, k ≥ 1 → (f k 7 : ℝ) = (3/4 + ε k) * k

/-- Question 1 is OPEN. -/
axiom question1_open : Question1

/-- Lower bound for f(k,7). -/
theorem f_k_7_lower (k : ℕ) (hk : k ≥ 1) : f k 7 ≥ (3 * k) / 4 - k / 10 := by
  sorry

/-- Upper bound for f(k,7). -/
theorem f_k_7_upper (k : ℕ) (hk : k ≥ 1) : f k 7 ≤ k := by
  sorry

/- ## Part VI: Question 2 - General Asymptotics -/

/-- Conjecture: For all r ≥ 3, f(k,r) = (c_r + o(1))k for some constant c_r. -/
def Question2 : Prop :=
  ∀ r, r ≥ 3 → ∃ c_r : ℝ, c_r > 0 ∧
    ∃ ε : ℕ → ℝ, Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      ∀ k, k ≥ 1 → (f k r : ℝ) = (c_r + ε k) * k

/-- Question 2 is OPEN. -/
axiom question2_open : Question2

/-- If Question 2 holds, coefficients are bounded. -/
theorem q2_implies_bounded (h : Question2) :
    ∀ r, r ≥ 3 → ∃ c_r : ℝ, 0 < c_r ∧ c_r ≤ 2 := by
  sorry

/- ## Part VII: Extremal Constructions -/

/-- Construction showing f(k,3) ≥ 2k. -/
def extremalFamily3 (k : ℕ) : KFamily ℕ k where
  family := fun i => Finset.range k |>.map ⟨fun j => i * k + j, fun _ _ h => h⟩
  card_eq := by sorry

/-- The extremal family for r=3 requires 2k covering. -/
theorem extremalFamily3_lower (k : ℕ) (hk : k ≥ 1) :
    HasRWisePairProperty (extremalFamily3 k) 3 ∧
    ∀ S : Finset ℕ, IsCoveringSetInf S (extremalFamily3 k) → S.card ≥ 2 * k := by
  sorry

/-- Construction for r=6 showing f(k,6) = k is tight. -/
def extremalFamily6 (k : ℕ) : KFamily ℕ k where
  family := fun i => Finset.range k |>.map ⟨fun j => i * k + j, fun _ _ h => h⟩
  card_eq := by sorry

/- ## Part VIII: Monotonicity Properties -/

/-- f(k,r) is non-increasing in r. -/
theorem f_mono_r (k r₁ r₂ : ℕ) (h : r₁ ≤ r₂) (hr : r₁ ≥ 3) : f k r₂ ≤ f k r₁ := by
  sorry

/-- f(k,r) is non-decreasing in k. -/
theorem f_mono_k (k₁ k₂ r : ℕ) (h : k₁ ≤ k₂) (hr : r ≥ 3) : f k₁ r ≤ f k₂ r := by
  sorry

/-- f(k,r) ≤ k for r ≥ 6 (from f(k,6) = k). -/
theorem f_le_k (k r : ℕ) (hr : r ≥ 6) (hk : k ≥ 1) : f k r ≤ k := by
  sorry

/- ## Part IX: Sunflower Connection -/

/-- A sunflower with r petals. -/
structure Sunflower (α : Type*) [DecidableEq α] (r : ℕ) where
  core : Finset α
  petals : Fin r → Finset α
  disjoint_petals : ∀ i j, i ≠ j → Disjoint (petals i \ core) (petals j \ core)
  core_subset : ∀ i, core ⊆ petals i

/-- Sunflower lemma connects to pair intersection property. -/
theorem sunflower_connection (k r : ℕ) (hr : r ≥ 3) :
    ∀ F : KFamily α k, HasRWisePairProperty F r →
      ¬∃ sf : Sunflower α r, (∀ i, sf.petals i ∈ Set.range F.family) ∧ sf.core.card < 2 := by
  sorry

/- ## Part X: Hypergraph Formulation -/

/-- The problem as a hypergraph covering problem. -/
def HypergraphCovering (k r : ℕ) : Prop :=
  ∀ H : Finset (Finset ℕ), (∀ e ∈ H, e.card = k) →
    (∀ S : Finset (Finset ℕ), S ⊆ H → S.card = r →
      ∃ x y, x ≠ y ∧ ∀ e ∈ S, x ∈ e ∨ y ∈ e) →
    ∃ T : Finset ℕ, T.card ≤ f k r ∧ ∀ e ∈ H, (T ∩ e).Nonempty

/-- Hypergraph formulation is equivalent. -/
theorem hypergraph_equiv (k r : ℕ) (hr : r ≥ 3) : HypergraphCovering k r := by
  sorry

/- ## Part XI: Special Cases -/

/-- For r = 2, every pair of sets shares a pair, so f(k,2) = 2. -/
theorem f_k_2 (k : ℕ) (hk : k ≥ 2) : f k 2 = 2 := by
  sorry

/-- As r → ∞, f(k,r) → ? (unknown limit behavior). -/
theorem f_limit_behavior (k : ℕ) (hk : k ≥ 1) :
    ∀ r, r ≥ 6 → f k r ≤ k := by
  sorry

/-- Eventual stabilization: Does f(k,r) = f(k,r+1) for large r? -/
def EventualStabilization : Prop :=
  ∀ k, k ≥ 1 → ∃ R, ∀ r, r ≥ R → f k r = f k R

/- ## Part XII: Main Conjectures -/

/-- Main conjecture combining Q1 and Q2. -/
def MainConjecture : Prop :=
  Question1 ∧ Question2

/-- The main conjecture is OPEN. -/
axiom main_conjecture_open : MainConjecture

/-- Summary of what's known. -/
theorem known_summary :
    (∀ k, k ≥ 1 → f k 3 = 2 * k) ∧
    (∀ k, k ≥ 1 → f k 4 = (3 * k) / 2) ∧
    (∀ k, k ≥ 1 → f k 5 = (5 * k) / 4) ∧
    (∀ k, k ≥ 1 → f k 6 = k) := by
  constructor
  · exact f_k_3
  constructor
  · exact f_k_4
  constructor
  · exact f_k_5
  · exact f_k_6

end Erdos644

/-
  ## Summary

  This file formalizes Erdős Problem #644 on covering families of sets.

  **Status**: OPEN

  **The Function f(k,r)**:
  Minimum covering set size for k-uniform families with r-wise pair property.

  **Known Values** (EFKT92):
  - f(k,3) = 2k
  - f(k,4) = ⌊3k/2⌋
  - f(k,5) = ⌊5k/4⌋
  - f(k,6) = k

  **Open Questions**:
  1. Is f(k,7) = (3/4 + o(1))k?
  2. Does f(k,r) = (c_r + o(1))k for all r ≥ 3?

  **Key sorries**:
  - `f_k_3`, `f_k_4`, `f_k_5`, `f_k_6`: The known EFKT92 results
  - `question1_open`, `question2_open`: The main open questions (axioms)
-/
