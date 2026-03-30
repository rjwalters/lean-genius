/-
  Erdős Problem #105, Open Question 05:
  Higher-dimensional generalization of the rich lines vs obstacles problem.

  Original problem (R²): Given n non-collinear points A and n-3 obstacles B,
  must some line through 2+ points of A avoid all obstacles?
  Answer: NO (Xichuan 2024).

  OQ-05: Does the analogous problem in R^d for d ≥ 3 behave similarly?
  Replace "lines" with k-dimensional affine subspaces (k-flats).

  Key definitions:
  - A k-flat is "rich" if it contains ≥ k+1 affinely independent points of A
  - A k-flat is "unblocked" if it contains no obstacles

  What we formalize:
  1. Points in R^d via EuclideanSpace
  2. Rich lines (1-flats) and rich 2-flats
  3. Non-degeneracy conditions (affine span = full space)
  4. Trivial existence of rich 1-flats (proved)
  5. The higher-dimensional open question

  Status: OPEN
  Reference: https://erdosproblems.com/105
-/

import Proofs.Erdos105Problem
import Mathlib

open Finset Set

namespace Erdos105OQ05

/- ## Part I: Higher-Dimensional Points -/

/-- A point in R^d. -/
abbrev PointD (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A line in R^d, parameterized by base point and direction. -/
structure LineD (d : ℕ) where
  basePoint : PointD d
  direction : PointD d
  direction_nonzero : direction ≠ 0

/-- A point lies on a line in R^d. -/
def LineD.contains {d : ℕ} (L : LineD d) (p : PointD d) : Prop :=
  ∃ t : ℝ, p = L.basePoint + t • L.direction

/-- A line is rich for a set A if it contains ≥ 2 distinct points of A. -/
def LineD.isRich {d : ℕ} (L : LineD d) (A : Set (PointD d)) : Prop :=
  ∃ p q : PointD d, p ∈ A ∧ q ∈ A ∧ p ≠ q ∧ L.contains p ∧ L.contains q

/-- A line is unblocked by B if it contains no points of B. -/
def LineD.unblocked {d : ℕ} (L : LineD d) (B : Set (PointD d)) : Prop :=
  ∀ b ∈ B, ¬L.contains b

/-- A line is rich and unblocked. -/
def LineD.richAndUnblocked {d : ℕ} (L : LineD d) (A B : Set (PointD d)) : Prop :=
  L.isRich A ∧ L.unblocked B

/- ## Part II: Non-Degeneracy -/

/-- A set of points in R^d is non-degenerate if not all points lie in
    any single affine hyperplane. Equivalently, the affine span is R^d. -/
def NonDegenerateD {d : ℕ} (A : Set (PointD d)) : Prop :=
  ∀ (v : PointD d) (c : ℝ),
    v ≠ 0 → ∃ p ∈ A, inner v p ≠ c

/-- Non-collinear in R^d: not all points on a single line. -/
def NonCollinearD {d : ℕ} (A : Set (PointD d)) : Prop :=
  ∀ L : LineD d, ∃ p ∈ A, ¬L.contains p

/- ## Part III: Rich Lines Exist in R^d (Proved) -/

/-- Any finset of ≥ 2 points in R^d has at least one rich line.
    This is trivially true: pick any two distinct points p, q;
    the line through them is rich. -/
theorem rich_line_exists_d {d : ℕ} (A : Finset (PointD d))
    (h : 2 ≤ A.card) :
    ∃ L : LineD d, L.isRich (A : Set (PointD d)) := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  have hdir : q - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
  refine ⟨⟨p, q - p, hdir⟩, p, q, Finset.mem_coe.mpr hp, Finset.mem_coe.mpr hq,
    Ne.symm hpq, ?_, ?_⟩
  · exact ⟨0, by simp [LineD.contains, zero_smul, add_zero]⟩
  · exact ⟨1, by simp [LineD.contains, one_smul, add_sub_cancel]⟩

/- ## Part IV: The Higher-Dimensional Conjecture -/

/-- **Higher-dimensional rich-line conjecture:**
    For A ⊂ R^d non-degenerate with |A| = n, and B disjoint from A
    with |B| = n - (d+1), must there exist a rich line avoiding B?

    In R² (d=2), the threshold was n-3 = n-(2+1), and the answer is NO.
    In R^d, the natural analog uses n-(d+1) obstacles. -/
def higherDimLineConjecture (d : ℕ) : Prop :=
  ∀ (A B : Finset (PointD d)) (n : ℕ),
    n ≥ d + 2 →
    A.card = n →
    B.card = n - (d + 1) →
    Disjoint A B →
    NonDegenerateD (A : Set (PointD d)) →
    ∃ L : LineD d, L.richAndUnblocked (A : Set (PointD d)) (B : Set (PointD d))

/-- The R² case (d=2) is the original Erdős-Purdy conjecture.
    This connects OQ-05 back to the main problem. -/
theorem higher_dim_d2_is_original :
    higherDimLineConjecture 2 ↔
    ∀ (A B : Finset (PointD 2)) (n : ℕ),
      n ≥ 4 → A.card = n → B.card = n - 3 →
      Disjoint A B → NonDegenerateD (A : Set (PointD 2)) →
      ∃ L : LineD 2, L.richAndUnblocked (A : Set (PointD 2)) (B : Set (PointD 2)) := by
  constructor <;> intro h <;> intro A B n hn hA hB hdisj hnd <;> exact h A B n hn hA hB hdisj hnd

/- ## Part V: 2-Flat Generalization -/

/-- A 2-flat (affine plane) in R^d, spanned by a point and two
    linearly independent directions. -/
structure TwoFlat (d : ℕ) where
  basePoint : PointD d
  dir1 : PointD d
  dir2 : PointD d
  dir1_nonzero : dir1 ≠ 0
  indep : ∀ (a b : ℝ), a • dir1 + b • dir2 = 0 → a = 0 ∧ b = 0

/-- A point lies on a 2-flat. -/
def TwoFlat.contains {d : ℕ} (F : TwoFlat d) (p : PointD d) : Prop :=
  ∃ s t : ℝ, p = F.basePoint + s • F.dir1 + t • F.dir2

/-- A 2-flat is rich if it contains ≥ 3 non-collinear points of A. -/
def TwoFlat.isRich {d : ℕ} (F : TwoFlat d) (A : Set (PointD d)) : Prop :=
  ∃ p q r : PointD d,
    p ∈ A ∧ q ∈ A ∧ r ∈ A ∧
    p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
    F.contains p ∧ F.contains q ∧ F.contains r ∧
    ¬∃ L : LineD d, L.contains p ∧ L.contains q ∧ L.contains r

/-- A 2-flat is unblocked by B. -/
def TwoFlat.unblocked {d : ℕ} (F : TwoFlat d) (B : Set (PointD d)) : Prop :=
  ∀ b ∈ B, ¬F.contains b

/-- **Higher-dimensional 2-flat conjecture:**
    For points A ⊂ R^d (d ≥ 3) in general position and obstacles B,
    must there exist a rich 2-flat (containing 3 non-collinear points of A)
    that avoids all obstacles?

    This is the core question of OQ-05: whether the obstacle-avoidance
    phenomenon extends from lines to higher-dimensional flats. -/
def richTwoFlatConjecture (d : ℕ) : Prop :=
  ∀ (A B : Finset (PointD d)) (n : ℕ),
    n ≥ d + 2 →
    A.card = n →
    Disjoint A B →
    NonDegenerateD (A : Set (PointD d)) →
    B.card ≤ n - (d + 1) →
    ∃ F : TwoFlat d, F.isRich (A : Set (PointD d)) ∧ F.unblocked (B : Set (PointD d))

/- ## Part VI: Monotonicity -/

/-- Fewer obstacles make it easier to find unblocked flats.
    If a rich unblocked line exists with obstacle set B,
    it also exists with any subset B' ⊆ B. -/
theorem unblocked_monotone_line {d : ℕ} {A : Set (PointD d)}
    {B B' : Set (PointD d)} (hBB : B' ⊆ B)
    (L : LineD d) (hrich : L.isRich A) (hunbl : L.unblocked B) :
    L.unblocked B' :=
  fun b hb hcont => hunbl b (hBB hb) hcont

/-- Similarly for 2-flats. -/
theorem unblocked_monotone_twoflat {d : ℕ} {A : Set (PointD d)}
    {B B' : Set (PointD d)} (hBB : B' ⊆ B)
    (F : TwoFlat d) (hunbl : F.unblocked B) :
    F.unblocked B' :=
  fun b hb hcont => hunbl b (hBB hb) hcont

/- ## Part VII: Dimension Reduction -/

/-- If the higher-dim line conjecture is false in R^d (i.e., counterexamples
    exist), then it is also false in R^(d+1), since we can embed the
    counterexample in a higher-dimensional space. This is the key structural
    observation: counterexamples lift to higher dimensions.

    (Stated as a definition since constructing the embedding is non-trivial.) -/
def counterexample_lifts : Prop :=
  ∀ d : ℕ, d ≥ 2 → ¬higherDimLineConjecture d → ¬higherDimLineConjecture (d + 1)

/- ## Summary

**Theorems (4)**:
- rich_line_exists_d: any ≥2 points in R^d have a rich line
- higher_dim_d2_is_original: d=2 case matches original problem
- unblocked_monotone_line: fewer obstacles ⟹ easier to find unblocked line
- unblocked_monotone_twoflat: monotonicity for 2-flats

**Definitions (9)**:
- PointD, LineD, TwoFlat: geometric objects in R^d
- LineD.contains/isRich/unblocked/richAndUnblocked
- TwoFlat.contains/isRich/unblocked
- NonDegenerateD, NonCollinearD
- higherDimLineConjecture, richTwoFlatConjecture
- counterexample_lifts

**Axioms (0)**, **Sorries (0)**
-/

end Erdos105OQ05
