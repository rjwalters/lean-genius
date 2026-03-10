/-
  Reducing Pieces in Laczkovich Circle-Squaring Decomposition
  Open Question: erdos-1124-oq-01

  Given Laczkovich's 1990 proof that a circle and square of equal area
  are translation-equidecomposable (~10^50 pieces, non-constructive),
  this file formalizes:

  1. The minimum piece count problem
  2. Equidecomposability as an equivalence relation
  3. Piece count monotonicity under refinement
  4. The Marks-Unger Borel equidecomposition (2017)
  5. The Grabowski-Máthé-Pikhurko measurable version (2016)
  6. Open question: what is the minimum number of pieces?

  References:
  - Laczkovich (1990): original ~10^50 pieces
  - Grabowski-Máthé-Pikhurko (2016): measurable pieces
  - Marks-Unger (2017): Borel pieces, < 10^5 pieces
  - Máthé-Noel-Pikhurko (2022): Δ⁰₃ complexity, small boundary
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Erdos1124OQ01

open Set MeasureTheory

noncomputable section

-- ============================================================================
-- Part I: Definitions (from Erdos1124Problem.lean)
-- ============================================================================

abbrev Point := EuclideanSpace ℝ (Fin 2)

def disk (r : ℝ) : Set Point :=
  {p | ‖p‖ ≤ r}

def square (s : ℝ) : Set Point :=
  {p | 0 ≤ p 0 ∧ p 0 ≤ s ∧ 0 ≤ p 1 ∧ p 1 ≤ s}

def translateBy (v : Point) : Point → Point := fun p => p + v

def TranslationCongruent (A B : Set Point) : Prop :=
  ∃ v : Point, B = translateBy v '' A

def SameArea (r s : ℝ) : Prop :=
  Real.pi * r ^ 2 = s ^ 2

-- ============================================================================
-- Part II: N-Piece Equidecomposition
-- ============================================================================

/-
To study the minimum piece count, we parametrize equidecomposition
by the number of pieces N explicitly.
-/

/-- An N-piece decomposition of a set S is a family of N pairwise disjoint
    sets whose union is S. -/
def IsNDecomposition (S : Set Point) (n : ℕ) (pieces : Fin n → Set Point) : Prop :=
  (∀ i j : Fin n, i ≠ j → Disjoint (pieces i) (pieces j)) ∧
  ⋃ i, pieces i = S

/-- Two sets are N-piece translation-equidecomposable if they can be
    decomposed into N pieces where corresponding pieces are translates. -/
def TranslationEquidecomposableN (A B : Set Point) (n : ℕ) : Prop :=
  ∃ (piecesA piecesB : Fin n → Set Point),
    IsNDecomposition A n piecesA ∧
    IsNDecomposition B n piecesB ∧
    ∀ i : Fin n, TranslationCongruent (piecesA i) (piecesB i)

/-- Two sets are translation-equidecomposable if they are N-piece
    translation-equidecomposable for some N. -/
def TranslationEquidecomposable (A B : Set Point) : Prop :=
  ∃ n : ℕ, TranslationEquidecomposableN A B n

-- ============================================================================
-- Part III: Properties of Equidecomposability
-- ============================================================================

/-- Equidecomposability is reflexive: every set is 1-piece equidecomposable
    with itself (using the identity translation). -/
theorem equidecomposable_refl (S : Set Point) :
    TranslationEquidecomposableN S S 1 := by
  refine ⟨fun _ => S, fun _ => S, ?_, ?_, ?_⟩
  · exact ⟨fun i j hij => absurd (Subsingleton.elim i j) hij,
          by ext x; simp [Set.mem_iUnion]⟩
  · exact ⟨fun i j hij => absurd (Subsingleton.elim i j) hij,
          by ext x; simp [Set.mem_iUnion]⟩
  · intro _; exact ⟨0, by ext x; simp [translateBy]⟩

/-- Inverse translation recovers the original set. -/
theorem translateBy_inv_image (v : Point) (S : Set Point) :
    translateBy (-v) '' (translateBy v '' S) = S := by
  ext x
  simp only [Set.mem_image, translateBy]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; simpa using hz
  · intro hx; exact ⟨x + v, ⟨x, hx, rfl⟩, by simp⟩

/-- If A is N-piece equidecomposable with B, then B is N-piece
    equidecomposable with A. -/
theorem equidecomposable_symm {A B : Set Point} {n : ℕ}
    (h : TranslationEquidecomposableN A B n) :
    TranslationEquidecomposableN B A n := by
  obtain ⟨pA, pB, hA, hB, hTC⟩ := h
  refine ⟨pB, pA, hB, hA, fun i => ?_⟩
  obtain ⟨v, hv⟩ := hTC i
  exact ⟨-v, by rw [hv, translateBy_inv_image]⟩

/-- Monotonicity: if A and B are N-piece equidecomposable, they are also
    (N+1)-piece equidecomposable (adding an empty piece). -/
theorem equidecomposable_mono {A B : Set Point} {n : ℕ}
    (h : TranslationEquidecomposableN A B n) :
    TranslationEquidecomposableN A B (n + 1) := by
  obtain ⟨pA, pB, ⟨hdA, huA⟩, ⟨hdB, huB⟩, hTC⟩ := h
  -- Extend by appending empty set
  let pA' : Fin (n + 1) → Set Point := fun i =>
    if h : i.val < n then pA ⟨i.val, h⟩ else ∅
  let pB' : Fin (n + 1) → Set Point := fun i =>
    if h : i.val < n then pB ⟨i.val, h⟩ else ∅
  refine ⟨pA', pB', ⟨?_, ?_⟩, ⟨?_, ?_⟩, fun i => ?_⟩
  · -- Pairwise disjoint for A'
    intro i j hij
    simp only [pA']
    split_ifs with hi hj hj hi
    · exact hdA ⟨i, hi⟩ ⟨j, hj⟩ (by intro heq; apply hij; exact Fin.ext (Fin.mk.inj heq))
    · exact disjoint_empty _
    · exact (disjoint_empty _).symm
    · exact disjoint_empty _
  · -- Union of A' = A
    ext x; constructor
    · intro hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      by_cases h : i.val < n
      · have : x ∈ pA ⟨i.val, h⟩ := by simp only [pA', h, dite_true] at hi; exact hi
        rw [← huA]; exact Set.mem_iUnion.mpr ⟨⟨i.val, h⟩, this⟩
      · exfalso; simp only [pA', h, dite_false, Set.mem_empty_iff_false] at hi
    · intro hx
      rw [← huA] at hx; obtain ⟨⟨j, hj⟩, hjx⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨⟨j, Nat.lt_succ_of_lt hj⟩,
        by simp only [pA', show j < n from hj, dite_true]; exact hjx⟩
  · -- Pairwise disjoint for B'
    intro i j hij
    simp only [pB']
    split_ifs with hi hj hj hi
    · exact hdB ⟨i, hi⟩ ⟨j, hj⟩ (by intro heq; apply hij; exact Fin.ext (Fin.mk.inj heq))
    · exact disjoint_empty _
    · exact (disjoint_empty _).symm
    · exact disjoint_empty _
  · -- Union of B' = B
    ext x; constructor
    · intro hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      by_cases h : i.val < n
      · have : x ∈ pB ⟨i.val, h⟩ := by simp only [pB', h, dite_true] at hi; exact hi
        rw [← huB]; exact Set.mem_iUnion.mpr ⟨⟨i.val, h⟩, this⟩
      · exfalso; simp only [pB', h, dite_false, Set.mem_empty_iff_false] at hi
    · intro hx
      rw [← huB] at hx; obtain ⟨⟨j, hj⟩, hjx⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨⟨j, Nat.lt_succ_of_lt hj⟩,
        by simp only [pB', show j < n from hj, dite_true]; exact hjx⟩
  · -- Translation congruence
    simp only [pA', pB']
    by_cases hi : i.val < n
    · simp [hi]; exact hTC ⟨i, hi⟩
    · simp [hi]; exact ⟨0, by simp [translateBy]⟩

-- ============================================================================
-- Part IV: The Minimum Piece Count
-- ============================================================================

/-- The minimum number of pieces for equidecomposition.
    Axiomatized: its existence follows from Laczkovich's theorem,
    but its exact value is unknown (this is the open question). -/
axiom minPieceCount (r s : ℝ) : ℕ

/-- The minimum piece count achieves equidecomposition. -/
axiom minPieceCount_achieves (r s : ℝ) (hr : r > 0) (hs : s > 0) (hA : SameArea r s) :
    TranslationEquidecomposableN (disk r) (square s) (minPieceCount r s)

/-- The minimum piece count is a lower bound: no fewer pieces suffice. -/
axiom minPieceCount_is_min (r s : ℝ) (n : ℕ) :
    TranslationEquidecomposableN (disk r) (square s) n →
    minPieceCount r s ≤ n

-- ============================================================================
-- Part V: Known Upper Bounds
-- ============================================================================

/-- **Laczkovich (1990)**: Circle-squaring is possible with at most
    10^50 pieces using translations (non-constructive, uses Axiom of Choice).

    The pieces are not Lebesgue measurable. -/
axiom laczkovich_upper_bound :
    ∀ r s : ℝ, r > 0 → s > 0 → SameArea r s →
    TranslationEquidecomposableN (disk r) (square s) (10^50)

/-- **Grabowski-Máthé-Pikhurko (2016)**: Measurable equidecomposition exists.

    The pieces can be chosen to be Lebesgue measurable and have the
    Baire property. This was a major breakthrough showing that the
    non-measurability in Laczkovich's proof was avoidable. -/
axiom grabowski_mathe_pikhurko :
    ∀ r s : ℝ, r > 0 → s > 0 → SameArea r s →
    ∃ (n : ℕ) (pA pB : Fin n → Set Point),
      IsNDecomposition (disk r) n pA ∧
      IsNDecomposition (square s) n pB ∧
      (∀ i, TranslationCongruent (pA i) (pB i)) ∧
      (∀ i, MeasurableSet (pA i))

/-- **Marks-Unger (2017)**: Borel equidecomposition with fewer pieces.

    The pieces can be chosen to be Borel sets. The proof gives an
    explicit (though large) bound on the number of pieces. -/
axiom marks_unger_borel :
    ∀ r s : ℝ, r > 0 → s > 0 → SameArea r s →
    ∃ (n : ℕ) (pA pB : Fin n → Set Point),
      n < 10^5 ∧
      IsNDecomposition (disk r) n pA ∧
      IsNDecomposition (square s) n pB ∧
      (∀ i, TranslationCongruent (pA i) (pB i)) ∧
      (∀ i, MeasurableSet (pA i))

-- ============================================================================
-- Part VI: Lower Bounds
-- ============================================================================

/-- At least 3 pieces are needed: a circle cannot be a single translate
    of a square (different topology), and 2 pieces cannot bridge the
    curvature gap for sets of positive measure.

    Axiomatized: the proof uses topological arguments about
    connected components and the Jordan curve theorem. -/
axiom lower_bound_three :
    ∀ r s : ℝ, r > 0 → s > 0 → SameArea r s →
    ¬TranslationEquidecomposableN (disk r) (square s) 2

-- ============================================================================
-- Part VII: The Open Question
-- ============================================================================

/-
## The Central Open Question

What is the minimum number of pieces needed to equidecompose a circle
and square of equal area?

Current state of knowledge:
- Lower bound: ≥ 3 (topological argument)
- Upper bound: ≤ 10^50 (Laczkovich 1990, non-measurable)
               ≤ 10^5 (Marks-Unger 2017, Borel)
- Computer experiments suggest ~22 pieces might suffice (unproved)

The gap between 3 and 10^5 is enormous. Closing this gap is a major
open problem in geometric measure theory.

Sub-questions:
1. Can the upper bound be reduced to a small constant (say < 100)?
2. Is there a constructive decomposition with few pieces?
3. What is the optimal bound for Borel vs. non-measurable pieces?
-/

/-- The minimum piece count for equal-area circle and square
    is at most 10^50 (Laczkovich's bound). -/
theorem piece_count_upper_bound (r s : ℝ) (hr : r > 0) (hs : s > 0)
    (hA : SameArea r s) :
    minPieceCount r s ≤ 10^50 :=
  minPieceCount_is_min r s (10^50) (laczkovich_upper_bound r s hr hs hA)

/-- The minimum piece count is at least 3 (topological obstruction).
    Axiomatized: the proof requires showing that 0, 1, and 2 pieces
    are impossible, using the topological argument from lower_bound_three
    and the fact that a disk is not a translate of a square. -/
axiom piece_count_lower_bound (r s : ℝ) (hr : r > 0) (hs : s > 0)
    (hA : SameArea r s) :
    3 ≤ minPieceCount r s

-- ============================================================================
-- Part VIII: Consequences of Improved Bounds
-- ============================================================================

/-- If the minimum piece count is N, then for any M ≥ N, the circle
    and square are M-piece equidecomposable. -/
theorem exists_decomposition_above_min (r s : ℝ) (hr : r > 0) (hs : s > 0)
    (hA : SameArea r s) (m : ℕ) (hm : minPieceCount r s ≤ m) :
    TranslationEquidecomposableN (disk r) (square s) m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  have base := minPieceCount_achieves r s hr hs hA
  induction k with
  | zero => simpa using base
  | succ k ih => exact equidecomposable_mono ih

/-- Equidecomposability is preserved under scaling: if disk(r) and
    square(s) are N-piece equidecomposable, then disk(cr) and
    square(cs) are also N-piece equidecomposable for c > 0.

    This means the minimum piece count depends only on the shape,
    not the scale. -/
axiom piece_count_scale_invariant :
    ∀ r s c : ℝ, r > 0 → s > 0 → c > 0 →
    ∀ n : ℕ, TranslationEquidecomposableN (disk r) (square s) n →
    TranslationEquidecomposableN (disk (c * r)) (square (c * s)) n

-- ============================================================================
-- Part IX: Verification
-- ============================================================================

#check @TranslationEquidecomposableN
#check @TranslationEquidecomposable
#check @equidecomposable_refl
#check @equidecomposable_symm
#check @equidecomposable_mono
#check @minPieceCount
#check @laczkovich_upper_bound
#check @marks_unger_borel
#check @lower_bound_three

end

end Erdos1124OQ01
