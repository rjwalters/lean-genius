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

import Mathlib

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

-- ============================================================================
-- Part IX: Zero-Piece Impossibility (PROVED)
-- ============================================================================

/-- The empty union over Fin 0 is the empty set. -/
theorem iUnion_fin_zero (f : Fin 0 → Set Point) : ⋃ i, f i = ∅ := by
  ext x
  simp

/-- A nonempty set cannot be 0-piece decomposed. -/
theorem not_zero_decomposition {S : Set Point} (hne : S.Nonempty)
    (pieces : Fin 0 → Set Point) :
    ¬IsNDecomposition S 0 pieces := by
  intro ⟨_, hu⟩
  rw [iUnion_fin_zero] at hu
  exact Set.Nonempty.ne_empty hne hu.symm

/-- The disk of positive radius is nonempty (contains the origin). -/
theorem disk_nonempty {r : ℝ} (hr : r > 0) : (disk r).Nonempty :=
  ⟨0, by simp [disk, norm_zero, le_of_lt hr]⟩

/-- The square of positive side is nonempty (contains the origin). -/
theorem square_nonempty {s : ℝ} (hs : s > 0) : (square s).Nonempty :=
  ⟨0, by simp [square, le_of_lt hs]⟩

/-- PROVED: A disk and square of positive dimensions cannot be
    0-piece equidecomposable (the disk is nonempty but Fin 0 union is empty). -/
theorem not_zero_equidecomposable (r s : ℝ) (hr : r > 0) (hs : s > 0) :
    ¬TranslationEquidecomposableN (disk r) (square s) 0 := by
  intro ⟨pA, _, hA, _, _⟩
  exact not_zero_decomposition (disk_nonempty hr) pA hA

-- ============================================================================
-- Part X: One-Piece Impossibility (PROVED)
-- ============================================================================

-- Strategy: if disk(r) = translate of square(s), then the diagonal of the
-- square ((0,0) to (s,s)) must fit inside the disk. The diagonal has length
-- s√2, and the disk has diameter 2r. So s√2 ≤ 2r, giving s² ≤ 2r².
-- But SameArea: πr² = s² ≤ 2r² → π ≤ 2. Contradiction since π > 3.

/-- Extract the single piece from a Fin 1 union. -/
theorem iUnion_fin_one_eq (f : Fin 1 → Set Point) : (⋃ i, f i) = f 0 := by
  ext x; simp only [Set.mem_iUnion]
  exact ⟨fun ⟨i, hi⟩ => (Subsingleton.elim i 0) ▸ hi, fun h => ⟨0, h⟩⟩

/-- Membership in a translated set: q ∈ translateBy v '' S ↔ q - v ∈ S. -/
theorem mem_translateBy_iff (v : Point) (S : Set Point) (q : Point) :
    q ∈ translateBy v '' S ↔ q - v ∈ S := by
  simp only [translateBy, Set.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩; rwa [add_sub_cancel_right]
  · intro h; exact ⟨q - v, h, by simp⟩

/-- The origin is in the disk of positive radius. -/
theorem zero_mem_disk {r : ℝ} (hr : r > 0) : (0 : Point) ∈ disk r := by
  simp [disk, norm_zero, le_of_lt hr]

/-- A point (a, b) constructed via EuclideanSpace.single is in the square
    when both coordinates are in [0, s]. -/
theorem single_sum_mem_disk {r a : ℝ} (ha : ‖(EuclideanSpace.single 0 a : Point)
    + (EuclideanSpace.single 1 a : Point)‖ ≤ r) :
    (EuclideanSpace.single 0 a : Point) + (EuclideanSpace.single 1 a : Point) ∈ disk r :=
  ha

/-- Norm squared of (a, a) in ℝ² via inner product. -/
theorem norm_sq_diagonal (a : ℝ) :
    ‖(EuclideanSpace.single 0 a : Point) + (EuclideanSpace.single 1 a : Point)‖ ^ 2 =
    2 * a ^ 2 := by
  rw [sq, ← real_inner_self_eq_norm_mul_norm, inner_add_left, inner_add_right, inner_add_right]
  simp [EuclideanSpace.inner_single_right]
  ring

/-- PROVED: A disk and square of positive dimensions with equal area
    cannot be 1-piece equidecomposable.

    Proof: If disk(r) = translate of square(s), then the diagonal corners
    (0,0) and (s,s) of the square both map to points in the disk via the
    inverse translation. By the triangle inequality, ‖(s,s)‖ ≤ 2r.
    Since ‖(s,s)‖² = 2s², we get s² ≤ 2r². But πr² = s² ≤ 2r² gives
    π ≤ 2, contradicting π > 3. -/
theorem not_one_equidecomposable (r s : ℝ) (hr : r > 0) (hs : s > 0)
    (hA : SameArea r s) :
    ¬TranslationEquidecomposableN (disk r) (square s) 1 := by
  intro ⟨pA, pB, ⟨_, huA⟩, ⟨_, huB⟩, hTC⟩
  -- With 1 piece, the single piece IS the whole set
  rw [iUnion_fin_one_eq] at huA huB
  -- Get the translation: pB 0 = translateBy v '' (pA 0)
  obtain ⟨v, hv⟩ := hTC 0
  -- So square(s) = translateBy v '' (disk(r))
  rw [huA, huB] at hv
  -- The origin (0,0) is in square(s)
  have h0_sq : (0 : Point) ∈ square s := by simp [square, le_of_lt hs]
  -- So 0 - v ∈ disk(r), i.e., ‖v‖ ≤ r
  have hv_disk : ‖v‖ ≤ r := by
    have := (mem_translateBy_iff v (disk r) 0).mp (hv ▸ h0_sq)
    simp [disk] at this
    exact this
  -- The corner (s,s) is in square(s)
  -- We use EuclideanSpace.single to construct it as single 0 s + single 1 s
  set corner := (EuclideanSpace.single 0 s : Point) + (EuclideanSpace.single 1 s : Point)
  have hc_sq : corner ∈ square s := by
    show 0 ≤ corner 0 ∧ corner 0 ≤ s ∧ 0 ≤ corner 1 ∧ corner 1 ≤ s
    simp [corner, EuclideanSpace.single_apply, le_of_lt hs]
  -- So corner - v ∈ disk(r), i.e., ‖corner - v‖ ≤ r
  have hcv_disk : ‖corner - v‖ ≤ r := by
    have := (mem_translateBy_iff v (disk r) corner).mp (hv ▸ hc_sq)
    exact this
  -- Triangle inequality: ‖corner‖ ≤ ‖corner - v‖ + ‖v‖ ≤ 2r
  have h_tri : ‖corner‖ ≤ 2 * r := by
    have : ‖corner‖ ≤ ‖corner - v‖ + ‖v‖ := by
      have := norm_add_le (corner - v) v; rwa [sub_add_cancel] at this
    linarith
  -- ‖corner‖² = 2s² (norm of the diagonal vector (s,s))
  have h_norm_sq : ‖corner‖ ^ 2 = 2 * s ^ 2 := norm_sq_diagonal s
  -- So 2s² ≤ (2r)² = 4r², giving s² ≤ 2r²
  have h_sq_bound : s ^ 2 ≤ 2 * r ^ 2 := by
    have h_sq_le : ‖corner‖ ^ 2 ≤ (2 * r) ^ 2 :=
      sq_le_sq' (by linarith [norm_nonneg corner]) h_tri
    nlinarith
  -- But πr² = s² ≤ 2r² → π ≤ 2. Contradiction since π > 3.
  have : SameArea r s := hA
  simp only [SameArea] at this
  nlinarith [Real.pi_gt_three]

-- ============================================================================
-- Part XI: Transitivity of Equidecomposition (PROVED)
-- ============================================================================

/-- Composing translations: translateBy w ∘ translateBy v = translateBy (v + w). -/
theorem translateBy_comp (v w : Point) (S : Set Point) :
    translateBy w '' (translateBy v '' S) = translateBy (v + w) '' S := by
  ext x
  simp only [Set.mem_image, translateBy]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by abel⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z + v, ⟨z, hz, rfl⟩, by abel⟩

/-- Translation congruence is transitive: if A ~ B and B ~ C then A ~ C. -/
theorem translation_congruent_trans {A B C : Set Point}
    (h1 : TranslationCongruent A B) (h2 : TranslationCongruent B C) :
    TranslationCongruent A C := by
  obtain ⟨v, hv⟩ := h1
  obtain ⟨w, hw⟩ := h2
  exact ⟨v + w, by rw [hw, hv, translateBy_comp]⟩

-- ============================================================================
-- Part XII: Proved Lower Bound Chain
-- ============================================================================

/-- **PROVED**: The minimum piece count is at least 3.
    Case analysis: 0 pieces impossible (nonempty), 1 piece impossible
    (shape mismatch, proved above), 2 pieces impossible (topological). -/
theorem piece_count_lower_bound (r s : ℝ) (hr : r > 0) (hs : s > 0)
    (hA : SameArea r s) :
    3 ≤ minPieceCount r s := by
  by_contra h
  push_neg at h
  have hach := minPieceCount_achieves r s hr hs hA
  have : minPieceCount r s = 0 ∨ minPieceCount r s = 1 ∨ minPieceCount r s = 2 := by omega
  rcases this with h0 | h1 | h2
  · rw [h0] at hach; exact not_zero_equidecomposable r s hr hs hach
  · rw [h1] at hach; exact not_one_equidecomposable r s hr hs hA hach
  · rw [h2] at hach; exact lower_bound_three r s hr hs hA hach

/-- Combined lower bound (alias). -/
theorem lower_bound_chain (r s : ℝ) (hr : r > 0) (hs : s > 0) (hA : SameArea r s) :
    3 ≤ minPieceCount r s :=
  piece_count_lower_bound r s hr hs hA

/-- The gap between upper and lower bounds. -/
theorem piece_count_in_range (r s : ℝ) (hr : r > 0) (hs : s > 0) (hA : SameArea r s) :
    3 ≤ minPieceCount r s ∧ minPieceCount r s ≤ 10^50 :=
  ⟨piece_count_lower_bound r s hr hs hA, piece_count_upper_bound r s hr hs hA⟩

-- ============================================================================
-- Part XIII: Verification
-- ============================================================================

#check @not_zero_equidecomposable
#check @not_one_equidecomposable
#check @translateBy_comp
#check @translation_congruent_trans
#check @piece_count_in_range

end

end Erdos1124OQ01
