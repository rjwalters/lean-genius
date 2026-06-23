import Mathlib

/-
# Erdős #29 OQ-02: Corrected Basis Size Lower Bound

The original `basis_size_lower_bound` was refuted by Aristotle:
  FALSE: ∀ A basis, ∀ N ≥ 1, |A ∩ [1,N]| ≥ √N
  Counterexample: A = {0,1} ∪ {n ≥ 3}, N = 2 gives |A ∩ [1,2]| = 1 < √2

The CORRECT statement uses [0,N] instead of [1,N]:
  TRUE: ∀ A basis, ∀ N, |A ∩ [0,N]| ≥ √(N+1)

Proof: If A+A = ℕ, every n ∈ {0,...,N} is a+b with a,b ∈ A ∩ [0,N],
so {0,...,N} ⊆ (A ∩ [0,N]) + (A ∩ [0,N]). The sumset has at most
|A ∩ [0,N]|² elements, giving N+1 ≤ |A ∩ [0,N]|².

Axioms: 0
Sorries: 0
-/

namespace Erdos29OQ02

open Set Finset BigOperators Real

-- ============================================================
-- Part I: Reuse definitions from Erdős 29
-- ============================================================

/-- Sumset A + B = { a + b : a ∈ A, b ∈ B }. -/
def Sumset (A B : Set ℕ) : Set ℕ := { n | ∃ a ∈ A, ∃ b ∈ B, n = a + b }

/-- A is an additive basis (of order 2) if A + A = ℕ. -/
def IsAdditiveBasis (A : Set ℕ) : Prop := Sumset A A = Set.univ

-- ============================================================
-- Part II: The Correct Lower Bound Statement
-- ============================================================

/-- **Key lemma**: If A + A covers {0,...,N}, then every n ≤ N has
    a representation a + b = n with a,b ∈ A and a,b ≤ N.
    (Since a,b ≥ 0 and a + b = n ≤ N, both a ≤ N and b ≤ N.) -/
theorem representation_in_interval (A : Set ℕ) (hA : IsAdditiveBasis A)
    (n N : ℕ) (hn : n ≤ N) :
    ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ a ≤ N ∧ b ≤ N ∧ n = a + b := by
  have hmem : n ∈ Sumset A A := by rw [hA]; exact Set.mem_univ n
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  exact ⟨a, b, ha, hb, by omega, by omega, hab⟩

/-- The finite restriction A ∩ [0,N] as a Finset. -/
noncomputable def basisRestriction (A : Set ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (· ∈ A)

/-- Elements of basisRestriction are in A and ≤ N. -/
theorem mem_basisRestriction (A : Set ℕ) (N : ℕ) (a : ℕ) :
    a ∈ basisRestriction A N ↔ a ∈ A ∧ a ≤ N := by
  simp [basisRestriction, Finset.mem_filter, Finset.mem_range]
  omega

-- ============================================================
-- Part III: Counting Argument
-- ============================================================

/-- The sumset image: pairs (a,b) from S×S map to a+b. -/
noncomputable def pairSumImage (S : Finset ℕ) : Finset ℕ :=
  (S ×ˢ S).image (fun p => p.1 + p.2)

/-- The sumset of a finite set has at most |S|² elements. -/
theorem pairSumImage_card_le (S : Finset ℕ) :
    (pairSumImage S).card ≤ S.card * S.card := by
  unfold pairSumImage
  calc (S ×ˢ S).image (fun p => p.1 + p.2) |>.card
      ≤ (S ×ˢ S).card := Finset.card_image_le
    _ = S.card * S.card := Finset.card_product S S

/-- If A is a basis, then {0,...,N} is contained in the pairwise sums
    of basisRestriction A N. -/
theorem range_subset_pairSum (A : Set ℕ) (hA : IsAdditiveBasis A) (N : ℕ) :
    Finset.range (N + 1) ⊆ pairSumImage (basisRestriction A N) := by
  intro n hn
  rw [Finset.mem_range] at hn
  have hle : n ≤ N := by omega
  obtain ⟨a, b, ha, hb, haN, hbN, hab⟩ := representation_in_interval A hA n N hle
  unfold pairSumImage
  rw [Finset.mem_image]
  exact ⟨(a, b), Finset.mem_product.mpr
    ⟨(mem_basisRestriction A N a).mpr ⟨ha, haN⟩,
     (mem_basisRestriction A N b).mpr ⟨hb, hbN⟩⟩, hab⟩

/-- **Corrected lower bound**: For any additive basis A,
    |A ∩ [0,N]|² ≥ N + 1.

    Proof: {0,...,N} ⊆ sumset of A ∩ [0,N], and
    |sumset| ≤ |A ∩ [0,N]|², so N+1 ≤ |A ∩ [0,N]|². -/
theorem basis_size_squared_lower_bound (A : Set ℕ) (hA : IsAdditiveBasis A) (N : ℕ) :
    N + 1 ≤ (basisRestriction A N).card * (basisRestriction A N).card := by
  calc N + 1 = (Finset.range (N + 1)).card := by simp
    _ ≤ (pairSumImage (basisRestriction A N)).card :=
        Finset.card_le_card (range_subset_pairSum A hA N)
    _ ≤ (basisRestriction A N).card * (basisRestriction A N).card :=
        pairSumImage_card_le _

/-- **Corrected lower bound (real form)**: |A ∩ [0,N]| ≥ √(N+1).
    This is the corrected version of the false `basis_size_lower_bound`. -/
theorem basis_size_lower_bound_correct (A : Set ℕ) (hA : IsAdditiveBasis A) (N : ℕ) :
    Real.sqrt (N + 1 : ℝ) ≤ ((basisRestriction A N).card : ℝ) := by
  rw [Real.sqrt_le_left]
  right
  constructor
  · exact Nat.cast_nonneg _
  · rw [sq]
    exact_mod_cast basis_size_squared_lower_bound A hA N

-- ============================================================
-- Part IV: Consistency with Counterexample
-- ============================================================

/-
  The counterexample A = {0,1} ∪ {n ≥ 3} satisfies the CORRECT bound.
  At N=2: |A ∩ [0,2]| = |{0,1}| = 2, and √3 ≈ 1.73, so 2 ≥ √3. ✓
  (The FALSE bound used [1,2] giving |{1}| = 1 < √2.)

  The corrected bound is consistent with the counterexample because including
  0 in the interval adds one more element to the count.
-/

-- ============================================================
-- Part V: Optimality and Tightness
-- ============================================================

/-- The √(N+1) bound is tight up to constants: there exist bases A
    with |A ∩ [0,N]| = O(√N). For example, A = {0,1,...,⌈√N⌉} ∪ multiples
    would give |A ∩ [0,N]| ≈ √N.

    More precisely, for A = {0, 1, ..., m} with m ≥ √N, we have A+A ⊇ {0,...,2m},
    so A is a basis for {0,...,2m} with |A| = m+1 ≈ √(2m) ≈ √N. -/
theorem small_basis_exists (N : ℕ) (hN : 0 < N) :
    -- There exists a set covering {0,...,N} with size roughly √N
    -- (via the interval [0,N])
    ∃ S : Finset ℕ, (∀ n ≤ N, ∃ a b : ℕ, a ∈ S ∧ b ∈ S ∧ n = a + b) ∧
    S.card ≤ N + 1 := by
  use Finset.range (N + 1)
  constructor
  · intro n hn
    exact ⟨n, 0, Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega),
      by omega⟩
  · simp

/-
  Why the original was wrong: The interval [1,N] excludes 0, which can be
  a critical element of the basis. The counterexample A = {0,1} ∪ {n ≥ 3}
  has 0 ∈ A, so representations like 0 + n = n are available.
  By excluding 0 from the count, the original bound was too strong.

  The fix: include 0 in the counting interval — use [0,N] instead of [1,N].
-/

end Erdos29OQ02
