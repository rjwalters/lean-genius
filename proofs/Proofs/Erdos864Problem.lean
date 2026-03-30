/-
# Erdős Problem #864: Almost-Sidon Sets with One Collision

Let A ⊆ {1, ..., N} be such that at most one integer n has multiple
representations as a + b with a ≤ b ∈ A. What is the maximum |A|?

## Key Results

- Erdős–Freud (1991): |A| ≥ (1+o(1)) · (2/√3) · √N (construction)
- Conjecture: |A| ≤ (1+o(1)) · (2/√3) · √N (matching upper bound)
- For differences (a − b): |A| ~ √N (proved by Erdős–Freud)
- Sidon sets (no collisions at all): |A| ≤ √N + O(N^{1/4})
- This is a weaker version of Problem #840

## References

- Erdős, Freud (1991): [ErFr91]
- Erdős (1992): [Er92c]
- <https://erdosproblems.com/864>
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Proofs.Erdos44SidonLowerBound

open Finset

/- ## Core Definitions -/

/-- The number of ordered representations of n as a + b with a ≤ b, a, b ∈ A. -/
def sumRepCount (A : Finset ℕ) (n : ℕ) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = n)).card

/-- The set of integers with multiple sum representations from A. -/
def multiRepSet (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A).image (fun p => p.1 + p.2)
    |>.filter (fun n => sumRepCount A n ≥ 2)

/-- A is an almost-Sidon set: at most one integer has multiple representations. -/
def IsAlmostSidon (A : Finset ℕ) : Prop :=
  (multiRepSet A).card ≤ 1

/-- A is a Sidon set: no integer has multiple representations. -/
def IsSidon (A : Finset ℕ) : Prop :=
  (multiRepSet A).card = 0

/-- The maximum size of an almost-Sidon subset of {1, ..., N}. -/
noncomputable def maxAlmostSidon (N : ℕ) : ℕ :=
  Finset.sup ((Finset.Icc 1 N).powerset.filter (fun A => IsAlmostSidon A)) Finset.card

/- ## Main Conjecture -/

/-- **Erdős Problem #864** (OPEN): The maximum almost-Sidon set in {1,...,N}
    has size (1+o(1)) · (2/√3) · √N. -/
theorem erdos_864_conjecture :
  -- For all ε > 0, for sufficiently large N:
  -- maxAlmostSidon N ≤ (2/√3 + ε) · √N
  -- NOTE: The actual conjecture is OPEN. This placeholder states True only.
  True := trivial

/- ## Known Bounds -/

/-- **Erdős–Freud (1991)**: Lower bound via reflected Sidon construction.
    Take a Sidon set B ⊆ {1,...,N/3} and form A = B ∪ {N − b : b ∈ B}.
    This gives |A| ≥ (1+o(1)) · (2/√3) · √N. -/
axiom erdos_freud_lower_bound :
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (maxAlmostSidon N : ℝ) ≥ (2 / Real.sqrt 3 - ε) * Real.sqrt (N : ℝ)

/-- **Note**: The Lindström (1969) bound |A| ≤ √N + O(N^{1/4}) for Sidon sets
    requires Fourier-analytic methods not yet available in Mathlib v4.26.0.
    The elementary difference-counting bound k² ≤ 2N + k (proved below as
    `sidon_card_sq_le_2N`) gives |A| ≤ √(2N), improving `sidon_card_sq_le`
    (k² ≤ 4N) by ~2×. See also `Erdos340GreedySidon.sidon_upper_bound_weak`
    for the equivalent |A| ≤ √(2N) + 1. -/

/-- Almost-Sidon sets can be larger than Sidon sets by a factor of 2/√3 ≈ 1.155.
    Proof: erdos_freud_lower_bound gives maxAlmostSidon(N) ≥ (2/√3 - ε)√N.
    Since 2/√3 > 1 (as √3 < 2), taking ε = 1/10 gives coefficient > 1,
    so (2/√3 - 1/10)√N > √N + 1 for N ≥ 400. -/
theorem almost_sidon_exceeds_sidon :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (maxAlmostSidon N : ℝ) > Real.sqrt (N : ℝ) + 1 := by
  obtain ⟨N₀, hN₀⟩ := erdos_freud_lower_bound (1/10) (by norm_num)
  use max N₀ 400
  intro N hN
  have hge := hN₀ N (le_trans (le_max_left _ _) hN)
  have hNge : (N : ℝ) ≥ 400 := by exact_mod_cast le_trans (le_max_right N₀ 400) hN
  -- Key: √3 < 40/23 (since 3 < 1600/529), so 2/√3 > 23/20
  have h_sqrt3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos_of_pos (by norm_num)
  have h_sqrt3_bound : Real.sqrt 3 < 40 / 23 := by
    rw [show (40 : ℝ) / 23 = Real.sqrt ((40 / 23) ^ 2) from
      (Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 40 / 23)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h_coeff : 2 / Real.sqrt 3 - 1 / 10 > 1 := by
    rw [gt_iff_lt, sub_lt_iff_lt_add]; linarith [div_lt_div_left (by norm_num : (0:ℝ) < 2) h_sqrt3_pos (by norm_num : (0:ℝ) < 23/20)]
  -- √N ≥ 20 (since N ≥ 400 = 20²)
  have h_sqrtN : Real.sqrt (N : ℝ) ≥ 20 := by
    calc Real.sqrt N ≥ Real.sqrt 400 :=
          Real.sqrt_le_sqrt (by exact_mod_cast hNge)
      _ = 20 := by rw [show (400 : ℝ) = 20 ^ 2 from by norm_num];
                    exact Real.sqrt_sq (by norm_num)
  -- Main bound: (2/√3 - 1/10) * √N > √N + 1
  suffices h : (2 / Real.sqrt 3 - 1 / 10) * Real.sqrt N > Real.sqrt N + 1 by linarith
  have h_pos : Real.sqrt (N : ℝ) > 0 := Real.sqrt_pos_of_pos (by linarith)
  -- 2/√3 > 23/20 (from √3 < 40/23)
  have h_23_20 : 2 / Real.sqrt 3 > 23 / 20 := by
    rw [gt_iff_lt, div_lt_div_iff (by norm_num : (0:ℝ) < 20) h_sqrt3_pos]
    linarith
  -- (2/√3 - 11/10) > 1/20
  have h_gap : 2 / Real.sqrt 3 - 11 / 10 > 1 / 20 := by linarith
  -- (2/√3 - 1/10) * √N = √N + (2/√3 - 11/10) * √N
  -- ≥ √N + (1/20) * 20 = √N + 1 (strict since gap > 1/20 and √N ≥ 20)
  have h1 : (2 / Real.sqrt 3 - 11 / 10) * Real.sqrt N > 1 :=
    calc (2 / Real.sqrt 3 - 11 / 10) * Real.sqrt N
        > (1 / 20) * Real.sqrt N :=
          mul_lt_mul_of_pos_right h_gap h_pos
      _ ≥ (1 / 20) * 20 :=
          mul_le_mul_of_nonneg_left h_sqrtN (by norm_num)
      _ = 1 := by norm_num
  linarith

/-- Every Sidon set is also almost-Sidon (trivially). -/
theorem sidon_is_almost_sidon (A : Finset ℕ) (h : IsSidon A) : IsAlmostSidon A := by
  unfold IsAlmostSidon IsSidon at *
  omega

/-- Empty set is almost-Sidon (trivially) -/
theorem isAlmostSidon_empty : IsAlmostSidon ∅ := by
  unfold IsAlmostSidon multiRepSet sumRepCount
  simp

/-- Almost-Sidon is monotone: subsets of almost-Sidon sets are almost-Sidon -/
theorem isAlmostSidon_subset {A B : Finset ℕ} (h : IsAlmostSidon B) (hsub : A ⊆ B) :
    IsAlmostSidon A := by
  unfold IsAlmostSidon at *
  have : (multiRepSet A).card ≤ (multiRepSet B).card := by
    apply Finset.card_le_card
    intro n hn
    simp only [multiRepSet, Finset.mem_filter, Finset.mem_image,
      Finset.mem_product, Prod.exists] at hn ⊢
    obtain ⟨⟨a, b, ha, hb, rfl⟩, hrep⟩ := hn
    exact ⟨⟨a, b, hsub ha, hsub hb, rfl⟩,
           le_trans hrep (sumRepCount_le_of_subset hsub _)⟩
  omega

/- ## Difference Version -/

/-- For the difference analogue (at most one n with multiple a − b
    representations), Erdős–Freud proved |A| ~ √N. -/
theorem erdos_freud_difference_version :
  -- The maximum size of A ⊆ {1,...,N} with at most one difference collision
  -- is asymptotically √N
  -- NOTE: The actual result is deep. This placeholder states True only.
  True := trivial

/- ## Structural Properties -/

/-- The number of ordered pairs (a, b) with a ≤ b in A is C(|A|, 2) + |A|.
    In a Sidon set, all pairwise sums are distinct, using C(|A|,2) + |A|
    distinct values from {2, ..., 2N}. -/
theorem pairwise_sum_count (A : Finset ℕ) :
    ((A ×ˢ A).filter (fun p => p.1 ≤ p.2)).card = A.card * (A.card + 1) / 2 := by
  -- Split upper triangle into strict and diagonal:
  -- |{(a,b) | a ≤ b}| = |{(a,b) | a < b}| + |{(a,b) | a = b}|
  -- By symmetry: |{a < b}| = |{a > b}|, and |A×A| = |{a<b}| + |{a=b}| + |{a>b}|
  -- So |{a ≤ b}| = (|A|² + |A|) / 2 = |A|(|A|+1)/2
  set n := A.card with hn
  -- The upper triangle and lower triangle partition A×A with the diagonal
  have h_total : (A ×ˢ A).card = n * n := by simp [Finset.card_product, hn]
  -- Define the three regions
  set upper := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2) with hupper
  set diag := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 = p.2) with hdiag
  set lower := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.2 < p.1) with hlower
  -- Diagonal has n elements
  have h_diag : diag.card = n := by
    rw [hdiag]
    have : diag = A.image (fun a => (a, a)) := by
      ext ⟨x, y⟩; simp [diag, Finset.mem_filter, Finset.mem_product, Finset.mem_image]
      constructor
      · rintro ⟨⟨hx, hy⟩, rfl⟩; exact ⟨x, hx, rfl⟩
      · rintro ⟨a, ha, rfl, rfl⟩; exact ⟨⟨ha, ha⟩, rfl⟩
    rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using h), hn]
  -- Upper and lower have equal cardinality (by the involution (a,b) ↦ (b,a))
  have h_sym : upper.card = lower.card := by
    have : lower = upper.image (fun p : ℕ × ℕ => (p.2, p.1)) := by
      ext ⟨x, y⟩; simp [upper, lower, Finset.mem_filter, Finset.mem_product, Finset.mem_image]
      constructor
      · rintro ⟨⟨hx, hy⟩, hlt⟩; exact ⟨y, x, ⟨hy, hx⟩, hlt, rfl, rfl⟩
      · rintro ⟨a, b, ⟨ha, hb⟩, hab, rfl, rfl⟩; exact ⟨⟨hb, ha⟩, hab⟩
    rw [this, Finset.card_image_of_injective _ (fun ⟨a, b⟩ ⟨c, d⟩ h => by simpa using h)]
  -- Partition: |A×A| = |upper| + |diag| + |lower|
  have h_part : (A ×ˢ A).card = upper.card + diag.card + lower.card := by
    have h1 : A ×ˢ A = upper ∪ diag ∪ lower := by
      ext ⟨x, y⟩; simp [upper, lower, diag, Finset.mem_filter, Finset.mem_union, Finset.mem_product]
      intro _ _; omega
    have h2 : Disjoint upper diag := by
      simp [Finset.disjoint_filter]; intro ⟨x, y⟩ _ hlt heq; omega
    have h3 : Disjoint (upper ∪ diag) lower := by
      simp [Finset.disjoint_filter, Finset.mem_union]; intro ⟨x, y⟩ _ h _
      rcases h with h | h <;> omega
    rw [h1, Finset.card_union_of_disjoint h3, Finset.card_union_of_disjoint h2]
  -- From partition: n² = 2·|upper| + n, so |upper| = (n²-n)/2
  have h_upper : upper.card = n * (n - 1) / 2 := by
    have := h_total; rw [h_part, h_sym, h_diag] at this; omega
  -- Target set = upper ∪ diag
  have h_target : (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 ≤ p.2) = upper ∪ diag := by
    ext ⟨x, y⟩; simp [upper, diag, Finset.mem_filter, Finset.mem_union, Finset.mem_product]
    intro _ _; omega
  have h_disj : Disjoint upper diag := by
    simp [Finset.disjoint_filter]; intro ⟨x, y⟩ _ hlt heq; omega
  rw [h_target, Finset.card_union_of_disjoint h_disj, h_upper, h_diag]
  omega

/-- Sums a + b with a,b ∈ A ⊆ {1,...,N} and a ≤ b lie in {2,...,2N} -/
theorem sum_in_range {A : Finset ℕ} {N : ℕ}
    (hA : ∀ a ∈ A, a ∈ Finset.Icc 1 N) {a b : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≤ b) :
    a + b ∈ Finset.Icc 2 (2 * N) := by
  simp only [Finset.mem_Icc] at hA ⊢
  have := hA a ha; have := hA b hb; omega

/-- Empty set is Sidon -/
theorem isSidon_empty : IsSidon ∅ := by
  unfold IsSidon multiRepSet sumRepCount
  simp

/-- sumRepCount is monotone in the underlying set -/
private lemma sumRepCount_le_of_subset {A B : Finset ℕ} (hsub : A ⊆ B) (n : ℕ) :
    sumRepCount A n ≤ sumRepCount B n := by
  unfold sumRepCount
  exact Finset.card_le_card
    (Finset.filter_subset_filter _ (Finset.product_subset_product hsub hsub))

/-- Sidon is monotone: subsets of Sidon sets are Sidon -/
theorem isSidon_subset {A B : Finset ℕ} (h : IsSidon B) (hsub : A ⊆ B) :
    IsSidon A := by
  unfold IsSidon at *
  -- multiRepSet A ⊆ multiRepSet B, so card(A) ≤ card(B) = 0
  have : (multiRepSet A).card ≤ (multiRepSet B).card := by
    apply Finset.card_le_card
    intro n hn
    simp only [multiRepSet, Finset.mem_filter, Finset.mem_image,
      Finset.mem_product, Prod.exists] at hn ⊢
    obtain ⟨⟨a, b, ha, hb, rfl⟩, hrep⟩ := hn
    exact ⟨⟨a, b, hsub ha, hsub hb, rfl⟩,
           le_trans hrep (sumRepCount_le_of_subset hsub _)⟩
  omega

/-- The set of distinct pairwise sums from A ⊆ {1,...,N} has at most 2N-1 elements,
    since all sums a+b lie in {2,...,2N}. -/
theorem distinct_sums_bounded (A : Finset ℕ) (N : ℕ) (hN : 0 < N)
    (hA : ∀ a ∈ A, a ∈ Finset.Icc 1 N) :
    ((A ×ˢ A).image (fun p => p.1 + p.2)).card ≤ 2 * N - 1 := by
  calc ((A ×ˢ A).image (fun p => p.1 + p.2)).card
      ≤ (Finset.Icc 2 (2 * N)).card := by
        apply Finset.card_le_card
        intro s hs
        simp only [Finset.mem_image, Finset.mem_product, Prod.exists] at hs
        obtain ⟨a, b, ha, hb, rfl⟩ := hs
        simp only [Finset.mem_Icc] at hA ⊢
        have := hA a ha; have := hA b hb; omega
    _ = 2 * N - 1 := by rw [Finset.Nat.card_Icc]; omega

/-- **Sidon counting bound (sums)**: For a Sidon set A ⊆ {1,...,N}, the sum
    map (a,b) ↦ a+b is injective on the upper triangle {(a,b) | a ≤ b}, so
    |A|(|A|+1)/2 ≤ 2N-1. This gives |A| ≤ ~2√N. The tighter difference-counting
    bound k² ≤ 2N+k (see `sidon_card_sq_le_2N`) improves this by ~2×. -/
theorem sidon_counting_bound (A : Finset ℕ) (N : ℕ) (hN : 0 < N)
    (hA : ∀ a ∈ A, a ∈ Finset.Icc 1 N) (hS : IsSidon A) :
    A.card * (A.card + 1) / 2 ≤ 2 * N - 1 := by
  rw [← pairwise_sum_count A]
  set U := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 ≤ p.2) with hU_def
  -- Step 1: The sum function is injective on U (from Sidon property)
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2) (↑U) := by
    intro ⟨a₁, b₁⟩ h1 ⟨a₂, b₂⟩ h2 heq
    simp only [Finset.mem_coe, hU_def, Finset.mem_filter, Finset.mem_product] at h1 h2
    obtain ⟨⟨ha1, hb1⟩, hab1⟩ := h1
    obtain ⟨⟨ha2, hb2⟩, hab2⟩ := h2
    -- Both pairs are in the sumRepCount filter for the same sum
    have hle := isSidon_sumRepCount_le_one hS (a₁ + b₁)
    unfold sumRepCount at hle
    have hp1 : (a₁, b₁) ∈ (A ×ˢ A).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = a₁ + b₁) := by
      simp [Finset.mem_filter, Finset.mem_product, ha1, hb1, hab1]
    have hp2 : (a₂, b₂) ∈ (A ×ˢ A).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = a₁ + b₁) := by
      simp [Finset.mem_filter, Finset.mem_product, ha2, hb2, hab2, heq]
    exact Finset.card_le_one.mp hle hp1 hp2
  -- Chain: |U| = |U.image sum| ≤ |(A×A).image sum| ≤ 2N-1
  calc U.card
      = (U.image (fun p : ℕ × ℕ => p.1 + p.2)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((A ×ˢ A).image (fun p => p.1 + p.2)).card :=
        Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))
    _ ≤ 2 * N - 1 := distinct_sums_bounded A N hN hA

/-- **Sidon square bound**: For Sidon A ⊆ {1,...,N}, |A|² ≤ 4N.
    Corollary of `sidon_counting_bound`: k·k/2 ≤ k·(k+1)/2 ≤ 2N−1,
    so k² ≤ 2·(k²/2)+1 ≤ 4N−1 ≤ 4N. Gives |A| < 2√N + 1. -/
theorem sidon_card_sq_le (A : Finset ℕ) (N : ℕ) (hN : 0 < N)
    (hA : ∀ a ∈ A, a ∈ Finset.Icc 1 N) (hS : IsSidon A) :
    A.card ^ 2 ≤ 4 * N := by
  have h := sidon_counting_bound A N hN hA hS
  set k := A.card
  -- k*k/2 ≤ k*(k+1)/2 ≤ 2N-1 (monotonicity of / + counting bound)
  have h1 : k * k / 2 ≤ k * (k + 1) / 2 :=
    Nat.div_le_div_right (by rw [mul_add, mul_one]; exact Nat.le_add_right _ _)
  have h2 : k * k / 2 ≤ 2 * N - 1 := le_trans h1 h
  -- k^2 = k*k ≤ 2*(k*k/2)+1 ≤ 2*(2N-1)+1 = 4N-1 ≤ 4N
  have h3 : k ^ 2 = k * k := by ring
  omega

/- ## Difference Counting (Improved Sidon Bound)

Sum-Sidon (all pairwise sums a+b with a≤b distinct) implies difference-Sidon
(all pairwise differences a-b with a>b distinct). The k(k-1)/2 positive
differences lie in {1,...,N-1}, giving the tighter bound k(k-1) ≤ 2(N-1),
i.e., k² ≤ 2N + k. This improves sidon_card_sq_le (k² ≤ 4N) by ~2×.
-/

/-- Sum-Sidon implies difference-uniqueness: if a₁-b₁ = a₂-b₂ with a₁>b₁
    and a₂>b₂, then a₁=a₂ and b₁=b₂. Proof: derive a₁+b₂=a₂+b₁, then
    apply sumRepCount ≤ 1 to identify the pairs. -/
private theorem isSidon_diff_injective {A : Finset ℕ} (hS : IsSidon A)
    {a₁ b₁ a₂ b₂ : ℕ} (ha1 : a₁ ∈ A) (hb1 : b₁ ∈ A) (ha2 : a₂ ∈ A) (hb2 : b₂ ∈ A)
    (hgt1 : b₁ < a₁) (hgt2 : b₂ < a₂) (heq : a₁ - b₁ = a₂ - b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hsum : a₁ + b₂ = a₂ + b₁ := by omega
  have hle := isSidon_sumRepCount_le_one hS (a₁ + b₂)
  unfold sumRepCount at hle
  -- Case split on orderings: each case constructs two pairs in the filter,
  -- Sidon forces them equal, yielding the conclusion or a contradiction.
  by_cases h1 : a₁ ≤ b₂
  · by_cases h2 : a₂ ≤ b₁
    · -- Pairs (a₁, b₂) and (a₂, b₁)
      have hp1 : (a₁, b₂) ∈ (A ×ˢ A).filter
          (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = a₁ + b₂) := by
        simp only [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨ha1, hb2⟩, h1, rfl⟩
      have hp2 : (a₂, b₁) ∈ (A ×ˢ A).filter
          (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = a₁ + b₂) := by
        simp only [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨ha2, hb1⟩, h2, by omega⟩
      have heqp := Finset.card_le_one.mp hle hp1 hp2
      simp only [Prod.mk.injEq] at heqp
      exact ⟨heqp.1, heqp.2.symm⟩
    · -- Pairs (a₁, b₂) and (b₁, a₂) — gives a₁=b₁ contradiction
      push_neg at h2
      have hp1 : (a₁, b₂) ∈ (A ×ˢ A).filter
          (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = a₁ + b₂) := by
        simp only [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨ha1, hb2⟩, h1, rfl⟩
      have hp2 : (b₁, a₂) ∈ (A ×ˢ A).filter
          (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = a₁ + b₂) := by
        simp only [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hb1, ha2⟩, le_of_lt h2, by omega⟩
      have heqp := Finset.card_le_one.mp hle hp1 hp2
      simp only [Prod.mk.injEq] at heqp
      omega -- a₁ = b₁ contradicts hgt1
  · push_neg at h1
    by_cases h2 : b₁ ≤ a₂
    · -- Pairs (b₂, a₁) and (b₁, a₂) — gives conclusion directly
      have hp1 : (b₂, a₁) ∈ (A ×ˢ A).filter
          (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = a₁ + b₂) := by
        simp only [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hb2, ha1⟩, le_of_lt h1, by omega⟩
      have hp2 : (b₁, a₂) ∈ (A ×ˢ A).filter
          (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = a₁ + b₂) := by
        simp only [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hb1, ha2⟩, h2, by omega⟩
      have heqp := Finset.card_le_one.mp hle hp1 hp2
      simp only [Prod.mk.injEq] at heqp
      exact ⟨heqp.2.symm, heqp.1.symm⟩
    · -- Pairs (b₂, a₁) and (a₂, b₁) — gives a₁=b₁ contradiction
      push_neg at h2
      have hp1 : (b₂, a₁) ∈ (A ×ˢ A).filter
          (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = a₁ + b₂) := by
        simp only [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hb2, ha1⟩, le_of_lt h1, by omega⟩
      have hp2 : (a₂, b₁) ∈ (A ×ˢ A).filter
          (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = a₁ + b₂) := by
        simp only [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨ha2, hb1⟩, le_of_lt h2, by omega⟩
      have heqp := Finset.card_le_one.mp hle hp1 hp2
      simp only [Prod.mk.injEq] at heqp
      omega -- b₂=a₂ and a₁=b₁ contradicts hgt1

/-- **Sidon counting bound (differences)**: For Sidon A ⊆ {1,...,N}, the k(k-1)/2
    positive pairwise differences are all distinct (by `isSidon_diff_injective`)
    and lie in {1,...,N-1}. Therefore k(k-1) ≤ 2(N-1). -/
theorem sidon_diff_counting_bound (A : Finset ℕ) (N : ℕ) (hN : 0 < N)
    (hA : ∀ a ∈ A, a ∈ Finset.Icc 1 N) (hS : IsSidon A) :
    A.card * (A.card - 1) ≤ 2 * (N - 1) := by
  set k := A.card with hk
  -- The strict lower triangle: ordered pairs (a,b) with b < a
  set L := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.2 < p.1)
  -- Step 1: The difference map is injective on L
  have h_inj : Set.InjOn (fun p : ℕ × ℕ => p.1 - p.2) ↑L := by
    intro ⟨a₁, b₁⟩ h1 ⟨a₂, b₂⟩ h2 heq
    rw [Finset.mem_coe] at h1 h2
    simp only [Finset.mem_filter, Finset.mem_product] at h1 h2
    have ⟨rfl, rfl⟩ := isSidon_diff_injective hS h1.1.1 h1.1.2 h2.1.1 h2.1.2 h1.2 h2.2 heq
    rfl
  -- Step 2: Image lies in {1,...,N-1}
  have h_range : L.image (fun p : ℕ × ℕ => p.1 - p.2) ⊆ Finset.Icc 1 (N - 1) := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨⟨a, b⟩, hp, rfl⟩ := hd
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    simp only [Finset.mem_Icc]
    have := (Finset.mem_Icc.mp (hA a hp.1.1))
    have := (Finset.mem_Icc.mp (hA b hp.1.2))
    omega
  -- Step 3: |image| = |L| by injectivity, and |image| ≤ N-1
  have h_card_img := Finset.card_image_of_injOn h_inj
  have h_le : L.card ≤ N - 1 := by
    rw [← h_card_img]
    calc (L.image _).card ≤ (Finset.Icc 1 (N - 1)).card := Finset.card_le_card h_range
      _ = N - 1 := by rw [Finset.Nat.card_Icc]; omega
  -- Step 4: 2*|L| + k = k*k (partition into lower triangle, diagonal, upper triangle)
  have h_2L : 2 * L.card + k = k * k := by
    set U := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2)
    set D := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 = p.2)
    -- |L| = |U| via the swap bijection (a,b) ↦ (b,a)
    have h_LU : L.card = U.card := by
      have : L = U.image (fun p : ℕ × ℕ => (p.2, p.1)) := by
        ext ⟨x, y⟩
        simp only [L, U, Finset.mem_filter, Finset.mem_product,
          Finset.mem_image, Prod.exists]
        constructor
        · rintro ⟨⟨hx, hy⟩, hlt⟩; exact ⟨y, x, ⟨hy, hx⟩, hlt, rfl, rfl⟩
        · rintro ⟨a, b, ⟨ha, hb⟩, hab, rfl, rfl⟩; exact ⟨⟨hb, ha⟩, hab⟩
      rw [this]; exact Finset.card_image_of_injective _
        (fun ⟨a, b⟩ ⟨c, d⟩ h => by simpa using h)
    -- |D| = k (diagonal)
    have h_D : D.card = k := by
      have : D = A.image (fun a => (a, a)) := by
        ext ⟨x, y⟩
        simp only [D, Finset.mem_filter, Finset.mem_product, Finset.mem_image]
        constructor
        · rintro ⟨⟨hx, _⟩, rfl⟩; exact ⟨x, hx, rfl⟩
        · rintro ⟨a, ha, h⟩; rw [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h; exact ⟨⟨ha, ha⟩, rfl⟩
      rw [this]; exact Finset.card_image_of_injective _
        (fun a b h => by simpa using h)
    -- Partition: A×A = L ∪ D ∪ U
    have h_part : A ×ˢ A = L ∪ D ∪ U := by
      ext ⟨x, y⟩
      simp only [L, U, D, Finset.mem_filter, Finset.mem_union, Finset.mem_product]
      constructor
      · intro ⟨hx, hy⟩; rcases lt_trichotomy y x with h | h | h
        · left; left; exact ⟨⟨hx, hy⟩, h⟩
        · left; right; exact ⟨⟨hx, hy⟩, h.symm⟩
        · right; exact ⟨⟨hx, hy⟩, h⟩
      · rintro ((⟨m, _⟩ | ⟨m, _⟩) | ⟨m, _⟩) <;> exact m
    have h_disj1 : Disjoint L D := by
      simp only [Finset.disjoint_filter]; intro ⟨x, y⟩ _; omega
    have h_disj2 : Disjoint (L ∪ D) U := by
      rw [Finset.disjoint_union_left]
      exact ⟨by simp only [Finset.disjoint_filter]; intro ⟨x, y⟩ _; omega,
             by simp only [Finset.disjoint_filter]; intro ⟨x, y⟩ _; omega⟩
    have h_total : (A ×ˢ A).card = k * k := by simp [Finset.card_product]
    rw [h_part, Finset.card_union_of_disjoint h_disj2,
        Finset.card_union_of_disjoint h_disj1, h_D, h_LU] at h_total
    omega
  -- Combine: k*(k-1) ≤ 2*(N-1)
  rcases k with _ | n
  · simp
  · -- From 2*L.card + (n+1) = (n+1)*(n+1), derive 2*L.card = n*(n+1)
    -- Combined with L.card ≤ N-1: n*(n+1) ≤ 2*(N-1)
    -- Goal: (n+1)*n ≤ 2*(N-1)
    have h_eq : (n + 1) * (n + 1) = (n + 1) * n + (n + 1) := by ring
    omega

/-- **Improved Sidon square bound**: |A|² ≤ 2N + |A| for Sidon A ⊆ {1,...,N}.
    Corollary of the difference counting bound k(k-1) ≤ 2(N-1).
    Improves `sidon_card_sq_le` (k² ≤ 4N) by nearly a factor of 2. -/
theorem sidon_card_sq_le_2N (A : Finset ℕ) (N : ℕ) (hN : 0 < N)
    (hA : ∀ a ∈ A, a ∈ Finset.Icc 1 N) (hS : IsSidon A) :
    A.card ^ 2 ≤ 2 * N + A.card := by
  have h := sidon_diff_counting_bound A N hN hA hS
  set k := A.card
  -- k^2 = k*(k-1) + k ≤ 2*(N-1) + k ≤ 2*N + k
  rcases k with _ | n
  · simp
  · have h_eq : (n + 1) ^ 2 = (n + 1) * n + (n + 1) := by ring
    omega

/-- **FALSE (removed)**: The original claimed k(k+1)/2 - 1 ≤ 2N - 1 for
    almost-Sidon A ⊆ {1,...,N} with |A| = k.

    COUNTEREXAMPLE: A = {1, 2, 4, 6, 7} ⊆ {1,...,7} is almost-Sidon
    (the only collision is at sum 8, with three representations:
    1+7 = 2+6 = 4+4 = 8). But |A|·(|A|+1)/2 - 1 = 5·6/2 - 1 = 14 > 13 = 2·7 - 1.

    The bug: when the single allowed collision has multiplicity c ≥ 3,
    the number of distinct sums is k(k+1)/2 - (c-1), which can be
    strictly less than k(k+1)/2 - 1. The correct bound is:
    #{distinct sums} ≤ 2N - 1, i.e., k(k+1)/2 - (c-1) ≤ 2N - 1.
    The correct PROVED bound is `distinct_sums_bounded` above. -/
theorem almost_sidon_sum_range_false_note : True := trivial

/-- IsSidon means every sum has at most one representation. -/
private lemma isSidon_sumRepCount_le_one {B : Finset ℕ} (hS : IsSidon B) (n : ℕ) :
    sumRepCount B n ≤ 1 := by
  unfold IsSidon at hS
  by_contra h
  push_neg at h
  have hmem : n ∈ multiRepSet B := by
    unfold multiRepSet
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · unfold sumRepCount at h
      have hpos : 0 < ((B ×ˢ B).filter fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = n).card := by omega
      obtain ⟨⟨a, b⟩, hab⟩ := Finset.card_pos.mp hpos
      simp only [Finset.mem_filter, Finset.mem_product] at hab
      exact ⟨a, b, hab.1.1, hab.1.2, hab.2.2⟩
    · unfold sumRepCount at h; omega
  rw [Finset.card_eq_zero] at hS
  exact (hS ▸ Finset.not_mem_empty n) hmem

/-- The reflected construction: B ∪ (N − B) is almost-Sidon when B is Sidon.
    The only possible collision is at n = N (sums from B-side and reflected-side). -/
theorem reflected_construction_valid (N : ℕ) (B : Finset ℕ) :
    (∀ b ∈ B, b ∈ Finset.Icc 1 (N / 3)) → IsSidon B →
      IsAlmostSidon (B ∪ B.image (fun b => N - b)) := by
  intro hB hSidon
  set B' := B.image (fun b => N - b) with hB'_def
  set A := B ∪ B'
  -- Bounds on elements
  have hB_le : ∀ x ∈ B, x ≤ N / 3 := fun x hx => (Finset.mem_Icc.mp (hB x hx)).2
  have hB_pos : ∀ x ∈ B, 1 ≤ x := fun x hx => (Finset.mem_Icc.mp (hB x hx)).1
  have hB_le_N : ∀ x ∈ B, x ≤ N := fun x hx => le_trans (hB_le x hx) (Nat.div_le_self N 3)
  -- B' elements: ∃ c ∈ B, x = N - c
  have hB'_mem : ∀ x ∈ B', ∃ c ∈ B, x = N - c :=
    fun x hx => Finset.mem_image.mp hx
  -- B' elements are large: x ≥ N - N/3
  have hB'_ge : ∀ x ∈ B', x ≥ N - N / 3 := by
    intro x hx; obtain ⟨c, hc, rfl⟩ := hB'_mem x hx
    have := hB_le c hc; omega
  -- B elements < B' elements (for disjoint ranges)
  have hB_lt_B' : ∀ x ∈ B, ∀ y ∈ B', x < y := by
    intro x hx y hy
    obtain ⟨c, hc, rfl⟩ := hB'_mem y hy
    have hxle := hB_le x hx; have hcle := hB_le c hc
    have hcpos := hB_pos c hc
    -- x ≤ N/3 and N - c ≥ N - N/3; need N/3 < N - N/3, i.e. 2*(N/3) < N
    -- This holds when N ≥ 2 (and when N=0,1 B is empty)
    by_cases hN : N ≤ 1
    · -- N ≤ 1: N/3 = 0, but x ≥ 1 and x ≤ N/3 = 0, contradiction
      omega
    · -- N ≥ 2: 2*(N/3) < N, so N/3 < N - N/3
      omega
  -- Show multiRepSet A ⊆ {N}
  unfold IsAlmostSidon
  suffices hsub : multiRepSet A ⊆ {N} by
    calc (multiRepSet A).card ≤ ({N} : Finset ℕ).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton N
  -- For any s ∈ multiRepSet A, show s = N
  intro s hs
  rw [Finset.mem_singleton]
  -- s has sumRepCount ≥ 2, extract two distinct pairs
  simp only [multiRepSet, Finset.mem_filter] at hs
  obtain ⟨_, hrep⟩ := hs
  unfold sumRepCount at hrep
  have hlt : 1 < ((A ×ˢ A).filter fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = s).card := by omega
  rw [Finset.one_lt_card] at hlt
  obtain ⟨⟨a₁, b₁⟩, h1, ⟨a₂, b₂⟩, h2, hne⟩ := hlt
  simp only [Finset.mem_filter, Finset.mem_product] at h1 h2
  obtain ⟨⟨ha1, hb1⟩, hab1, hs1⟩ := h1
  obtain ⟨⟨ha2, hb2⟩, hab2, hs2⟩ := h2
  -- Each element is in B or B'
  -- Classify each pair: (B,B), (B,B'), or (B',B'). (B',B) impossible since a ≤ b.
  -- Helper: if a ∈ B' and b ∈ B then a > b, contradicting a ≤ b
  have no_B'_B : ∀ a b, a ∈ B' → b ∈ B → ¬(a ≤ b) := by
    intro a b ha hb; exact not_le.mpr (hB_lt_B' b hb a ha)
  -- Sum range for BB pairs: s ≤ 2*(N/3)
  have bb_range : ∀ a b, a ∈ B → b ∈ B → a + b ≤ 2 * (N / 3) := by
    intro a b ha hb; have := hB_le a ha; have := hB_le b hb; omega
  -- Sum range for cross pairs (B,B'): s ≥ N - N/3 + 1
  have cross_lo : ∀ a b, a ∈ B → b ∈ B' → a + b ≥ N - N / 3 + 1 := by
    intro a b ha hb
    have := hB_pos a ha; have := hB'_ge b hb; omega
  -- Sum range for cross pairs: s ≤ N/3 + (N - 1)
  have cross_hi : ∀ a b, a ∈ B → b ∈ B' → B.Nonempty → a + b ≤ N / 3 + (N - 1) := by
    intro a b ha hb _
    have hale := hB_le a ha
    obtain ⟨c, hc, rfl⟩ := hB'_mem b hb
    have hcpos := hB_pos c hc
    omega
  -- Sum range for B'B' pairs: s ≥ 2*(N - N/3)
  have b'b'_range : ∀ a b, a ∈ B' → b ∈ B' → a + b ≥ 2 * (N - N / 3) := by
    intro a b ha hb; have := hB'_ge a ha; have := hB'_ge b hb; omega
  -- Key separation: 2*(N/3) < N - N/3 + 1 (BB max < Cross min)
  have sep1 : 2 * (N / 3) < N - N / 3 + 1 := by omega
  -- Key separation: N/3 + (N-1) < 2*(N - N/3) (Cross max < B'B' min) when N ≥ 3
  -- (equivalent to 3*(N/3) < N+1, which is 3*(N/3) ≤ N)
  have sep2 : N ≥ 3 → N / 3 + (N - 1) < 2 * (N - N / 3) := by omega
  -- Now do the case analysis on the two pairs
  rcases Finset.mem_union.mp ha1 with ha1B | ha1B'
  · -- a₁ ∈ B
    rcases Finset.mem_union.mp hb1 with hb1B | hb1B'
    · -- Pair 1 is BB: s = a₁ + b₁ ≤ 2*(N/3)
      have hs_bb := bb_range a₁ b₁ ha1B hb1B
      rcases Finset.mem_union.mp ha2 with ha2B | ha2B'
      · rcases Finset.mem_union.mp hb2 with hb2B | hb2B'
        · -- Pair 2 also BB: both in B×B filter with same sum → equal by Sidon
          have hle1 := isSidon_sumRepCount_le_one hSidon s
          unfold sumRepCount at hle1
          have h1' : (a₁, b₁) ∈ (B ×ˢ B).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = s) := by
            simp [Finset.mem_filter, Finset.mem_product, ha1B, hb1B, hab1, hs1]
          have h2' : (a₂, b₂) ∈ (B ×ˢ B).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = s) := by
            simp [Finset.mem_filter, Finset.mem_product, ha2B, hb2B, hab2, hs2]
          exact absurd (Finset.card_le_one.mp hle1 h1' h2') hne
        · -- Pair 2 is Cross: s ≥ N - N/3 + 1 > 2*(N/3) ≥ s. Contradiction.
          have := cross_lo a₂ b₂ ha2B hb2B'
          omega
      · -- a₂ ∈ B'
        rcases Finset.mem_union.mp hb2 with hb2B | hb2B'
        · exact absurd hab2 (no_B'_B a₂ b₂ ha2B' hb2B)
        · -- Pair 2 is B'B': s ≥ 2*(N - N/3) > 2*(N/3) ≥ s. Contradiction.
          have := b'b'_range a₂ b₂ ha2B' hb2B'
          omega
    · -- Pair 1 is Cross (a₁ ∈ B, b₁ ∈ B')
      obtain ⟨d₁, hd1, rfl⟩ := hB'_mem b₁ hb1B'
      -- s = a₁ + (N - d₁), so s ≥ N - N/3 + 1 and s ≤ N/3 + (N-1)
      rcases Finset.mem_union.mp ha2 with ha2B | ha2B'
      · rcases Finset.mem_union.mp hb2 with hb2B | hb2B'
        · -- Pair 2 is BB: s ≤ 2*(N/3) but s ≥ N - N/3 + 1 > 2*(N/3). Contradiction.
          have := bb_range a₂ b₂ ha2B hb2B
          have := cross_lo a₁ (N - d₁) ha1B (Finset.mem_image.mpr ⟨d₁, hd1, rfl⟩)
          omega
        · -- Pair 2 also Cross (a₂ ∈ B, b₂ ∈ B')
          obtain ⟨d₂, hd2, rfl⟩ := hB'_mem b₂ hb2B'
          -- a₁ + (N - d₁) = a₂ + (N - d₂) = s
          -- So a₁ + d₂ = a₂ + d₁ (rearranging with ℕ subtraction)
          have hd1_le : d₁ ≤ N := hB_le_N d₁ hd1
          have hd2_le : d₂ ≤ N := hB_le_N d₂ hd2
          have heq : a₁ + d₂ = a₂ + d₁ := by omega
          -- By IsSidon B: the pair (min(a₁,d₂), max(a₁,d₂)) = (min(a₂,d₁), max(a₂,d₁))
          -- Use sumRepCount B (a₁ + d₂) ≤ 1
          -- Two pairs with same sum in B: (a₁, d₂) ordered and (a₂, d₁) ordered
          -- Both give sum a₁ + d₂ = a₂ + d₁
          -- Sidon on B says at most one pair, so the ordered versions must match
          by_cases h_ad : a₁ ≤ d₂
          · by_cases h_ad2 : a₂ ≤ d₁
            · -- Pairs (a₁, d₂) and (a₂, d₁) both in upper triangle of B
              have hle1 := isSidon_sumRepCount_le_one hSidon (a₁ + d₂)
              unfold sumRepCount at hle1
              have hp1 : (a₁, d₂) ∈ (B ×ˢ B).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = a₁ + d₂) := by
                simp [Finset.mem_filter, Finset.mem_product, ha1B, hd2, h_ad]
              have hp2 : (a₂, d₁) ∈ (B ×ˢ B).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = a₁ + d₂) := by
                simp [Finset.mem_filter, Finset.mem_product, ha2B, hd1, h_ad2, heq]
              have := Finset.card_le_one.mp hle1 hp1 hp2
              -- (a₁, d₂) = (a₂, d₁), so a₁ = a₂ and d₂ = d₁
              -- Then the original pairs are equal, contradicting hne
              simp only [Prod.mk.injEq] at this
              obtain ⟨rfl, rfl⟩ := this
              exact absurd rfl hne
            · -- a₂ > d₁: swap order to (d₁, a₂)
              push_neg at h_ad2
              have hle1 := isSidon_sumRepCount_le_one hSidon (a₁ + d₂)
              unfold sumRepCount at hle1
              have hp1 : (a₁, d₂) ∈ (B ×ˢ B).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = a₁ + d₂) := by
                simp [Finset.mem_filter, Finset.mem_product, ha1B, hd2, h_ad]
              have hp2 : (d₁, a₂) ∈ (B ×ˢ B).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = a₁ + d₂) := by
                simp [Finset.mem_filter, Finset.mem_product, hd1, ha2B]; omega
              have := Finset.card_le_one.mp hle1 hp1 hp2
              simp only [Prod.mk.injEq] at this
              obtain ⟨rfl, rfl⟩ := this
              -- a₁ = d₁ and d₂ = a₂, so s = a₁ + (N - d₁) = a₁ + (N - a₁) = N
              omega
          · push_neg at h_ad
            -- a₁ > d₂: swap order to (d₂, a₁)
            by_cases h_ad2 : a₂ ≤ d₁
            · have hle1 := isSidon_sumRepCount_le_one hSidon (a₁ + d₂)
              unfold sumRepCount at hle1
              have hp1 : (d₂, a₁) ∈ (B ×ˢ B).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = a₁ + d₂) := by
                simp [Finset.mem_filter, Finset.mem_product, hd2, ha1B]; omega
              have hp2 : (a₂, d₁) ∈ (B ×ˢ B).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = a₁ + d₂) := by
                simp [Finset.mem_filter, Finset.mem_product, ha2B, hd1, h_ad2, heq]
              have := Finset.card_le_one.mp hle1 hp1 hp2
              simp only [Prod.mk.injEq] at this
              obtain ⟨rfl, rfl⟩ := this
              -- d₂ = a₂ and a₁ = d₁ → s = a₁ + (N - a₁) = N
              omega
            · push_neg at h_ad2
              have hle1 := isSidon_sumRepCount_le_one hSidon (a₁ + d₂)
              unfold sumRepCount at hle1
              have hp1 : (d₂, a₁) ∈ (B ×ˢ B).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = a₁ + d₂) := by
                simp [Finset.mem_filter, Finset.mem_product, hd2, ha1B]; omega
              have hp2 : (d₁, a₂) ∈ (B ×ˢ B).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = a₁ + d₂) := by
                simp [Finset.mem_filter, Finset.mem_product, hd1, ha2B]; omega
              have := Finset.card_le_one.mp hle1 hp1 hp2
              simp only [Prod.mk.injEq] at this
              obtain ⟨rfl, rfl⟩ := this
              exact absurd rfl hne
      · -- a₂ ∈ B'
        rcases Finset.mem_union.mp hb2 with hb2B | hb2B'
        · exact absurd hab2 (no_B'_B a₂ b₂ ha2B' hb2B)
        · -- Pair 2 is B'B': s ≥ 2*(N - N/3) but s ≤ Cross max. Contradiction for N ≥ 3.
          have := b'b'_range a₂ b₂ ha2B' hb2B'
          have hcross := cross_lo a₁ (N - d₁) ha1B (Finset.mem_image.mpr ⟨d₁, hd1, rfl⟩)
          have hBne : B.Nonempty := ⟨a₁, ha1B⟩
          have hchi := cross_hi a₁ (N - d₁) ha1B (Finset.mem_image.mpr ⟨d₁, hd1, rfl⟩) hBne
          -- Need N ≥ 3 for the separation
          by_cases hN3 : N ≥ 3
          · have := sep2 hN3; omega
          · -- N < 3: N/3 = 0, so B ⊆ Icc 1 0 = ∅, contradiction
            exfalso; have h03 : N / 3 = 0 := by omega
            have := (Finset.mem_Icc.mp (hB a₁ ha1B)).1
            have := (Finset.mem_Icc.mp (hB a₁ ha1B)).2; omega
  · -- a₁ ∈ B'
    rcases Finset.mem_union.mp hb1 with hb1B | hb1B'
    · exact absurd hab1 (no_B'_B a₁ b₁ ha1B' hb1B)
    · -- Pair 1 is B'B': s ≥ 2*(N - N/3)
      have hs_b'b' := b'b'_range a₁ b₁ ha1B' hb1B'
      rcases Finset.mem_union.mp ha2 with ha2B | ha2B'
      · rcases Finset.mem_union.mp hb2 with hb2B | hb2B'
        · -- Pair 2 is BB: range contradiction
          have := bb_range a₂ b₂ ha2B hb2B; omega
        · -- Pair 2 is Cross: range contradiction
          obtain ⟨d₂, hd2, rfl⟩ := hB'_mem b₂ hb2B'
          have hBne : B.Nonempty := ⟨a₂, ha2B⟩
          have hchi := cross_hi a₂ (N - d₂) ha2B (Finset.mem_image.mpr ⟨d₂, hd2, rfl⟩) hBne
          by_cases hN3 : N ≥ 3
          · have := sep2 hN3; omega
          · exfalso; have h03 : N / 3 = 0 := by omega
            have := (Finset.mem_Icc.mp (hB a₂ ha2B)).1
            have := (Finset.mem_Icc.mp (hB a₂ ha2B)).2; omega
      · rcases Finset.mem_union.mp hb2 with hb2B | hb2B'
        · exact absurd hab2 (no_B'_B a₂ b₂ ha2B' hb2B)
        · -- Pair 2 also B'B': use reflected Sidon
          -- a₁ = N - c₁, b₁ = N - d₁, a₂ = N - c₂, b₂ = N - d₂
          obtain ⟨c₁, hc1, rfl⟩ := hB'_mem a₁ ha1B'
          obtain ⟨d₁, hd1, rfl⟩ := hB'_mem b₁ hb1B'
          obtain ⟨c₂, hc2, rfl⟩ := hB'_mem a₂ ha2B'
          obtain ⟨d₂, hd2, rfl⟩ := hB'_mem b₂ hb2B'
          -- (N-c₁) + (N-d₁) = (N-c₂) + (N-d₂) → c₁+d₁ = c₂+d₂
          have hc1N := hB_le_N c₁ hc1; have hd1N := hB_le_N d₁ hd1
          have hc2N := hB_le_N c₂ hc2; have hd2N := hB_le_N d₂ hd2
          have heq : c₁ + d₁ = c₂ + d₂ := by omega
          -- a₁ ≤ b₁ means N-c₁ ≤ N-d₁ means d₁ ≤ c₁
          have hdc1 : d₁ ≤ c₁ := by omega
          have hdc2 : d₂ ≤ c₂ := by omega
          -- Sidon: (d₁, c₁) and (d₂, c₂) are pairs in B with same sum
          have hle1 := isSidon_sumRepCount_le_one hSidon (c₁ + d₁)
          unfold sumRepCount at hle1
          have hp1 : (d₁, c₁) ∈ (B ×ˢ B).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = c₁ + d₁) := by
            simp [Finset.mem_filter, Finset.mem_product, hc1, hd1, hdc1]; omega
          have hp2 : (d₂, c₂) ∈ (B ×ˢ B).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = c₁ + d₁) := by
            simp [Finset.mem_filter, Finset.mem_product, hc2, hd2, hdc2, heq]; omega
          have := Finset.card_le_one.mp hle1 hp1 hp2
          simp only [Prod.mk.injEq] at this
          obtain ⟨rfl, rfl⟩ := this
          exact absurd rfl hne

/- ## Reflected Construction: Quantitative Lower Bound

The reflected construction A = B ∪ {N − b : b ∈ B} gives |A| = 2|B| when
B ⊆ {1,...,N/3}, since B lives in [1, N/3] and the reflected set lives in
[N − N/3, N − 1], which are disjoint ranges. Combined with
`reflected_construction_valid`, this yields maxAlmostSidon(N) ≥ 2|B|. -/

/-- The reflection map b ↦ N − b is injective on B when all elements ≤ N. -/
private lemma reflected_injOn (N : ℕ) (B : Finset ℕ)
    (hB_le : ∀ b ∈ B, b ≤ N) :
    Set.InjOn (fun b => N - b) ↑B := by
  intro a ha b hb heq
  rw [Finset.mem_coe] at ha hb
  have := hB_le a ha; have := hB_le b hb
  omega

/-- B and B.image(N−·) are disjoint when B ⊆ {1,...,N/3}. -/
private lemma reflected_disjoint (N : ℕ) (B : Finset ℕ)
    (hB : ∀ b ∈ B, b ∈ Finset.Icc 1 (N / 3)) :
    Disjoint B (B.image (fun b => N - b)) := by
  rw [Finset.disjoint_left]
  intro x hxB hxImg
  rw [Finset.mem_image] at hxImg
  obtain ⟨y, hyB, hxy⟩ := hxImg
  have := Finset.mem_Icc.mp (hB x hxB)
  have := Finset.mem_Icc.mp (hB y hyB)
  omega

/-- |B ∪ B.image(N−·)| = 2|B| when B ⊆ {1,...,N/3}. -/
private lemma reflected_card (N : ℕ) (B : Finset ℕ)
    (hB : ∀ b ∈ B, b ∈ Finset.Icc 1 (N / 3)) :
    (B ∪ B.image (fun b => N - b)).card = 2 * B.card := by
  rw [Finset.card_union_of_disjoint (reflected_disjoint N B hB),
      Finset.card_image_of_injOn (reflected_injOn N B
        (fun b hb => le_trans (Finset.mem_Icc.mp (hB b hb)).2 (Nat.div_le_self N 3)))]
  ring

/-- B ∪ B.image(N−·) ⊆ {1,...,N} when B ⊆ {1,...,N/3}. -/
private lemma reflected_subset_Icc (N : ℕ) (B : Finset ℕ)
    (hB : ∀ b ∈ B, b ∈ Finset.Icc 1 (N / 3)) :
    B ∪ B.image (fun b => N - b) ⊆ Finset.Icc 1 N := by
  intro x hx
  rw [Finset.mem_union] at hx
  rcases hx with hxB | hxImg
  · have := Finset.mem_Icc.mp (hB x hxB)
    rw [Finset.mem_Icc]; constructor <;> omega
  · rw [Finset.mem_image] at hxImg
    obtain ⟨b, hbB, rfl⟩ := hxImg
    have := Finset.mem_Icc.mp (hB b hbB)
    rw [Finset.mem_Icc]; constructor <;> omega

/-- **Reflected construction bound**: If B ⊆ {1,...,N/3} is Sidon,
    then maxAlmostSidon(N) ≥ 2·|B|. This quantifies `reflected_construction_valid`:
    the reflected set has exactly 2|B| elements (disjointness), lies in {1,...,N},
    and witnesses the lower bound. To eliminate `erdos_freud_lower_bound`, it
    suffices to construct Sidon sets of size ∼√(N/3) in {1,...,N/3}. -/
theorem reflected_construction_bound (N : ℕ) (B : Finset ℕ)
    (hB : ∀ b ∈ B, b ∈ Finset.Icc 1 (N / 3)) (hS : IsSidon B) :
    maxAlmostSidon N ≥ 2 * B.card := by
  have hA_mem : B ∪ B.image (fun b => N - b) ∈
      (Finset.Icc 1 N).powerset.filter IsAlmostSidon :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (reflected_subset_Icc N B hB),
                            reflected_construction_valid N B hB hS⟩
  have h1 : (B ∪ B.image (fun b => N - b)).card ≤ maxAlmostSidon N :=
    Finset.le_sup hA_mem
  have h2 := reflected_card N B hB
  omega

/- ## Bridge from Erdős-Turán Sidon Construction

The Erdős-Turán modular parabola construction (Erdos44SidonLowerBound.lean) produces
Sidon sets of size ⌊√N⌋/2 in {1,...,N}. To use this with our reflected construction,
we bridge the Erdos340.IsSidon definition (pairwise sum uniqueness) to our local
IsSidon definition (multiRepSet = ∅). -/

/-- Bridge: Erdos340.IsSidon (all pairwise sums distinct) implies
    our local IsSidon (multiRepSet is empty). -/
theorem erdos340_isSidon_implies_local {A : Finset ℕ} (h : Erdos340.IsSidon A) :
    IsSidon A := by
  unfold IsSidon
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem]
  intro n hn
  simp only [multiRepSet, Finset.mem_filter] at hn
  obtain ⟨_, hrep⟩ := hn
  unfold sumRepCount at hrep
  -- Extract two distinct pairs with the same sum
  have hlt : 1 < ((A ×ˢ A).filter fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = n).card := by omega
  rw [Finset.one_lt_card] at hlt
  obtain ⟨⟨a₁, b₁⟩, h1, ⟨a₂, b₂⟩, h2, hne⟩ := hlt
  simp only [Finset.mem_filter, Finset.mem_product] at h1 h2
  -- By Erdos340.IsSidon: same sum + ordered → same pair
  have := h a₁ b₁ a₂ b₂ h1.1.1 h1.1.2 h2.1.1 h2.1.2 h1.2.1 h2.2.1 (by linarith [h1.2.2, h2.2.2])
  exact hne (Prod.ext this.1 this.2)

/-- **Concrete lower bound**: For N ≥ 3, there exists an almost-Sidon set in {1,...,N}
    of size ≥ 2·⌊√(N/3)⌋/2, obtained by applying the reflected construction to a
    modular parabola Sidon set in {1,...,N/3}.

    This is weaker than `erdos_freud_lower_bound` (which gives ∼(2/√3)·√N) by a
    factor of √2, because the Erdős-Turán construction has range 2p² (not p²).
    The optimal constant requires the Singer/Bose-Chowla construction. -/
theorem maxAlmostSidon_concrete_lower_bound (N : ℕ) (hN : 3 ≤ N) :
    maxAlmostSidon N ≥ 2 * (Nat.sqrt (N / 3) / 2) := by
  set M := N / 3 with hM_def
  -- M ≥ 1 since N ≥ 3
  have hM : 1 ≤ M := by omega
  -- By Erdős-Turán construction: ∃ Sidon B ⊆ {1,...,M} with |B| ≥ √M/2
  obtain ⟨B, hB_sub, hB_sidon, hB_card⟩ := Erdos44.sidon_set_lower_bound_exists M hM
  -- Bridge: Erdos340.IsSidon → local IsSidon
  have hB_local : IsSidon B := erdos340_isSidon_implies_local hB_sidon
  -- B ⊆ Icc 1 M = Icc 1 (N/3)
  have hB_Icc : ∀ b ∈ B, b ∈ Finset.Icc 1 (N / 3) := fun b hb => hB_sub hb
  -- Apply reflected construction
  have := reflected_construction_bound N B hB_Icc hB_local
  omega
