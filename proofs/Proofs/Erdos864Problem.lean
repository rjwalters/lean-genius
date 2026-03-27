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

/-- Sidon set upper bound: |A| ≤ √N + O(N^{1/4}) for Sidon sets. -/
axiom sidon_upper_bound :
  ∃ C : ℝ, C > 0 ∧
    ∀ (N : ℕ) (A : Finset ℕ), (∀ a ∈ A, a ∈ Finset.Icc 1 N) →
      IsSidon A → (A.card : ℝ) ≤ Real.sqrt (N : ℝ) + C * (N : ℝ) ^ (1/4 : ℝ)

/-- Almost-Sidon sets can be larger than Sidon sets by a factor of 2/√3 ≈ 1.155.
    One extra collision allows ~15.5% more elements. -/
axiom almost_sidon_exceeds_sidon :
  ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    (maxAlmostSidon N : ℝ) > Real.sqrt (N : ℝ) + 1

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

/-- For almost-Sidon A, at most one sum has a collision, so the number of
    distinct sums is ≥ C(|A|,2) + |A| − 1. These must fit in [2, 2N]. -/
axiom almost_sidon_sum_range (A : Finset ℕ) (N : ℕ) :
  (∀ a ∈ A, a ∈ Finset.Icc 1 N) → IsAlmostSidon A →
    A.card * (A.card + 1) / 2 - 1 ≤ 2 * N - 1

/-- The reflected construction: B ∪ (N − B) is almost-Sidon when B is Sidon.
    The only possible collision is at n = N (sums from B-side and reflected-side). -/
axiom reflected_construction_valid (N : ℕ) (B : Finset ℕ) :
  (∀ b ∈ B, b ∈ Finset.Icc 1 (N / 3)) → IsSidon B →
    IsAlmostSidon (B ∪ B.image (fun b => N - b))
