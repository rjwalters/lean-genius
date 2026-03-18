/-
# Combinatorial Proof of Vandermonde's Identity via Explicit Bijection

Open Question (from binomial-theorem-oq-04):
  Can Vandermonde's identity be proved combinatorially, via an explicit
  bijection on Finsets, rather than through the algebraic Nat.add_choose_eq?

Answer: YES.

We construct an explicit bijection between:
- r-element subsets of {0,...,m+n-1}
- disjoint union over k of (k-subsets of {0,...,m-1}) × ((r-k)-subsets of {0,...,n-1})

The bijection splits each subset S by a threshold m:
  forward:  S  ↦  (S ∩ {0,...,m-1},  shift(S ∩ {m,...,m+n-1}))
  inverse:  (A, B)  ↦  A ∪ shift⁻¹(B)

where shift subtracts m from each element.

This gives a purely combinatorial proof: no polynomial algebra or generating functions.
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open Finset Nat

namespace BinomialTheoremOQ04OQ01

-- ============================================================================
-- Part I: The Split Map
-- ============================================================================

/-- The "low part" of S: elements below the threshold m. -/
def lowPart (m : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.filter (· < m)

/-- The "high part" of S: elements ≥ m, shifted down by m. -/
def highPart (m : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (S.filter (m ≤ ·)).image (· - m)

-- ============================================================================
-- Part II: The Merge Map
-- ============================================================================

/-- Merge: given A ⊆ range(m) and B ⊆ range(n), form A ∪ shift(B) ⊆ range(m+n). -/
def merge (m : ℕ) (A B : Finset ℕ) : Finset ℕ :=
  A ∪ B.image (· + m)

-- ============================================================================
-- Part III: Properties of Low/High Parts
-- ============================================================================

theorem lowPart_subset_range {m n : ℕ} {S : Finset ℕ} (_ : S ⊆ range (m + n)) :
    lowPart m S ⊆ range m := by
  intro x hx
  simp only [lowPart, mem_filter] at hx
  exact mem_range.mpr hx.2

theorem highPart_subset_range {m n : ℕ} {S : Finset ℕ} (hS : S ⊆ range (m + n)) :
    highPart m S ⊆ range n := by
  intro x hx
  simp only [highPart, mem_image, mem_filter] at hx
  obtain ⟨y, ⟨hyS, hym⟩, rfl⟩ := hx
  have hy_bound : y < m + n := mem_range.mp (hS hyS)
  rw [mem_range]; omega

theorem lowPart_card_add_highPart_card {m : ℕ} {S : Finset ℕ} :
    (lowPart m S).card + (highPart m S).card = S.card := by
  -- S = (S.filter (· < m)) ∪ (S.filter (m ≤ ·))
  have hpart : S = S.filter (· < m) ∪ S.filter (m ≤ ·) := by
    ext x; simp only [mem_union, mem_filter]
    exact ⟨fun h => if hlt : x < m then Or.inl ⟨h, hlt⟩ else Or.inr ⟨h, by omega⟩,
           fun h => h.elim (·.1) (·.1)⟩
  have hdisj : Disjoint (S.filter (· < m)) (S.filter (m ≤ ·)) := by
    rw [Finset.disjoint_filter]
    exact fun _ _ h1 h2 => by omega
  have hcard : S.card = (S.filter (· < m)).card + (S.filter (m ≤ ·)).card := by
    conv_lhs => rw [hpart]
    exact card_union_of_disjoint hdisj
  -- highPart has same card as the high filter (· - m is injective when m ≤ ·)
  have hinj : Set.InjOn (fun x : ℕ => x - m) ↑(S.filter fun x => m ≤ x) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, mem_filter] at ha hb
    have hab' : a - m = b - m := hab
    omega
  change (S.filter (· < m)).card +
    (Finset.image (fun x => x - m) (S.filter fun x => m ≤ x)).card = S.card
  rw [Finset.card_image_of_injOn hinj]
  linarith

-- ============================================================================
-- Part IV: Round-Trip Properties
-- ============================================================================

/-- Merge then split recovers the original pair (low part). -/
theorem lowPart_merge {m n : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ range m) (hB : B ⊆ range n) :
    lowPart m (merge m A B) = A := by
  ext x
  simp only [lowPart, merge, mem_filter, mem_union, mem_image]
  constructor
  · rintro ⟨hx | ⟨y, hy, rfl⟩, hxm⟩
    · exact hx
    · exfalso; have := mem_range.mp (hB hy); omega
  · intro hx
    exact ⟨Or.inl hx, mem_range.mp (hA hx)⟩

/-- Merge then split recovers the original pair (high part). -/
theorem highPart_merge {m n : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ range m) (hB : B ⊆ range n) :
    highPart m (merge m A B) = B := by
  ext x
  simp only [highPart, merge, mem_image, mem_filter, mem_union]
  constructor
  · rintro ⟨y, ⟨hy_mem | ⟨z, hz, rfl⟩, hym⟩, rfl⟩
    · exfalso; have := mem_range.mp (hA hy_mem); omega
    · have : z + m - m = z := by omega
      rw [this]; exact hz
  · intro hx
    exact ⟨x + m, ⟨Or.inr ⟨x, hx, rfl⟩, Nat.le_add_left m x⟩, by omega⟩

/-- Split then merge recovers the original set. -/
theorem merge_lowPart_highPart {m n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ range (m + n)) :
    merge m (lowPart m S) (highPart m S) = S := by
  ext x
  simp only [merge, lowPart, highPart, mem_union, mem_filter, mem_image]
  constructor
  · rintro (⟨hxS, _⟩ | ⟨y, ⟨z, ⟨hzS, hzm⟩, rfl⟩, rfl⟩)
    · exact hxS
    · convert hzS using 1; omega
  · intro hxS
    by_cases hxm : x < m
    · exact Or.inl ⟨hxS, hxm⟩
    · right
      exact ⟨x - m, ⟨x, ⟨hxS, by omega⟩, rfl⟩, by omega⟩

-- ============================================================================
-- Part V: Merge Preserves Cardinality
-- ============================================================================

theorem merge_card {m n : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ range m) (_ : B ⊆ range n) :
    (merge m A B).card = A.card + B.card := by
  rw [merge, card_union_of_disjoint]
  · rw [card_image_of_injective _ (fun _ _ h => by omega)]
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [mem_image] at hx'
    obtain ⟨_, _, rfl⟩ := hx'
    have := mem_range.mp (hA hx)
    omega

theorem merge_subset_range {m n : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ range m) (hB : B ⊆ range n) :
    merge m A B ⊆ range (m + n) := by
  intro x hx
  simp only [merge, mem_union, mem_image, mem_range] at hx ⊢
  rcases hx with hx | ⟨y, hy, rfl⟩
  · have := mem_range.mp (hA hx); omega
  · have := mem_range.mp (hB hy); omega

-- ============================================================================
-- Part VI: The Fiber Bijection
-- ============================================================================

/-- The fiber: r-subsets of range(m+n) whose low part has cardinality k. -/
def fiber (m n r k : ℕ) : Finset (Finset ℕ) :=
  ((range (m + n)).powersetCard r).filter (fun S => (lowPart m S).card = k)

theorem fiber_disjoint {m n r : ℕ} {k₁ k₂ : ℕ} (hne : k₁ ≠ k₂) :
    Disjoint (fiber m n r k₁) (fiber m n r k₂) := by
  simp only [fiber, Finset.disjoint_filter]
  intro S _ h1 h2; exact hne (h1 ▸ h2)

theorem mem_fiber_iff {m n r k : ℕ} {S : Finset ℕ} :
    S ∈ fiber m n r k ↔ S ∈ (range (m + n)).powersetCard r ∧ (lowPart m S).card = k := by
  simp [fiber]

theorem powersetCard_eq_biUnion_fiber (m n r : ℕ) :
    (range (m + n)).powersetCard r = (range (r + 1)).biUnion (fiber m n r) := by
  ext S
  simp only [mem_biUnion, mem_range, mem_fiber_iff]
  constructor
  · intro hS
    have hcard : (lowPart m S).card < r + 1 := by
      rw [mem_powersetCard] at hS
      calc (lowPart m S).card ≤ S.card := Finset.card_filter_le S _
        _ = r := hS.2
        _ < r + 1 := by omega
    exact ⟨(lowPart m S).card, hcard, hS, rfl⟩
  · rintro ⟨_, _, hS, _⟩
    exact hS

/-- Each fiber has cardinality C(m,k) · C(n,r-k). -/
theorem card_fiber (m n r k : ℕ) (hk : k ≤ r) :
    (fiber m n r k).card = Nat.choose m k * Nat.choose n (r - k) := by
  rw [fiber]
  have : (((range (m + n)).powersetCard r).filter
      (fun S => (lowPart m S).card = k)).card =
    ((range m).powersetCard k ×ˢ (range n).powersetCard (r - k)).card := by
    apply Finset.card_bij (fun S _ => (lowPart m S, highPart m S))
    · -- Maps into target
      intro S hS
      simp only [mem_filter, mem_powersetCard] at hS
      obtain ⟨⟨hSsub, hScard⟩, hlow⟩ := hS
      simp only [mem_product, mem_powersetCard]
      refine ⟨⟨lowPart_subset_range hSsub, hlow⟩,
             ⟨highPart_subset_range hSsub, ?_⟩⟩
      have := lowPart_card_add_highPart_card (m := m) (S := S)
      omega
    · -- Injective
      intro S₁ hS₁ S₂ hS₂ heq
      simp only [Prod.mk.injEq] at heq
      have h1 : S₁ ⊆ range (m + n) := by
        simp only [mem_filter, mem_powersetCard] at hS₁; exact hS₁.1.1
      have h2 : S₂ ⊆ range (m + n) := by
        simp only [mem_filter, mem_powersetCard] at hS₂; exact hS₂.1.1
      calc S₁ = merge m (lowPart m S₁) (highPart m S₁) := (merge_lowPart_highPart h1).symm
        _ = merge m (lowPart m S₂) (highPart m S₂) := by rw [heq.1, heq.2]
        _ = S₂ := merge_lowPart_highPart h2
    · -- Surjective
      intro ⟨A, B⟩ hAB
      simp only [mem_product, mem_powersetCard] at hAB
      obtain ⟨⟨hAsub, hAcard⟩, ⟨hBsub, hBcard⟩⟩ := hAB
      refine ⟨merge m A B, ?_, ?_⟩
      · simp only [mem_filter, mem_powersetCard]
        refine ⟨⟨merge_subset_range hAsub hBsub, ?_⟩,
               by rw [lowPart_merge hAsub hBsub, hAcard]⟩
        rw [merge_card hAsub hBsub, hAcard, hBcard]; omega
      · simp only [Prod.mk.injEq]
        exact ⟨lowPart_merge hAsub hBsub, highPart_merge hAsub hBsub⟩
  rw [this, card_product, card_powersetCard, card_powersetCard, card_range, card_range]

-- ============================================================================
-- Part VII: The Main Theorem — Vandermonde via Combinatorial Bijection
-- ============================================================================

/-- **Vandermonde's Identity — Combinatorial Proof**

    C(m+n, r) = Σ_{k=0}^{r} C(m, k) · C(n, r-k)

    Proved by explicit bijection: partition r-subsets of {0,...,m+n-1}
    by the cardinality of their intersection with {0,...,m-1}. -/
theorem vandermonde_combinatorial (m n r : ℕ) :
    Nat.choose (m + n) r =
    ∑ k ∈ Finset.range (r + 1), Nat.choose m k * Nat.choose n (r - k) := by
  -- LHS = |powersetCard r (range (m+n))|
  have hlhs : Nat.choose (m + n) r =
      ((range (m + n)).powersetCard r).card := by
    rw [card_powersetCard, card_range]
  rw [hlhs, powersetCard_eq_biUnion_fiber m n r]
  -- Fibers are pairwise disjoint
  have hdisj : (↑(range (r + 1)) : Set ℕ).PairwiseDisjoint (fiber m n r) :=
    fun _ _ _ _ hne => fiber_disjoint hne
  rw [card_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro k hk
  exact card_fiber m n r k (Nat.lt_succ_iff.mp (mem_range.mp hk))

-- ============================================================================
-- Part VIII: Concrete Verifications
-- ============================================================================

/-- C(5+3, 4) = Σ C(5,k)·C(3,4-k) via the combinatorial proof. -/
example : Nat.choose 8 4 = 70 := by native_decide

/-- The split of {0,1,4,6} ⊆ {0,...,7} with threshold m=5:
    low = {0,1,4}, high = shift({6}) = {1}. -/
example : lowPart 5 {0, 1, 4, 6} = {0, 1, 4} := by native_decide
example : highPart 5 {0, 1, 4, 6} = {1} := by native_decide

/-- Merge recovers the original: {0,1,4} ∪ shift({1}) = {0,1,4,6}. -/
example : merge 5 {0, 1, 4} {1} = {0, 1, 4, 6} := by native_decide

/-- C(2·4, 4) = Σ C(4,k)² via bijective counting. -/
example : Nat.choose 8 4 = ∑ k ∈ Finset.range 5, (Nat.choose 4 k) ^ 2 := by native_decide

-- ============================================================================
-- Part IX: Sum-of-Squares Corollary (Combinatorial)
-- ============================================================================

/-- **Sum-of-Squares via Bijection**: C(2n, n) = Σ C(n,k)².
    Each n-subset of {0,...,2n-1} splits into a k-subset of the first half
    and an (n-k)-subset of the second half. Symmetry C(n,n-k) = C(n,k) yields squares. -/
theorem sum_squares_combinatorial (n : ℕ) :
    Nat.choose (2 * n) n = ∑ k ∈ Finset.range (n + 1), (Nat.choose n k) ^ 2 := by
  have h := vandermonde_combinatorial n n n
  rw [show n + n = 2 * n from (two_mul n).symm] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k hk
  have hkle : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [sq, Nat.choose_symm hkle]

end BinomialTheoremOQ04OQ01
