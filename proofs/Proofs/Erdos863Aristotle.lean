/-
  Aristotle targets for Erdős Problem #863
  Routine supporting lemmas for automated proof search.
  See Erdos863Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely provable via Mathlib combinatorics
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Erdos863Aristotle

/-- The number of representations of n as a + b with a ≤ b, a, b ∈ A -/
noncomputable def sumRepCount (A : Finset ℕ) (n : ℕ) : ℕ :=
  (A.product A).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = n) |>.card

/-- A is a B₂[r] set if every integer has at most r sum representations -/
def IsB2r (A : Finset ℕ) (r : ℕ) : Prop :=
  ∀ n : ℕ, sumRepCount A n ≤ r

/-- A ⊆ {1,...,N} -/
def InRange (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ a ∈ A, 1 ≤ a ∧ a ≤ N

/-- The number of representations of n as a - b with a, b ∈ A -/
noncomputable def diffRepCount (A : Finset ℕ) (n : ℤ) : ℕ :=
  (A.product A).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) = n) |>.card

/-- A is a difference B₂[r] set if every nonzero integer has at most r
    difference representations -/
def IsDiffB2r (A : Finset ℕ) (r : ℕ) : Prop :=
  ∀ n : ℤ, n ≠ 0 → diffRepCount A n ≤ r

/-- A singleton is B₂[r] for any r ≥ 1: the only sum representation
    of 2a from {a} is (a, a), giving sumRepCount {a} (2a) = 1 -/
theorem isB2r_singleton (a : ℕ) (r : ℕ) (hr : 1 ≤ r) : IsB2r {a} r := by
  intro n
  unfold sumRepCount
  calc ({a} ×ˢ {a}).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = n) |>.card
      ≤ ({a} ×ˢ {a}).card := Finset.card_filter_le _ _
    _ = 1 := by simp [Finset.product_singleton_singleton]
    _ ≤ r := hr

/-- A singleton is a difference B₂[r] set for any r ≥ 1 -/
theorem isDiffB2r_singleton (a : ℕ) (r : ℕ) (hr : 1 ≤ r) : IsDiffB2r {a} r := by
  intro n _
  unfold diffRepCount
  calc ({a} ×ˢ {a}).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) = n) |>.card
      ≤ ({a} ×ˢ {a}).card := Finset.card_filter_le _ _
    _ = 1 := by simp [Finset.product_singleton_singleton]
    _ ≤ r := hr

/-- Subset preserves B₂[r]: if A is B₂[r] and B ⊆ A, then B is B₂[r] -/
theorem isB2r_subset {A B : Finset ℕ} {r : ℕ} (h : IsB2r A r) (hsub : B ⊆ A) :
    IsB2r B r := by
  intro n
  unfold sumRepCount
  calc (B ×ˢ B).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = n) |>.card
      ≤ (A ×ˢ A).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = n) |>.card :=
        Finset.card_le_card (Finset.filter_subset_filter _
          (Finset.product_subset_product hsub hsub))
    _ ≤ r := h n

/-- Subset preserves difference B₂[r] -/
theorem isDiffB2r_subset {A B : Finset ℕ} {r : ℕ} (h : IsDiffB2r A r) (hsub : B ⊆ A) :
    IsDiffB2r B r := by
  intro n hn
  unfold diffRepCount
  calc (B ×ˢ B).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) = n) |>.card
      ≤ (A ×ˢ A).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) = n) |>.card :=
        Finset.card_le_card (Finset.filter_subset_filter _
          (Finset.product_subset_product hsub hsub))
    _ ≤ r := h n hn

/-- Counting argument: for a B₂[1] set A in {1,...,N}, the number of
    ordered pairs (a,b) with a ≤ b gives |A|(|A|+1)/2 distinct sums
    in {2,...,2N}, so |A|² ≤ 4N.
    The key steps: (1) the sum map is injective on ordered pairs by B₂[1],
    (2) all sums lie in {2,...,2N}, (3) so |A|(|A|+1)/2 ≤ 2N-1 < 2N,
    giving |A|² < |A|² + |A| ≤ 4N. -/
theorem sidon_counting_bound (A : Finset ℕ) (N : ℕ) (hN : 1 ≤ N)
    (hB : IsB2r A 1) (hR : InRange A N) :
    A.card * A.card ≤ 4 * N := by
  -- Strategy: S.card ≤ 2N-1 (injective sums in {2,...,2N}),
  -- L.card ≤ S.card (swap injection), S+L = |A|², so |A|² ≤ 4N-2 ≤ 4N.
  -- Step 1: Upper triangle S = {(a,b) ∈ A×A : a ≤ b}
  set S := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 ≤ p.2)
  -- Step 2: Sum map injective on S by B₂[1]
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2) ↑S := by
    intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe,
               Finset.mem_product] at h₁ h₂
    -- Both pairs represent the same sum. B₂[1] means ≤ 1 representation.
    -- Since both (a₁,b₁) and (a₂,b₂) are representations, they must be equal.
    by_contra hne
    push_neg at hne
    have hne' : (a₁, b₁) ≠ (a₂, b₂) := fun h => hne (Prod.mk.inj h).1 (Prod.mk.inj h).2
    -- The sum n = a₁+b₁ = a₂+b₂ has ≥ 2 representations, contradicting B₂[1]
    have : sumRepCount A (a₁ + b₁) ≥ 2 := by
      unfold sumRepCount
      have hp₁ : (a₁, b₁) ∈ (A ×ˢ A).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = a₁ + b₁) := by
        simp [Finset.mem_filter, Finset.mem_product, h₁.1.1, h₁.1.2, h₁.2]
      have hp₂ : (a₂, b₂) ∈ (A ×ˢ A).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = a₁ + b₁) := by
        simp [Finset.mem_filter, Finset.mem_product, h₂.1.1, h₂.1.2, h₂.2, heq]
      exact Finset.one_lt_card.mpr ⟨_, hp₁, _, hp₂, hne'⟩
    have hB1 := hB (a₁ + b₁)
    omega
  -- Step 3: Image lies in {2,...,2N} (elements ≥ 1, so sums ≥ 2 and ≤ 2N)
  have himg2 : S.image (fun p : ℕ × ℕ => p.1 + p.2) ⊆ Finset.Icc 2 (2 * N) := by
    intro s hs
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hs
    obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, _⟩, rfl⟩ := hs
    simp only [Finset.mem_Icc]
    constructor
    · have := (hR a ha).1; have := (hR b hb).1; omega
    · have := (hR a ha).2; have := (hR b hb).2; omega
  -- Step 4: |S| ≤ 2N-1 (injective image in {2,...,2N} which has 2N-1 elements)
  have hScard2 : S.card ≤ 2 * N - 1 := by
    calc S.card
        = (S.image (fun p : ℕ × ℕ => p.1 + p.2)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Icc 2 (2 * N)).card := Finset.card_le_card himg2
      _ = 2 * N - 1 := by rw [Finset.card_Icc]; omega
  -- Step 5: Lower triangle L = {(a,b) ∈ A×A : a > b}
  set L := (A ×ˢ A).filter (fun p : ℕ × ℕ => ¬(p.1 ≤ p.2))
  -- S and L partition A×A
  have hpart : S.card + L.card = A.card * A.card := by
    have := Finset.filter_card_add_filter_neg_card_eq_card (A ×ˢ A)
      (fun p : ℕ × ℕ => p.1 ≤ p.2)
    rwa [Finset.card_product] at this
  -- Swap maps L injectively into S: (a,b) ↦ (b,a) with b < a ⟹ b ≤ a
  have hL_le_S : L.card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => (p.2, p.1))
    · intro ⟨a, b⟩ hp
      simp only [Finset.mem_filter, Finset.mem_product, Nat.not_le] at hp
      simp only [S, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hp.1.2, hp.1.1⟩, Nat.le_of_lt hp.2⟩
    · intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
      exact Prod.ext (Prod.mk.inj h).2 (Prod.mk.inj h).1
  -- A.card² = S.card + L.card ≤ 2 * S.card ≤ 2*(2N-1) = 4N-2 ≤ 4N
  omega

end Erdos863Aristotle
