/- Erdős Problem #43: Sidon Sets with Disjoint Difference Sets

If A, B ⊆ {1,...,N} are Sidon sets with (A-A) ∩ (B-B) = {0},
must C(|A|,2) + C(|B|,2) ≤ C(f(N),2) + O(1), where f(N) is
the maximum Sidon set size in {1,...,N}?

Status: OPEN ($100 bounty)
- Tao proved: |A| ≤ (1/√2 + o(1))√N when |A| = |B| (without improvement constant)
- Barreto: the equal-size strengthening with -c is FALSE for infinitely many N

Reference: https://erdosproblems.com/43
-/

import Mathlib

/- ## Sidon Sets -/

/-- A Sidon set (B₂ set): all pairwise sums a + b (a ≤ b, a,b ∈ A) are distinct,
equivalently all nonzero pairwise differences are distinct. -/
def IsSidonSet (A : Finset ℤ) : Prop :=
  ∀ a₁ b₁ a₂ b₂ : ℤ, a₁ ∈ A → b₁ ∈ A → a₂ ∈ A → b₂ ∈ A →
    a₁ + b₁ = a₂ + b₂ → ({a₁, b₁} : Finset ℤ) = {a₂, b₂}

/-- The difference set A - A = { a - b | a, b ∈ A }. -/
def diffSet (A : Finset ℤ) : Finset ℤ :=
  (A ×ˢ A).image (fun p => p.1 - p.2)

/- ## Disjoint Differences -/

/-- Two sets have disjoint nonzero differences: (A-A) ∩ (B-B) = {0}. -/
def DisjointDifferences (A B : Finset ℤ) : Prop :=
  ∀ d : ℤ, d ∈ diffSet A → d ∈ diffSet B → d = 0

/- ## Maximum Sidon Set Size -/

/-- f(N): the maximum cardinality of a Sidon set in {1,...,N}. -/
axiom maxSidonSize : ℕ → ℕ

/-- f(N) ~ √N: the maximum Sidon set size is asymptotically √N.
    This is a classical result in additive combinatorics. -/
axiom sidon_size_asymptotic :
  ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    |(maxSidonSize N : ℝ) - Real.sqrt N| ≤ ε * Real.sqrt N

/- ## The Conjecture -/

/-- **Erdős Problem #43**: If A, B are Sidon sets in {1,...,N} with
disjoint nonzero differences, then C(|A|,2) + C(|B|,2) ≤ C(f(N),2) + O(1). -/
def ErdosProblem43 : Prop :=
  ∃ C : ℕ, ∀ N : ℕ, ∀ A B : Finset ℤ,
    IsSidonSet A → IsSidonSet B →
    (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) → (∀ b ∈ B, 1 ≤ b ∧ b ≤ N) →
    DisjointDifferences A B →
    A.card.choose 2 + B.card.choose 2 ≤ (maxSidonSize N).choose 2 + C

/- ## Equal Size Variant -/

/-- The equal-size strengthening: when |A| = |B|, can we get
C(|A|,2) + C(|B|,2) ≤ (1 - c)·C(f(N),2) for some c > 0?
Barreto showed this is FALSE for infinitely many N. -/
def EqualSizeVariant : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, ∀ A B : Finset ℤ,
    IsSidonSet A → IsSidonSet B →
    (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) → (∀ b ∈ B, 1 ≤ b ∧ b ≤ N) →
    DisjointDifferences A B → A.card = B.card →
    (A.card.choose 2 + B.card.choose 2 : ℝ) ≤ (1 - c) * (maxSidonSize N).choose 2

/-- Barreto's result: the equal-size variant is false. -/
axiom barreto_counterexample : ¬EqualSizeVariant

/- ## Arithmetic Helpers -/

/-- `2 * n.choose 2 = n*n - n` exactly (no rounding loss, since `n*(n-1)`
    is always even). Bridges `Nat.choose_two_right`'s `/2` form to the
    `n*n - n` form used by `Finset.offDiag_card`. -/
private lemma two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * n - n := by
  rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]
  rcases n with _ | k
  · rfl
  · have h : (k + 1) * (k + 1) = (k + 1) * k + (k + 1) := by ring
    rw [Nat.succ_sub_one, h, Nat.add_sub_cancel]

/- ## Counting Arguments -/

/-- For a Sidon set, nonzero differences are injective: if a₁ - b₁ = a₂ - b₂
    and a₁ ≠ b₁, then a₁ = a₂ and b₁ = b₂. -/
theorem sidon_diff_injective (A : Finset ℤ) (hS : IsSidonSet A)
    {a₁ b₁ a₂ b₂ : ℤ} (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₂ : b₂ ∈ A)
    (hne : a₁ ≠ b₁) (heq : a₁ - b₁ = a₂ - b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hsum : a₁ + b₂ = a₂ + b₁ := by omega
  have hpair := hS a₁ b₂ a₂ b₁ ha₁ hb₂ ha₂ hb₁ hsum
  -- a₁ ∈ {a₂, b₁}: a₁ = a₂ or a₁ = b₁
  have ha₁_mem : a₁ ∈ ({a₂, b₁} : Finset ℤ) := by
    rw [← hpair]; exact Finset.mem_insert_self a₁ {b₂}
  rw [Finset.mem_insert, Finset.mem_singleton] at ha₁_mem
  rcases ha₁_mem with h1 | h1
  · -- Case a₁ = a₂: then b₂ ∈ {a₂, b₁}
    have hb₂_mem : b₂ ∈ ({a₂, b₁} : Finset ℤ) := by
      rw [← hpair]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
    rw [Finset.mem_insert, Finset.mem_singleton] at hb₂_mem
    rcases hb₂_mem with h2 | h2
    · exfalso; omega  -- a₂ - b₁ = a₂ - a₂ = 0 → b₁ = a₂, contradicting hne
    · exact ⟨h1, h2.symm⟩
  · -- Case a₁ = b₁: contradicts hne
    exact absurd h1 hne

/- ## Structural Bounds -/

/-- A single Sidon set A in {1,...,N} has C(|A|,2) ≤ N.
    Proof sketch: the C(|A|,2) pairwise sums a+b (a<b) are all distinct
    (by Sidon property) and lie in {3,...,2N-1}, which has 2N-3 elements.
    More precisely, the differences a-b for a≠b are all distinct and
    lie in {-(N-1),...,-1,1,...,N-1}, giving |A|²-|A| ≤ 2(N-1). -/
theorem sidon_pair_bound (A : Finset ℤ) (N : ℕ)
    (hS : IsSidonSet A) (hR : ∀ a ∈ A, 1 ≤ a ∧ a ≤ N) :
  A.card.choose 2 ≤ N := by
  have he := two_mul_choose_two A.card
  -- n*(n-1) = |A.offDiag| (off-diagonal pairs)
  suffices h : A.card * A.card - A.card ≤ 2 * N by omega
  rw [← Finset.offDiag_card]
  -- The difference map (a,b) ↦ a-b is injective on A.offDiag (by Sidon)
  -- and maps into Finset.Icc (1-N) (N-1) which has ≤ 2N elements
  set f : ℤ × ℤ → ℤ := fun p => p.1 - p.2
  set T := Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)
  -- Injectivity on offDiag
  have hinj : Set.InjOn f ↑A.offDiag := by
    intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
    simp only [Finset.mem_coe, Finset.mem_offDiag] at h₁ h₂
    have := sidon_diff_injective A hS h₁.1 h₁.2.1 h₂.1 h₂.2.1 h₁.2.2 heq
    exact Prod.ext this.1 this.2
  -- Image maps into T
  have hfT : A.offDiag.image f ⊆ T := by
    intro d hd
    obtain ⟨⟨a, b⟩, hp, rfl⟩ := Finset.mem_image.mp hd
    simp only [Finset.mem_offDiag] at hp
    have ⟨ha1, haN⟩ := hR a hp.1
    have ⟨hb1, hbN⟩ := hR b hp.2.1
    simp only [T, f, Finset.mem_Icc]
    constructor <;> omega
  -- Card inequality: |offDiag| = |image| ≤ |T| ≤ 2N
  calc A.offDiag.card
      = (A.offDiag.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ T.card := Finset.card_le_card hfT
    _ ≤ 2 * N := by
        simp only [T, Int.card_Icc, Int.toNat_le]
        omega

/-- Disjoint differences force the nonzero differences of A and B
    to be completely disjoint, so the total number of distinct nonzero
    differences is |A|(|A|-1) + |B|(|B|-1), bounded by 2(N-1).
    This gives C(|A|,2) + C(|B|,2) ≤ N. -/
theorem disjoint_diff_combined_bound (A B : Finset ℤ) (N : ℕ)
    (hA : IsSidonSet A) (hB : IsSidonSet B)
    (hRA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ N) (hRB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ N)
    (hD : DisjointDifferences A B) :
  A.card.choose 2 + B.card.choose 2 ≤ N := by
  have heA := two_mul_choose_two A.card
  have heB := two_mul_choose_two B.card
  -- Reduce to: |A|*(|A|-1) + |B|*(|B|-1) ≤ 2*N
  suffices h : A.card * A.card - A.card + (B.card * B.card - B.card) ≤ 2 * N by omega
  rw [← Finset.offDiag_card, ← Finset.offDiag_card]
  set f : ℤ × ℤ → ℤ := fun p => p.1 - p.2
  set T := Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)
  -- Images of A.offDiag and B.offDiag under f are disjoint
  have hdisj : Disjoint (A.offDiag.image f) (B.offDiag.image f) := by
    rw [Finset.disjoint_left]
    intro d hda hdb
    -- d ∈ diffSet A and d ∈ diffSet B
    obtain ⟨⟨a₁, b₁⟩, hp₁, rfl⟩ := Finset.mem_image.mp hda
    obtain ⟨⟨a₂, b₂⟩, hp₂, heq⟩ := Finset.mem_image.mp hdb
    simp only [Finset.mem_offDiag] at hp₁ hp₂
    -- a₁ - b₁ ∈ diffSet A
    have hfA : f (a₁, b₁) ∈ diffSet A := by
      simp only [diffSet, Finset.mem_image]
      exact ⟨(a₁, b₁), Finset.mem_product.mpr ⟨hp₁.1, hp₁.2.1⟩, rfl⟩
    -- a₂ - b₂ ∈ diffSet B (and equals a₁ - b₁)
    have hfB : f (a₁, b₁) ∈ diffSet B := by
      rw [show f (a₁, b₁) = f (a₂, b₂) from heq.symm]
      simp only [diffSet, Finset.mem_image]
      exact ⟨(a₂, b₂), Finset.mem_product.mpr ⟨hp₂.1, hp₂.2.1⟩, rfl⟩
    -- By DisjointDifferences, a₁ - b₁ = 0, contradicting a₁ ≠ b₁
    have h0 := hD _ hfA hfB
    simp only [f] at h0
    exact absurd (sub_eq_zero.mp h0) hp₁.2.2
  -- Both injective on their offDiags
  have hinjA : Set.InjOn f ↑A.offDiag := by
    intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
    simp only [Finset.mem_coe, Finset.mem_offDiag] at h₁ h₂
    exact Prod.ext (sidon_diff_injective A hA h₁.1 h₁.2.1 h₂.1 h₂.2.1 h₁.2.2 heq).1
      (sidon_diff_injective A hA h₁.1 h₁.2.1 h₂.1 h₂.2.1 h₁.2.2 heq).2
  have hinjB : Set.InjOn f ↑B.offDiag := by
    intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
    simp only [Finset.mem_coe, Finset.mem_offDiag] at h₁ h₂
    exact Prod.ext (sidon_diff_injective B hB h₁.1 h₁.2.1 h₂.1 h₂.2.1 h₁.2.2 heq).1
      (sidon_diff_injective B hB h₁.1 h₁.2.1 h₂.1 h₂.2.1 h₁.2.2 heq).2
  -- Both images ⊆ T
  have hAT : A.offDiag.image f ⊆ T := by
    intro d hd; obtain ⟨⟨a, b⟩, hp, rfl⟩ := Finset.mem_image.mp hd
    simp only [Finset.mem_offDiag] at hp
    have ⟨ha1, haN⟩ := hRA a hp.1
    have ⟨hb1, hbN⟩ := hRA b hp.2.1
    simp only [T, f, Finset.mem_Icc]
    constructor <;> omega
  have hBT : B.offDiag.image f ⊆ T := by
    intro d hd; obtain ⟨⟨a, b⟩, hp, rfl⟩ := Finset.mem_image.mp hd
    simp only [Finset.mem_offDiag] at hp
    have ⟨ha1, haN⟩ := hRB a hp.1
    have ⟨hb1, hbN⟩ := hRB b hp.2.1
    simp only [T, f, Finset.mem_Icc]
    constructor <;> omega
  -- Combined: |offDiag A| + |offDiag B| = |image A ∪ image B| ≤ |T| ≤ 2N
  calc A.offDiag.card + B.offDiag.card
      = (A.offDiag.image f).card + (B.offDiag.image f).card := by
          rw [Finset.card_image_of_injOn hinjA, Finset.card_image_of_injOn hinjB]
    _ = (A.offDiag.image f ∪ B.offDiag.image f).card :=
          (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ T.card := Finset.card_le_card (Finset.union_subset hAT hBT)
    _ ≤ 2 * N := by simp only [T, Int.card_Icc, Int.toNat_le]; omega

/- ## Tao's Partial Result

Tao showed: if |A| = |B| and (A-A) ∩ (B-B) = {0}, then
|A| ≤ (1/√2 + o(1))√N.

The key idea: the C(|A|,2) + C(|B|,2) distinct differences from
A and B together are disjoint nonzero integers in {-(N-1),...,N-1}.
When |A| = |B| = m, we need 2·C(m,2) ≤ 2(N-1), so m(m-1) ≤ 2(N-1),
giving m ≤ (1/√2 + o(1))√N. -/

/-- Tao's bound: when |A| = |B|, both equal m, we get m^2 ≤ 2N+1.
    This follows from disjoint_diff_combined_bound: 2·C(m,2) ≤ N,
    so m(m-1) ≤ N, giving m^2 ≤ N + m ≤ 2N for large N. -/
theorem tao_equal_size_bound (A B : Finset ℤ) (N : ℕ)
    (hA : IsSidonSet A) (hB : IsSidonSet B)
    (hRA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ N) (hRB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ N)
    (hD : DisjointDifferences A B) (hEq : A.card = B.card) :
  (A.card : ℝ) ^ 2 ≤ 2 * N + 1 := by
  -- From disjoint_diff_combined_bound: C(m,2) + C(m,2) ≤ N
  have hcomb := disjoint_diff_combined_bound A B N hA hB hRA hRB hD
  rw [← hEq] at hcomb
  -- hcomb : A.card.choose 2 + A.card.choose 2 ≤ N
  have he := two_mul_choose_two A.card
  -- So m*(m-1) ≤ N (exactly, via the 2·choose2 bridge), in subtraction-free form
  have hz' : A.card * A.card ≤ N + A.card := by omega
  -- m ≤ N + 1 (from m² ≤ N + m)
  have hle : A.card ≤ N + 1 := by nlinarith [hz']
  -- m² ≤ 2N+1 in ℕ, then cast to ℝ
  have hsq : A.card * A.card ≤ 2 * N + 1 := by nlinarith [hz', hle]
  calc (A.card : ℝ) ^ 2 = ↑(A.card * A.card) := by push_cast; ring
    _ ≤ ↑(2 * N + 1) := Nat.cast_le.mpr hsq
    _ = 2 * ↑N + 1 := by push_cast; ring

/-- The number of elements of the difference set of a Sidon set A is |A|²-|A|+1:
    the |A|²-|A| off-diagonal pairs map injectively, plus 0 from the diagonal. -/
theorem sidon_diff_count (A : Finset ℤ) (hS : IsSidonSet A) (hA : A.Nonempty) :
  (diffSet A).card = A.card * A.card - A.card + 1 := by
  set f : ℤ × ℤ → ℤ := fun p => p.1 - p.2
  -- Injectivity on off-diagonal pairs
  have hinj : Set.InjOn f ↑A.offDiag := by
    intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
    simp only [Finset.mem_coe, Finset.mem_offDiag] at h₁ h₂
    exact Prod.ext (sidon_diff_injective A hS h₁.1 h₁.2.1 h₂.1 h₂.2.1 h₁.2.2 heq).1
      (sidon_diff_injective A hS h₁.1 h₁.2.1 h₂.1 h₂.2.1 h₁.2.2 heq).2
  -- Diagonal maps to {0}
  have hdiag_image : A.diag.image f = {0} := by
    ext x; simp only [Finset.mem_image, Finset.mem_diag, Finset.mem_singleton, f]
    constructor
    · rintro ⟨⟨a, b⟩, hmem, hfx⟩
      simp only at hmem hfx
      omega
    · intro hx; rw [hx]; obtain ⟨a, ha⟩ := hA
      exact ⟨(a, a), ⟨ha, rfl⟩, by simp⟩
  -- 0 is not in the off-diagonal image
  have hzero_not : (0 : ℤ) ∉ A.offDiag.image f := by
    intro h0; obtain ⟨⟨a, b⟩, hp, heq⟩ := Finset.mem_image.mp h0
    simp only [Finset.mem_offDiag] at hp
    simp only [f] at heq
    exact hp.2.2 (by omega)
  have hpos : 1 ≤ A.card := Finset.Nonempty.card_pos hA
  have hle : A.card ≤ A.card * A.card := by nlinarith
  -- Combine: |diffSet A| = 1 + |offDiag|
  suffices h : (diffSet A).card + A.card = A.card * A.card + 1 by omega
  calc (diffSet A).card + A.card
      = ((A.diag ∪ A.offDiag).image f).card + A.card := by
          rw [Finset.diag_union_offDiag]; rfl
    _ = (A.diag.image f ∪ A.offDiag.image f).card + A.card := by
          rw [Finset.image_union]
    _ = ((A.diag.image f).card + (A.offDiag.image f).card) + A.card := by
          rw [Finset.card_union_of_disjoint
            (by rw [hdiag_image]; exact Finset.disjoint_singleton_left.mpr hzero_not)]
    _ = 1 + A.offDiag.card + A.card := by
          rw [hdiag_image, Finset.card_singleton, Finset.card_image_of_injOn hinj]
    _ = A.card * A.card + 1 := by
          rw [Finset.offDiag_card]; omega

/-- When differences are disjoint, the combined difference set has cardinality
    |A|²-|A| + |B|²-|B| + 1 (the nonzero parts are disjoint, sharing only {0}). -/
theorem disjoint_diff_total (A B : Finset ℤ)
    (hA : IsSidonSet A) (hB : IsSidonSet B) (hD : DisjointDifferences A B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
  (diffSet A ∪ diffSet B).card ≥
    A.card * A.card - A.card + B.card * B.card - B.card + 1 := by
  -- The intersection is exactly {0}
  have h_inter : diffSet A ∩ diffSet B = {0} := by
    ext d; simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · exact fun ⟨hda, hdb⟩ => hD d hda hdb
    · intro hd; rw [hd]; constructor
      · simp only [diffSet, Finset.mem_image, Finset.mem_product]
        obtain ⟨a, ha⟩ := hAne; exact ⟨(a, a), ⟨ha, ha⟩, by simp⟩
      · simp only [diffSet, Finset.mem_image, Finset.mem_product]
        obtain ⟨b, hb⟩ := hBne; exact ⟨(b, b), ⟨hb, hb⟩, by simp⟩
  -- Use inclusion-exclusion
  have h_ie := Finset.card_union_add_card_inter (diffSet A) (diffSet B)
  rw [h_inter, Finset.card_singleton, sidon_diff_count A hA hAne,
      sidon_diff_count B hB hBne] at h_ie
  -- h_ie: card(A∪B) + 1 = (cA + 1) + (cB + 1)  where cA = A²-A, cB = B²-B
  set cA := A.card * A.card - A.card
  set cB := B.card * B.card - B.card
  omega
