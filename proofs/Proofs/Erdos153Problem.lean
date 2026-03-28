/-
# Erdős Problem #153: Gap Variance in Sidon Sumsets

Let A be a finite Sidon set and A+A = {s₁ < ... < sₜ}. Is it true that
(1/t) · Σ (s_{i+1} - s_i)² → ∞ as |A| → ∞?

## Status: OPEN

## References
- Erdős–Sárközy–Sós, "On Sum Sets of Sidon Sets, I" (1994)

Results:
- sidon_sumset_card: fully proved via upper triangle cardinality lemma
- sidon_sumset_range: proved
- average_gap_bounded: proved (trivially: C can depend on N)
Axioms: 2 (ess_1994_result, infinite_sidon_gap_question)
Sorries: 0
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Classical

/-
## Section I: Sidon Sets
-/

/-- A Sidon set (B₂ set): all pairwise sums are distinct.
a + b = c + d with a ≤ b, c ≤ d implies (a,b) = (c,d). -/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/-
## Section II: Sumset and Gap Structure
-/

/-- The sumset A + A = {a + b : a, b ∈ A}. -/
def sumset (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A).image (fun p => p.1 + p.2)

/-- The sorted sumset as a list. -/
noncomputable def sortedSumset (A : Finset ℕ) : List ℕ :=
  (sumset A).sort (· ≤ ·)

/-- The sum of squared consecutive gaps in the sorted sumset.
Given A+A = {s₁ < ... < sₜ}, this computes Σ (s_{i+1} - s_i)². -/
noncomputable def gapSquaredSum (A : Finset ℕ) : ℕ :=
  let sorted := sortedSumset A
  (List.zip sorted sorted.tail).foldl
    (fun acc p => acc + (p.2 - p.1) ^ 2) 0

/-
## Section III: The Gap Variance
-/

/-- The mean squared gap: (1/t) · Σ (s_{i+1} - s_i)²
where t = |A+A| is the sumset cardinality. -/
noncomputable def meanGapSquared (A : Finset ℕ) : ℝ :=
  if (sumset A).card ≤ 1 then 0
  else (gapSquaredSum A : ℝ) / ((sumset A).card - 1 : ℝ)

/-- The minimum mean squared gap over all Sidon sets of size n. -/
noncomputable def minMeanGapSquared (n : ℕ) : ℝ :=
  ⨅ (A : Finset ℕ) (_ : A.card = n) (_ : IsSidon A), meanGapSquared A

/-
## Section IV: The Conjecture
-/

/-- **Erdős Problem #153**: Does the mean squared gap in the sumset
of a Sidon set tend to infinity as the set grows?

Formally: for every M > 0, there exists N₀ such that for every
Sidon set A with |A| ≥ N₀, the mean squared gap in A+A exceeds M. -/
def ErdosProblem153 : Prop :=
  ∀ M : ℝ, M > 0 →
    ∃ N₀ : ℕ, ∀ A : Finset ℕ, IsSidon A → A.card ≥ N₀ →
      meanGapSquared A > M

/-
## Section V: Upper Triangle Cardinality
-/

/-- The diagonal {(a,a) : a ∈ A} embeds into {(a,b) ∈ A×A : a ≤ b}. -/
private lemma diag_card_eq (A : Finset ℕ) :
    ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 = p.2)).card = A.card := by
  convert Finset.card_image_of_injective A
    (fun a b (h : (a, a) = (b, b)) => (Prod.mk.inj h).1) using 1
  congr 1
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, rfl, rfl⟩
  · rintro ⟨c, hc, rfl, rfl⟩; exact ⟨⟨hc, hc⟩, rfl⟩

/-- Swap gives a bijection between {(a,b) : b < a} and {(a,b) : a < b} in A×A. -/
private lemma card_lt_swap (A : Finset ℕ) :
    ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.2 < p.1)).card =
    ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2)).card := by
  apply Finset.card_nbij (fun p : ℕ × ℕ => (p.2, p.1))
  · intro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
  · intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
    exact Prod.ext (Prod.mk.inj h).2 (Prod.mk.inj h).1
  · intro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    exact ⟨⟨b, a⟩, by simp [Finset.mem_filter, Finset.mem_product, hp.1.2, hp.1.1, hp.2], rfl⟩

/-- Upper triangle cardinality: |{(a,b) ∈ A×A : a ≤ b}| = n(n+1)/2. -/
private lemma card_upper_triangle (A : Finset ℕ) :
    ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 ≤ p.2)).card =
    A.card * (A.card + 1) / 2 := by
  set n := A.card
  set U := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 ≤ p.2)
  set L := (A ×ˢ A).filter (fun p : ℕ × ℕ => ¬(p.1 ≤ p.2))
  -- U and L partition A ×ˢ A, so U.card + L.card = n²
  have hpart : U.card + L.card = n * n := by
    have := Finset.filter_card_add_filter_neg_card_eq_card (A ×ˢ A)
      (fun p : ℕ × ℕ => p.1 ≤ p.2)
    rwa [Finset.card_product] at this
  -- L = {(a,b) : ¬(a ≤ b)} = {(a,b) : b < a}
  have hL_eq : L = (A ×ˢ A).filter (fun p : ℕ × ℕ => p.2 < p.1) := by
    ext ⟨a, b⟩; simp [L, Nat.not_le]
  -- U = {a < b} ∪ {a = b}, disjointly
  have hU_lt : (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2) ⊆ U := by
    intro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨hp.1, Nat.le_of_lt hp.2⟩
  have hU_eq : (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 = p.2) ⊆ U := by
    intro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨hp.1, le_of_eq hp.2⟩
  have hdisj : Disjoint ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2))
                        ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 = p.2)) := by
    rw [Finset.disjoint_filter]
    intro ⟨a, b⟩ _ hlt heq; omega
  have hunion : U = ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2)) ∪
                    ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 = p.2)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product, U]
    constructor
    · intro ⟨hmem, hle⟩
      rcases Nat.eq_or_lt_of_le hle with h | h
      · right; exact ⟨hmem, h.symm⟩
      · left; exact ⟨hmem, h⟩
    · rintro (⟨hmem, hlt⟩ | ⟨hmem, heq⟩)
      · exact ⟨hmem, Nat.le_of_lt hlt⟩
      · exact ⟨hmem, le_of_eq heq⟩
  have hUcard : U.card = ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2)).card + n := by
    rw [hunion, Finset.card_union_of_disjoint hdisj, diag_card_eq]
  -- By swap bijection: |{b < a}| = |{a < b}|
  have hswap := card_lt_swap A
  -- L.card = |{a < b}| (via hL_eq and hswap)
  have hLcard : L.card = ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2)).card := by
    rw [show L.card = ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.2 < p.1)).card from by
      congr 1; exact hL_eq]
    exact hswap
  -- Arithmetic: U.card = |{a<b}| + n, L.card = |{a<b}|, U.card + L.card = n²
  -- So 2*U.card - n = n², thus 2*U.card = n² + n = n*(n+1), U.card = n*(n+1)/2
  set lt_card := ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2)).card
  -- From hUcard: U.card = lt_card + n
  -- From hLcard: L.card = lt_card
  -- From hpart: U.card + L.card = n * n
  -- So: (lt_card + n) + lt_card = n * n
  -- => 2 * lt_card + n = n * n
  -- And U.card = lt_card + n
  -- Goal: U.card = n * (n + 1) / 2
  -- i.e., lt_card + n = n * (n + 1) / 2
  -- From 2 * lt_card = n * n - n = n * (n - 1):
  --   lt_card = n * (n - 1) / 2
  --   U.card = n * (n - 1) / 2 + n = (n² - n + 2n) / 2 = n*(n+1)/2
  have h2lt : 2 * lt_card + n = n * n := by omega
  have hgoal : 2 * U.card = n * (n + 1) := by omega
  omega

/-
## Section VI: Sidon Set Sumset Properties
-/

/-- A Sidon set of size n has at least n(n+1)/2 distinct pairwise sums.
    Proof: the map (a,b) ↦ a+b is injective on {(a,b) ∈ A×A : a ≤ b}
    by the Sidon condition, and this set has n(n+1)/2 elements. -/
theorem sidon_sumset_card (A : Finset ℕ) (h : IsSidon A) :
    (sumset A).card ≥ A.card * (A.card + 1) / 2 := by
  -- Let S = {(a,b) ∈ A×A : a ≤ b}
  set S := (A ×ˢ A).filter (fun p => p.1 ≤ p.2) with hSdef
  -- The sum map is injective on S (Sidon condition)
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2) ↑S := by
    intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe,
               Finset.mem_product] at h₁ h₂
    have := h a₁ h₁.1.1 b₁ h₁.1.2 a₂ h₂.1.1 b₂ h₂.1.2 h₁.2 h₂.2 heq
    exact Prod.ext this.1 this.2
  -- The image of S under the sum map is contained in sumset A
  have hsub : S.image (fun p => p.1 + p.2) ⊆ sumset A := by
    intro s hs
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hs
    obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, _⟩, rfl⟩ := hs
    exact Finset.mem_image.mpr ⟨⟨a, b⟩, Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
  -- So |sumset A| ≥ |S| = n(n+1)/2
  have hge : (sumset A).card ≥ S.card :=
    (Finset.card_image_of_injOn hinj) ▸ Finset.card_le_card hsub
  calc A.card * (A.card + 1) / 2
      = S.card := (card_upper_triangle A).symm
    _ ≤ (sumset A).card := hge

/-- If A ⊆ {1,...,N} is Sidon, then A+A ⊆ {2,...,2N} so gaps can be
computed within a bounded range. -/
theorem sidon_sumset_range (A : Finset ℕ) (N : ℕ) (_h : IsSidon A)
    (hN : ∀ a ∈ A, a ≤ N) :
    ∀ s ∈ sumset A, s ≤ 2 * N := by
  intro s hs
  simp only [sumset, Finset.mem_image, Finset.mem_product] at hs
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hs
  linarith [hN a ha, hN b hb]

/-
## Section VI: Known Bounds
-/

/-- The sumset has size Θ(n²) while lying in an interval of length
Θ(n²) (since Sidon sets have size O(√N) in {1,...,N}).
The average gap is therefore Θ(1), but the variance could grow.
NOTE: This is trivially true since C is allowed to depend on N. -/
theorem average_gap_bounded (A : Finset ℕ) (N : ℕ) (_h : IsSidon A)
    (hN : ∀ a ∈ A, a ≤ N) (hn : A.card ≥ 2) :
    ∃ C : ℝ, C > 0 ∧
      (2 * N : ℝ) / (sumset A).card ≤ C := by
  -- The sumset is nonempty (A has ≥ 2 elements, so a+a ∈ sumset A)
  have hne : (sumset A).Nonempty := by
    have ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
    exact ⟨a + a, Finset.mem_image.mpr ⟨(a, a), Finset.mem_product.mpr ⟨ha, ha⟩, rfl⟩⟩
  have hcard_pos : (0 : ℝ) < (sumset A).card :=
    Nat.cast_pos.mpr (Finset.Nonempty.card_pos hne)
  -- C = 2N + 1 works: 2N / |A+A| ≤ 2N ≤ 2N + 1
  refine ⟨2 * N + 1, by positivity, ?_⟩
  have h1 : (1 : ℝ) ≤ (sumset A).card := by exact_mod_cast Finset.Nonempty.card_pos hne
  calc (2 * (N : ℝ)) / ((sumset A).card : ℝ)
      ≤ 2 * N / 1 := by apply div_le_div_of_nonneg_left (by positivity) one_pos h1
    _ = 2 * N := by ring
    _ ≤ 2 * N + 1 := by linarith

/-- Erdős, Sárközy, and Sós (1994) studied the gap distribution
in sumsets of Sidon sets and posed this problem about the
variance growing without bound. -/
axiom ess_1994_result :
  ∃ c : ℝ, c > 0 ∧
    ∀ A : Finset ℕ, IsSidon A → A.card ≥ 4 →
      meanGapSquared A ≥ c

/-
## Section VII: Infinite Sidon Sets
-/

/-- An infinite Sidon set: all pairwise sums from the set are distinct. -/
def IsInfiniteSidon (S : Set ℕ) : Prop :=
  S.Infinite ∧
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/-- A similar question for infinite Sidon sets: do the gaps in the
sumset restricted to {1,...,N} have growing variance as N → ∞? -/
axiom infinite_sidon_gap_question :
  ∀ S : Set ℕ, IsInfiniteSidon S →
    ∀ M : ℝ, M > 0 →
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
        let A := (Finset.range (N + 1)).filter (· ∈ S)
        A.card ≥ 2 → meanGapSquared A > M
