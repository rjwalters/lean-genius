/-
# Erdős Problem 347: Complete Sequences with Ratio Tending to 2

Is there a sequence `A = {a₁ ≤ a₂ ≤ ⋯}` of positive integers with
`lim a_{n+1}/a_n = 2` such that for every cofinite subsequence `A'`,
the set of subset sums `P(A')` has density 1?

**Solved** affirmatively (ebarschkis, based on ideas by Tao and
van Doorn). A formal Lean proof exists.

*Reference:* [erdosproblems.com/347](https://www.erdosproblems.com/347)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

/- ## Subset sums -/

/-- The set of finite subset sums of a set `A ⊆ ℕ`. -/
def subsetSums (A : Set ℕ) : Set ℕ :=
    { s | ∃ (S : Finset ℕ), (↑S : Set ℕ) ⊆ A ∧ S.sum id = s }

/- ## Asymptotic density -/

/-- The counting function `|S ∩ {1,…,N}|`. -/
noncomputable def countIn (S : Set ℕ) (N : ℕ) : ℕ :=
    ((Finset.Icc 1 N).filter (· ∈ S)).card

/-- A set `S ⊆ ℕ` has density `δ` if `|S ∩ {1,…,N}| / N → δ`. -/
def HasDensity (S : Set ℕ) (δ : ℚ) : Prop :=
    ∀ ε : ℚ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        |((countIn S N : ℚ) / (N : ℚ)) - δ| < ε

/- ## Monotone sequences with ratio limit -/

/-- A sequence `a : ℕ → ℕ` is monotone nondecreasing. -/
def IsMonotone (a : ℕ → ℕ) : Prop :=
    ∀ m n : ℕ, m ≤ n → a m ≤ a n

/-- The ratio `a(n+1)/a(n)` tends to `r`. -/
def HasRatioLimit (a : ℕ → ℕ) (r : ℚ) : Prop :=
    ∀ ε : ℚ, 0 < ε →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        0 < a n →
          |((a (n + 1) : ℚ) / (a n : ℚ)) - r| < ε

/- ## Cofinite subsequences -/

/-- A cofinite subsequence: the range of `a ∘ ι` where `ι` omits only
finitely many indices. -/
def IsCofiniteSubseq (a ι : ℕ → ℕ) : Prop :=
    StrictMono ι ∧ (Set.range ι)ᶜ.Finite

/-- The image of a cofinite subsequence. -/
def cofiniteImage (a ι : ℕ → ℕ) : Set ℕ :=
    Set.range (a ∘ ι)

/- ## Main conjecture (solved) -/

/-- Erdős Problem 347 (solved): There exists a monotone sequence with
ratio limit 2 such that every cofinite subsequence has subset sums
of density 1. -/
def ErdosProblem347 : Prop :=
    ∃ (a : ℕ → ℕ),
      IsMonotone a ∧
      HasRatioLimit a 2 ∧
      ∀ (ι : ℕ → ℕ), IsCofiniteSubseq a ι →
        HasDensity (subsetSums (cofiniteImage a ι)) 1

/-- The answer to Erdős Problem 347 is affirmative. -/
axiom erdos347_affirmative : ErdosProblem347

/- ## Basic properties -/

/-- The empty subset sum is 0: `0 ∈ P(A)` for any `A`. -/
theorem zero_mem_subsetSums (A : Set ℕ) :
    0 ∈ subsetSums A :=
  ⟨∅, by simp, by simp⟩

/-- Subset sums grow when adding a new element not already in the witness.
    NOTE: The original `subsetSums_add` axiom (s ∈ P(A) → a ∈ A → s+a ∈ P(A))
    was INCORRECT — it fails when a is already in the witness finset S
    (e.g., A = {2,3}, s = 5, a = 2: 7 ∉ P({2,3}) = {0,2,3,5}).
    This correct version requires a fresh witness where a ∉ S. -/
theorem subsetSums_insert (A : Set ℕ) (S : Finset ℕ) (a : ℕ)
    (hS : (↑S : Set ℕ) ⊆ A) (ha : a ∈ A) (hna : a ∉ S) :
    S.sum id + a ∈ subsetSums A :=
  ⟨insert a S, by simpa [Set.insert_subset_iff] using ⟨ha, hS⟩,
   by rw [Finset.sum_insert hna]; ring⟩

/-- If `A ⊆ B`, then `P(A) ⊆ P(B)`. -/
theorem subsetSums_mono (A B : Set ℕ) (h : A ⊆ B) :
    subsetSums A ⊆ subsetSums B := by
  intro s ⟨S, hS, hs⟩
  exact ⟨S, Set.Subset.trans hS h, hs⟩

/-- Any element of `A` is in `P(A)` (singleton subset sum). -/
theorem mem_subsetSums_of_mem (A : Set ℕ) (a : ℕ) (ha : a ∈ A) :
    a ∈ subsetSums A :=
  ⟨{a}, by simpa using ha, by simp⟩

/-- Disjoint witnesses combine: `∑S + ∑T ∈ P(A)` when `S, T ⊆ A` are disjoint. -/
theorem subsetSums_add_of_disjoint (A : Set ℕ) (S T : Finset ℕ)
    (hS : (↑S : Set ℕ) ⊆ A) (hT : (↑T : Set ℕ) ⊆ A) (hdisj : Disjoint S T) :
    S.sum id + T.sum id ∈ subsetSums A := by
  refine ⟨S ∪ T, ?_, Finset.sum_union hdisj⟩
  simp only [Finset.coe_union]
  exact Set.union_subset hS hT

/-- The image of a cofinite subsequence is contained in the range of `a`. -/
theorem cofiniteImage_subset (a ι : ℕ → ℕ) :
    cofiniteImage a ι ⊆ Set.range a := by
  intro x ⟨n, hn⟩
  exact ⟨ι n, hn⟩

/-- The identity is a cofinite subsequence (keeps all indices). -/
theorem isCofiniteSubseq_id (a : ℕ → ℕ) : IsCofiniteSubseq a id :=
  ⟨strictMono_id, by simp [Set.range_id]⟩

-- ============================================================================
-- § DENSITY INFRASTRUCTURE
-- ============================================================================

/-- The counting function is monotone: A ⊆ B → countIn A N ≤ countIn B N. -/
theorem countIn_mono (A B : Set ℕ) (h : A ⊆ B) (N : ℕ) :
    countIn A N ≤ countIn B N := by
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro x _
  exact h

/-- The count is bounded by N: countIn S N ≤ N. -/
theorem countIn_le (S : Set ℕ) (N : ℕ) : countIn S N ≤ N := by
  apply le_trans (Finset.card_filter_le _ _)
  simp [Finset.card_Icc]

/-- Density is monotone upward: if A ⊆ B and A has density 1, then B also has density 1.
    Proof: sandwich countIn A N / N ≤ countIn B N / N ≤ 1 with countIn A N / N → 1. -/
theorem hasDensity_one_of_superset (A B : Set ℕ) (hAB : A ⊆ B)
    (hA : HasDensity A 1) : HasDensity B 1 := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hA ε hε
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℚ) < N := by exact_mod_cast Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN1)
  have hA_close := hN₀ N hNN₀
  have step1 : (countIn A N : ℚ) / N ≤ (countIn B N : ℚ) / N :=
    (div_le_div_right hNpos).mpr (by exact_mod_cast countIn_mono A B hAB N)
  have step2 : (countIn B N : ℚ) / N ≤ 1 :=
    div_le_one_of_le (by exact_mod_cast countIn_le B N) hNpos.le
  have step3 : (countIn A N : ℚ) / N ≤ 1 :=
    div_le_one_of_le (by exact_mod_cast countIn_le A N) hNpos.le
  rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hA_close
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

-- ============================================================================
-- § CONSEQUENCES OF THE AXIOM
-- ============================================================================

/-- From erdos347_affirmative: the full sequence (identity subsequence) has density-1 subset sums.
    This instantiates the existential with the identity cofinite subsequence. -/
theorem erdos347_range_density_one :
    ∃ (a : ℕ → ℕ), IsMonotone a ∧ HasRatioLimit a 2 ∧
      HasDensity (subsetSums (Set.range a)) 1 := by
  obtain ⟨a, hm, hr, hd⟩ := erdos347_affirmative
  refine ⟨a, hm, hr, ?_⟩
  have h := hd id (isCofiniteSubseq_id a)
  simp only [cofiniteImage, Function.comp_id] at h
  exact h

/-- SubsetSums are invariant under the cofinite subsequence structure:
    cofiniteImage a ι has subset sums contained in subsetSums (Set.range a). -/
theorem subsetSums_cofiniteImage_subset (a ι : ℕ → ℕ) :
    subsetSums (cofiniteImage a ι) ⊆ subsetSums (Set.range a) :=
  subsetSums_mono _ _ (cofiniteImage_subset a ι)

/-- For any cofinite subsequence of the Erdős-347 witness, the subset sums of
    that subsequence also have density ≥ 1 as a subset of P(range a). -/
theorem erdos347_cofinite_density_via_superset :
    ∃ (a : ℕ → ℕ), IsMonotone a ∧ HasRatioLimit a 2 ∧
      ∀ (ι : ℕ → ℕ), IsCofiniteSubseq a ι →
        HasDensity (subsetSums (Set.range a)) 1 := by
  obtain ⟨a, hm, hr, hd⟩ := erdos347_affirmative
  refine ⟨a, hm, hr, fun ι hι => ?_⟩
  have hcof := hd ι hι
  exact hasDensity_one_of_superset _ _ (subsetSums_cofiniteImage_subset a ι) hcof
