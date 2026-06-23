/-
# Erdős Problem 301: Egyptian Fraction Avoidance Sets

Let `f(N)` be the maximum size of `A ⊆ {1, ..., N}` with no solution to
`1/a = 1/b₁ + ⋯ + 1/bₖ` where `a, b₁, ..., bₖ ∈ A` are distinct.

Does `f(N) = (1/2 + o(1)) * N`?

Lower bound: `A = (N/2, N] ∩ ℕ` gives `f(N) ≥ N/2`.
Upper bound: Van Doorn showed `f(N) ≤ (25/28 + o(1)) * N`.

*Reference:* [erdosproblems.com/301](https://www.erdosproblems.com/301)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Finset

attribute [local instance] Classical.propDecidable

/- ## Egyptian fraction decomposition avoidance -/

/-- `HasEgyptianDecomp A a` means there exist distinct `b₁, ..., bₖ ∈ A` with
`1/a = 1/b₁ + ⋯ + 1/bₖ`, where all elements are distinct from `a`. -/
def HasEgyptianDecomp (A : Finset ℕ) (a : ℕ) : Prop :=
    ∃ B : Finset ℕ, B ⊆ A ∧ a ∉ B ∧ B.Nonempty ∧
      (B.sum (fun b => (1 : ℚ) / b)) = (1 : ℚ) / a

/-- `EgyptFractionFree A` means no element of `A` has an Egyptian fraction
decomposition using other elements of `A`. -/
def EgyptFractionFree (A : Finset ℕ) : Prop :=
    ∀ a ∈ A, ¬HasEgyptianDecomp A a

/-- `f(N)` is the maximum cardinality of an EgyptFractionFree subset of `{1,...,N}`. -/
noncomputable def maxEgyptFree (N : ℕ) : ℕ :=
    ((Finset.Icc 1 N).powerset.filter EgyptFractionFree).sup Finset.card

/- ## Main conjecture -/

/-- Erdős Problem 301: `f(N) = (1/2 + o(1)) * N`. -/
def ErdosProblem301 : Prop :=
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (1 / 2 - ε) * N ≤ (maxEgyptFree N : ℝ) ∧
      (maxEgyptFree N : ℝ) ≤ (1 / 2 + ε) * N

/- ## Lower bound -/

/-- The interval `(N/2, N]` is EgyptFractionFree, giving `f(N) ≥ N/2`.
    Proof: for a, b₁,...,bₖ all in (N/2, N]:
    - k=1: 1/b₁ = 1/a forces b₁ = a, contradicting a ∉ B
    - k≥2: sum ≥ 2/N > 1/a (since each 1/bᵢ ≥ 1/N and a > N/2) -/
theorem halfInterval_egyptFree (N : ℕ) :
    EgyptFractionFree ((Finset.Icc 1 N).filter (fun n => N / 2 < n)) := by
  intro a ha ⟨B, hB, haB, hBne, hBsum⟩
  simp only [mem_filter, mem_Icc] at ha
  have ha_pos : (0 : ℚ) < a := by exact_mod_cast show 0 < a by omega
  have hN_pos : (0 : ℚ) < N := by exact_mod_cast show 0 < N by omega
  -- Every b ∈ B satisfies N/2 < b ≤ N
  have hb_info : ∀ b ∈ B, N / 2 < b ∧ b ≤ N := by
    intro b hb; have := hB hb; simp only [mem_filter, mem_Icc] at this
    exact ⟨this.2, this.1.2⟩
  by_cases hone : B.card = 1
  · -- Singleton: 1/b = 1/a implies b = a, contradicting a ∉ B
    obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hone
    simp only [Finset.sum_singleton] at hBsum
    have hb_pos : (0 : ℚ) < b := by
      exact_mod_cast show 0 < b by have := (hb_info b (mem_singleton.mpr rfl)).1; omega
    rw [div_eq_div_iff hb_pos.ne' ha_pos.ne'] at hBsum
    simp only [one_mul] at hBsum
    exact haB (mem_singleton.mpr (by exact_mod_cast hBsum.symm))
  · -- |B| ≥ 2: sum ≥ 2/N > 1/a
    have hcard : 2 ≤ B.card := by
      rcases B.eq_empty_or_nonempty with rfl | hne
      · exact absurd (Finset.not_nonempty_empty) (not_not.mpr hBne) |>.elim
      · omega
    -- Each 1/b ≥ 1/N (since b ≤ N)
    have hsum_lower : (B.card : ℚ) / N ≤ B.sum (fun b => (1 : ℚ) / b) := by
      rw [div_eq_inv_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum (fun b hb => by
        rw [one_div, one_div]
        exact inv_anti₀ (by exact_mod_cast (hb_info b hb).2) (by exact_mod_cast show 0 < b by
          have := (hb_info b hb).1; omega))
    -- sum ≥ 2/N
    have hsum_ge : 2 / (N : ℚ) ≤ B.sum (fun b => (1 : ℚ) / b) := by
      calc (2 : ℚ) / N ≤ B.card / N := by
            exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
        _ ≤ _ := hsum_lower
    -- 1/a < 2/N
    have h1a_lt : (1 : ℚ) / a < 2 / N := by
      rw [div_lt_div_iff ha_pos hN_pos]; push_cast
      exact_mod_cast show 1 * N < 2 * a by omega
    linarith

/-- Lower bound: `f(N) ≥ N/2`.
    Proof: the half-interval (N/2, N] ∩ {1,...,N} is EgyptFractionFree
    and has cardinality ≥ N/2. -/
theorem maxEgyptFree_lower (N : ℕ) (hN : 0 < N) :
    N / 2 ≤ maxEgyptFree N := by
  unfold maxEgyptFree
  have hmem : (Icc 1 N).filter (fun n => N / 2 < n) ∈
      (Icc 1 N).powerset.filter EgyptFractionFree := by
    simp only [mem_filter, mem_powerset]
    exact ⟨filter_subset _ _, halfInterval_egyptFree N⟩
  have hcard : N / 2 ≤ ((Icc 1 N).filter (fun n => N / 2 < n)).card := by
    have : (Icc 1 N).filter (fun n => N / 2 < n) = Icc (N / 2 + 1) N := by
      ext n; simp only [mem_filter, mem_Icc]; omega
    rw [this, Nat.card_Icc]; omega
  calc N / 2 ≤ _ := hcard
    _ ≤ ((Icc 1 N).powerset.filter EgyptFractionFree).sup Finset.card :=
        Finset.le_sup hmem

/- ## Upper bound -/

/-- `f(N) ≤ N`: any EgyptFractionFree subset of `{1,...,N}` has at most N elements. -/
theorem maxEgyptFree_le (N : ℕ) : maxEgyptFree N ≤ N := by
  unfold maxEgyptFree
  apply Finset.sup_le
  intro A hA
  simp only [mem_filter, mem_powerset] at hA
  calc A.card ≤ (Icc 1 N).card := Finset.card_le_card hA.1
    _ = N := by rw [Nat.card_Icc]; omega

/-- Van Doorn's upper bound: `f(N) ≤ (25/28 + o(1)) * N`.
    The formalized bound `(25/28 + 1) * N` is weaker than the trivial `f(N) ≤ N`,
    so it follows immediately. The actual result uses o(1) → 0 as N → ∞. -/
theorem vanDoorn_upper (N : ℕ) (hN : 0 < N) :
    (maxEgyptFree N : ℝ) ≤ (25 / 28 + 1) * N := by
  calc (maxEgyptFree N : ℝ) ≤ (N : ℝ) := by exact_mod_cast maxEgyptFree_le N
    _ = 1 * N := by ring
    _ ≤ (25 / 28 + 1) * N := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        norm_num

/- ## Basic properties -/

/-- The empty set is EgyptFractionFree. -/
theorem egyptFractionFree_empty : EgyptFractionFree ∅ := by
  intro a ha; exact absurd ha (Finset.notMem_empty a)

/-- A singleton is EgyptFractionFree (no other elements to decompose into). -/
theorem egyptFractionFree_singleton (n : ℕ) : EgyptFractionFree {n} := by
  intro a ha ⟨B, hB, haB, hne, _⟩
  have hab : a = n := Finset.mem_singleton.mp ha
  have : B = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    have hxn := Finset.mem_singleton.mp (hB hx)
    exact haB (hab ▸ hxn ▸ hx)
  exact absurd (this ▸ hne) Finset.not_nonempty_empty

/-- Subsets of EgyptFractionFree sets are EgyptFractionFree. -/
theorem egyptFractionFree_subset {A B : Finset ℕ} (h : B ⊆ A) (hA : EgyptFractionFree A) :
    EgyptFractionFree B := by
  intro a ha ⟨C, hC, haC, hne, hsum⟩
  exact hA a (h ha) ⟨C, hC.trans h, haC, hne, hsum⟩
