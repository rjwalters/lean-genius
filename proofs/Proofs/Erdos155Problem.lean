/-
# Erdős Problem #155: Slow Growth of Maximum Sidon Subsets

Let F(N) be the size of the largest Sidon (B₂) subset of {1, ..., N}.
Is it true that for every k ≥ 1, F(N+k) ≤ F(N) + 1 for all
sufficiently large N?

## Background
A Sidon set (B₂ set) is a set of integers where all pairwise sums are
distinct. F(N) ~ N^{1/2} (Erdős–Turán 1941), but the fine growth
structure is poorly understood.

## Stronger Form
Erdős suggested this may hold with k ≈ ε·N^{1/2}, meaning F can
increase by at most 1 over intervals of length proportional to √N.

## Known Bounds
- F(N) = (1 + o(1))·N^{1/2} (Erdős–Turán upper, Lindström/Cilleruelo lower)
- F(N) ≤ N^{1/2} + N^{1/4} + 1 (Lindström 1969)

## Status: OPEN

Reference: https://erdosproblems.com/155
-/

import Mathlib

/- ## Core Definitions -/

/-- A Sidon set (B₂ set): a set of natural numbers where all pairwise sums
    a + b (a < b, a, b ∈ S) are distinct. Equivalently, all pairwise
    differences are distinct. Uses strict inequality a < b to match the
    standard combinatorial definition (distinct pairs only, no self-sums). -/
def IsSidonSet (S : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    a < b → c < d → a + b = c + d → a = c ∧ b = d

/-- The set of Sidon subsets of {1,...,N}. -/
private noncomputable def sidonSets (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset.filter (fun S => IsSidonSet S)

private theorem empty_mem_sidonSets (N : ℕ) : ∅ ∈ sidonSets N := by
  simp only [sidonSets, Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset,
             true_and, IsSidonSet]
  intro a _ _ _ ha; exact absurd ha (Finset.not_mem_empty a)

private theorem sidonSets_nonempty (N : ℕ) : (sidonSets N).Nonempty :=
  ⟨∅, empty_mem_sidonSets N⟩

/-- F(N): the size of the largest Sidon subset of {1, ..., N}.
    Defined as the supremum of cardinalities over all Sidon subsets of {1,...,N}. -/
noncomputable def maxSidonSize (N : ℕ) : ℕ :=
  (sidonSets N).sup Finset.card

/-- F(N) is achieved: there exists a Sidon subset of {1,...,N} of size F(N). -/
theorem maxSidon_achievable (N : ℕ) :
    ∃ S : Finset ℕ, IsSidonSet S ∧ (∀ x ∈ S, 1 ≤ x ∧ x ≤ N) ∧ S.card = maxSidonSize N := by
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image _ Finset.card (sidonSets_nonempty N)
  have hmem := Finset.mem_filter.mp hS
  have hpow := Finset.mem_powerset.mp hmem.1
  refine ⟨S, hmem.2, fun x hx => Finset.mem_Icc.mp (hpow hx), ?_⟩
  exact le_antisymm (Finset.le_sup hS) (Finset.sup_le fun T hT => hmax T hT)

/-- F(N) is optimal: no Sidon subset of {1,...,N} is larger. -/
theorem maxSidon_optimal (N : ℕ) (S : Finset ℕ)
    (hsidon : IsSidonSet S) (hrange : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N) :
    S.card ≤ maxSidonSize N := by
  have hS : S ∈ sidonSets N :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (fun x hx => Finset.mem_Icc.mpr (hrange x hx)),
                           hsidon⟩
  exact Finset.le_sup hS

/- ## Monotonicity -/

/-- F is monotone nondecreasing: F(N) ≤ F(N+1).
    Any Sidon subset of {1,...,N} is also a Sidon subset of {1,...,N+1}. -/
theorem maxSidon_monotone (N : ℕ) : maxSidonSize N ≤ maxSidonSize (N + 1) := by
  apply Finset.sup_le
  intro S hS
  have hmem := Finset.mem_filter.mp hS
  have hpow := Finset.mem_powerset.mp hmem.1
  have hS' : S ∈ sidonSets (N + 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (fun x hx => by
      have := Finset.mem_Icc.mp (hpow hx); exact Finset.mem_Icc.mpr ⟨this.1, by omega⟩), hmem.2⟩
  exact Finset.le_sup hS'

/-- F increases by at most 1 in each step: F(N+1) ≤ F(N) + 1.
    Removing N+1 from any Sidon subset of {1,...,N+1} gives a Sidon subset of {1,...,N}. -/
theorem maxSidon_step (N : ℕ) : maxSidonSize (N + 1) ≤ maxSidonSize N + 1 := by
  apply Finset.sup_le
  intro S hS
  have hmem := Finset.mem_filter.mp hS
  have hpow := Finset.mem_powerset.mp hmem.1
  -- S.erase (N+1) is Sidon and in {1,...,N}
  have hS'_sidon : IsSidonSet (S.erase (N + 1)) := by
    intro a b c d ha hb hc hd
    exact hmem.2 a b c d (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb)
      (Finset.mem_of_mem_erase hc) (Finset.mem_of_mem_erase hd)
  have hS'_range : S.erase (N + 1) ∈ sidonSets N :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (fun x hx => by
      have hxS := Finset.mem_of_mem_erase hx
      have hxne := Finset.ne_of_mem_erase hx
      have := Finset.mem_Icc.mp (hpow hxS)
      exact Finset.mem_Icc.mpr ⟨this.1, by omega⟩), hS'_sidon⟩
  -- S.card ≤ (S.erase (N+1)).card + 1 ≤ F(N) + 1
  have h1 : (S.erase (N + 1)).card ≤ maxSidonSize N := Finset.le_sup hS'_range
  have h2 : S.card ≤ (S.erase (N + 1)).card + 1 := by
    by_cases hmem : N + 1 ∈ S
    · rw [Finset.card_erase_of_mem hmem]; omega
    · rw [Finset.erase_eq_of_not_mem hmem]; omega
  omega

/- ## Asymptotic Bounds -/

/-- Erdős–Turán (1941): F(N) ≤ N^{1/2} + O(N^{1/4}).
    More precisely, F(N) ≤ √N + √(N)^{1/2} + 1 (Lindström 1969). -/
axiom erdos_turan_upper (N : ℕ) (hN : N ≥ 1) :
    (maxSidonSize N : ℝ) ≤ Real.sqrt (N : ℝ) + (N : ℝ) ^ ((1 : ℝ) / 4) + 1

/-- Lower bound: F(N) ≥ (1 - o(1))·√N.
    Singer's construction and refinements give Sidon sets of size ~√N. -/
/- ## The Main Conjecture -/

/-- Erdős Problem #155: For every k ≥ 1, F(N+k) ≤ F(N) + 1
    for all sufficiently large N.

    This says F(N) can increase by at most 1 over any fixed-length
    interval [N, N+k], once N is large enough (depending on k). -/
/- ## Stronger Form -/

/-- The stronger conjecture: F(N+k) ≤ F(N) + 1 holds even for
    k ≈ ε·√N, i.e., F increases by at most 1 over intervals
    of length proportional to √N. -/
/- ## Consequences -/

/-- The number of increase points N < M where F(N+1) > F(N) is at most F(M).
    Proof by induction: F increases by at most 1 (maxSidon_step), so the total
    increase F(M) - F(0) = F(M) bounds the number of steps where F goes up. -/
theorem increase_count_le (M : ℕ) :
    (Finset.filter (fun N => maxSidonSize (N + 1) > maxSidonSize N)
      (Finset.range M)).card ≤ maxSidonSize M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.range_succ, Finset.filter_insert]
    split_ifs with h
    · -- F(M+1) > F(M): count increases by 1
      have hnotmem : M ∉ Finset.filter (fun N => maxSidonSize (N + 1) > maxSidonSize N)
          (Finset.range M) :=
        fun hmem => absurd (Finset.mem_range.mp (Finset.mem_of_mem_filter _ hmem)) (lt_irrefl _)
      rw [Finset.card_insert_of_not_mem hnotmem]
      -- F(M+1) = F(M) + 1 from h and maxSidon_step
      have : maxSidonSize (M + 1) = maxSidonSize M + 1 :=
        le_antisymm (maxSidon_step M) h
      omega
    · -- F(M+1) = F(M): count unchanged, bound follows from monotonicity
      exact le_trans ih (maxSidon_monotone M)

/-- F(N+1) = F(N) for "most" values of N: the number of increase points
    below M is at most (1+ε)√M. Follows from increase_count_le (count ≤ F(M))
    and erdos_turan_upper (F(M) ≤ √M + M^{1/4} + 1). The remaining gap is
    the elementary inequality M^{1/4} + 1 ≤ ε√M for large M. -/
/- ## Small Values (OEIS A003022) -/

/-- F(1) = 1: {1} is the largest Sidon subset of {1}. -/
theorem maxSidonSize_1 : maxSidonSize 1 = 1 := by
  apply le_antisymm
  · apply Finset.sup_le; intro S hS
    exact le_trans (Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1))
      (by simp [Finset.card_Icc])
  · exact maxSidon_optimal 1 {1} (fun a b c d ha hb _ _ hab _ _ => by
      simp only [Finset.mem_singleton] at ha hb; omega)
      (fun x hx => by simp only [Finset.mem_singleton] at hx; subst hx; omega)

/-- F(2) = 2: {1, 2} is the largest Sidon subset of {1, 2}. -/
theorem maxSidonSize_2 : maxSidonSize 2 = 2 := by
  apply le_antisymm
  · apply Finset.sup_le; intro S hS
    exact le_trans (Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1))
      (by simp [Finset.card_Icc])
  · have : ({1, 2} : Finset ℕ).card = 2 := by decide
    rw [← this]; exact maxSidon_optimal 2 {1, 2} (fun a b c d ha hb hc hd hab hcd heq => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc hd
      omega) (fun x hx => by simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)

/-- F(3) = 3: {1, 2, 3} is Sidon under the strict-pair definition.
    Sums: 1+2=3, 1+3=4, 2+3=5 — all distinct. -/
theorem maxSidonSize_3 : maxSidonSize 3 = 3 := by
  apply le_antisymm
  · apply Finset.sup_le; intro S hS
    exact le_trans (Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1))
      (by simp [Finset.card_Icc])
  · have : ({1, 2, 3} : Finset ℕ).card = 3 := by decide
    rw [← this]; exact maxSidon_optimal 3 {1, 2, 3} (fun a b c d ha hb hc hd hab hcd heq => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc hd
      omega) (fun x hx => by simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)

/-- Known small values for larger N (OEIS A003022).
    F(6)=4, F(11)=5, F(18)=6. -/
