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
    a + b (a ≤ b, a, b ∈ S) are distinct. Equivalently, all pairwise
    differences are distinct. -/
def IsSidonSet (S : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

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
axiom sidon_lower_asymptotic :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (maxSidonSize N : ℝ) ≥ (1 - ε) * Real.sqrt (N : ℝ)

/- ## The Main Conjecture -/

/-- Erdős Problem #155: For every k ≥ 1, F(N+k) ≤ F(N) + 1
    for all sufficiently large N.

    This says F(N) can increase by at most 1 over any fixed-length
    interval [N, N+k], once N is large enough (depending on k). -/
axiom erdos_155_conjecture (k : ℕ) (hk : k ≥ 1) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → maxSidonSize (N + k) ≤ maxSidonSize N + 1

/- ## Stronger Form -/

/-- The stronger conjecture: F(N+k) ≤ F(N) + 1 holds even for
    k ≈ ε·√N, i.e., F increases by at most 1 over intervals
    of length proportional to √N. -/
axiom erdos_155_strong (ε : ℝ) (hε : ε > 0) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      maxSidonSize (N + Nat.floor (ε * Real.sqrt (N : ℝ))) ≤ maxSidonSize N + 1

/- ## Consequences -/

/-- If the conjecture holds, then F(N+1) = F(N) for "most" values of N:
    the set of N where F increases has density 0. -/
axiom increase_points_sparse :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ M : ℕ, M ≥ N₀ →
      (Finset.card (Finset.filter
        (fun N => maxSidonSize (N + 1) > maxSidonSize N)
        (Finset.range M)) : ℝ) ≤ (1 + ε) * Real.sqrt (M : ℝ)

/- ## Small Values (OEIS A003022) -/

/-- Known small values of F(N):
    F(1)=1, F(2)=2, F(3)=3, F(4)=3, F(5)=3, F(6)=4,
    F(11)=5, F(18)=6, F(26)=7. -/
axiom small_values :
    maxSidonSize 1 = 1 ∧ maxSidonSize 2 = 2 ∧ maxSidonSize 3 = 3 ∧
    maxSidonSize 6 = 4 ∧ maxSidonSize 11 = 5 ∧ maxSidonSize 18 = 6
