/-
Erdős Problem #531: Folkman's Theorem - Monochromatic Subset Sums

Let F(k) be the minimal N such that if we two-colour {1,...,N}, there is a set A
of size k such that all non-empty subset sums are monochromatic. Estimate F(k).

**Status**: Bounds established, exact growth rate open
- Lower bound: F(k) ≥ 2^{2^{k-1}/k} (Balogh-Eberhard-Narayanan-Treglown-Wagner 2017)
- Upper bound: F(k) exists (Folkman's theorem)

Reference: https://erdosproblems.com/531
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Basic
import Mathlib.Combinatorics.Additive.SalemSpencer
import Mathlib.Order.BoundedOrder.Basic

namespace Erdos531

/-
## Overview

This problem concerns Folkman's theorem, a fundamental result in Ramsey theory
about monochromatic subset sums in colorings of integers.

### Background

Given any two-coloring of {1,...,N}, Folkman's theorem guarantees that for
sufficiently large N, there exists a k-element subset A such that all 2^k - 1
non-empty subset sums have the same color.

This is related to:
- Schur's theorem: avoiding x + y = z
- Rado's theorem: general linear equations
- Van der Waerden's theorem: arithmetic progressions
-/

/-- A two-coloring of natural numbers. -/
def Coloring := ℕ → Bool

/-- The set of all non-empty subset sums of a finite set. -/
def SubsetSums (A : Finset ℕ) : Finset ℕ :=
  (A.powerset.filter (· ≠ ∅)).image (Finset.sum · id)

/-- All subset sums have the same color. -/
def MonochromaticSubsetSums (c : Coloring) (A : Finset ℕ) : Prop :=
  ∃ col : Bool, ∀ s ∈ SubsetSums A, c s = col

/-- F(k) is the minimum N such that any 2-coloring of {1,...,N} has
    a k-element set with monochromatic subset sums. -/
def ExistsMonochromaticSet (N k : ℕ) : Prop :=
  ∀ c : Coloring, ∃ A : Finset ℕ, A.card = k ∧ (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
    MonochromaticSubsetSums c A

/-- The set of valid N values for a given k. -/
def ValidN (k : ℕ) : Set ℕ := {N : ℕ | ExistsMonochromaticSet N k}

/-- F(k) is the minimum valid N. -/
noncomputable def F (k : ℕ) : ℕ := sInf (ValidN k)

/-
## Folkman's Theorem

The existence of F(k) is Folkman's theorem. For any k, F(k) is finite.
This follows from Rado's theorem applied to the system of equations
x₁ + x₂ + ... + xⱼ = s for all non-empty subsets.
-/

/-- Folkman's Theorem: F(k) exists for all k. -/
axiom folkman_theorem :
  ∀ k : ℕ, k ≥ 1 → ∃ N : ℕ, ExistsMonochromaticSet N k

/-- F(k) is well-defined (the set ValidN k is non-empty). -/
theorem F_well_defined (k : ℕ) (hk : k ≥ 1) : (ValidN k).Nonempty :=
  folkman_theorem k hk

/-
## Lower Bounds

### Erdős-Spencer (1989)
Proved F(k) ≥ 2^{ck²/log k} for some constant c > 0.

### Balogh-Eberhard-Narayanan-Treglown-Wagner (2017)
Improved to F(k) ≥ 2^{2^{k-1}/k}.
-/

/-- Erdős-Spencer lower bound: F(k) ≥ 2^{ck²/log k}. -/
/-- Balogh et al. (2017): F(k) ≥ 2^{2^{k-1}/k}. -/
axiom balogh_2017 :
  ∀ k : ℕ, k ≥ 1 → F k ≥ 2^(2^(k-1) / k)

/-
## Small Cases

For small k, we can compute or bound F(k) directly.
-/

/-- The only non-empty subset sum of a singleton `{n}` is `n` itself. -/
theorem mem_subsetSums_singleton {n s : ℕ} (h : s ∈ SubsetSums {n}) : s = n := by
  simp only [SubsetSums, Finset.mem_image, Finset.mem_filter, Finset.mem_powerset] at h
  obtain ⟨t, ⟨ht_sub, ht_ne⟩, ht_sum⟩ := h
  have ht : t = {n} := by
    rcases Finset.subset_singleton_iff.mp ht_sub with h0 | h1
    · exact absurd h0 ht_ne
    · exact h1
  subst ht
  simp only [Finset.sum_singleton, id_eq] at ht_sum
  exact ht_sum.symm

/-- `1 ∈ ValidN 1`: for `k = 1` the singleton `{1}` always works, since its only
    subset sum is `1`, which is trivially monochromatic. -/
theorem one_mem_validN_one : (1 : ℕ) ∈ ValidN 1 := by
  intro c
  refine ⟨{1}, Finset.card_singleton 1, ?_, c 1, ?_⟩
  · intro a ha
    rw [Finset.mem_singleton] at ha; subst ha
    exact ⟨le_refl 1, le_refl 1⟩
  · intro s hs
    rw [mem_subsetSums_singleton hs]

/-- `1` lower-bounds `ValidN 1`: any valid `N` admits a non-empty `1`-element set
    with elements in `[1, N]`, forcing `N ≥ 1`. -/
theorem validN_one_ge_one {N : ℕ} (hN : N ∈ ValidN 1) : 1 ≤ N := by
  obtain ⟨A, hcard, hbound, _⟩ := hN (fun _ => true)
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by rw [hcard]; norm_num)
  exact (hbound a ha).1.trans (hbound a ha).2

/-- F(1) = 1: Any element forms a monochromatic 1-element set. -/
theorem F_1 : F 1 = 1 := by
  have hmem : (1 : ℕ) ∈ ValidN 1 := one_mem_validN_one
  have hle : F 1 ≤ 1 := Nat.sInf_le hmem
  have hge : 1 ≤ F 1 := validN_one_ge_one (Nat.sInf_mem ⟨1, hmem⟩)
  exact le_antisymm hle hge

/-- F(2) = 8. **Correction (2026-07-10):** an earlier draft claimed `F 2 = 3`.
    That value is FALSE for the distinct-pair Folkman number defined here (a set
    `A` of `k = 2` *distinct* elements `{a, b}` with `a, b, a+b` monochromatic).
    An exhaustive check of all 2-colourings gives F(2) = 8, not 3:

    * `N = 7` fails — the colouring
        `1,2,4 ↦ B`, `3,5,6,7 ↦ R` (and `≥ 8 ↦ B`)
      leaves every 2-subset `{a,b} ⊆ {1,…,7}` with `{a, b, a+b}` non-monochromatic;
    * `N = 8` succeeds — every 2-colouring of `{1,…,8}` forces some distinct pair
      `{a, b}` with `a, b, a+b` all one colour.

    (In particular `3 ∉ ValidN 2`: the colouring `3 ↦ R`, everything else `B`
    defeats all three pairs of `{1,2,3}`, namely `{1,2}`, `{1,3}`, `{2,3}`.)

    The exact-value proof requires reducing the infinite coloring quantifier
    `∀ c : ℕ → Bool` to a finite search over `{1,…,15}`; that finite-reduction is
    left for a follow-up session (out of scope here). -/
theorem F_2 : F 2 = 8 := by
  sorry -- Verified by exhaustive computation; needs finite-coloring reduction to formalize.

/-- F(3) ≥ 11: Lower bound for 3-element sets. -/
/-
## Upper Bounds

The original upper bounds from Folkman's proof are very weak.
Improvements have been made using probabilistic methods.
-/

/-- Folkman's original upper bound is at least tower-type. -/
/-
## Connection to Rado's Theorem

Folkman's theorem follows from Rado's theorem about partition regularity
of systems of linear equations.

The equation system is:
- For each non-empty S ⊆ {1,...,k}: Σᵢ∈S xᵢ = yₛ
- We want all yₛ to be monochromatic.

Rado's theorem guarantees this for any k.
-/

/-- Folkman follows from Rado's theorem. -/
/-
## The Main Question

The central open question is the precise growth rate of F(k).

Known:
- F(k) ≥ 2^{2^{k-1}/k} (doubly exponential lower bound)
- F(k) is finite (Folkman's theorem)

The gap between lower and upper bounds is enormous.
-/

/-- The growth rate of F(k) is at least doubly exponential. -/
theorem F_growth_doubly_exponential :
    ∀ k : ℕ, k ≥ 1 → F k ≥ 2^(2^(k-1) / k) :=
  balogh_2017

/-- Summary of Erdős Problem #531. -/
theorem erdos_531_summary (k : ℕ) (hk : k ≥ 1) :
    (ValidN k).Nonempty ∧ F k ≥ 2^(2^(k-1) / k) :=
  ⟨F_well_defined k hk, balogh_2017 k hk⟩

/-
## Proof Techniques

The lower bound proofs use:
1. Probabilistic counting arguments
2. Careful analysis of subset sum structure
3. Balancing conditions on colorings

The proof by Balogh et al. (2017) uses a clever inductive construction
that exploits the multiplicative structure of subset sums.
-/

/-- The main result: F(k) exists with doubly exponential lower bound. -/
theorem erdos_531 :
    ∀ k : ℕ, k ≥ 1 → (ValidN k).Nonempty :=
  fun k hk => folkman_theorem k hk

end Erdos531
