/-
  Erdős Problem #1: Distinct Subset Sums

  Source: https://erdosproblems.com/1
  Status: OPEN ($500 prize)

  Statement:
  If A ⊆ {1,...,N} with |A| = n and all 2^n subset sums are distinct,
  must N ≥ c · 2^n for some absolute constant c > 0?

  The basic counting bound gives N ≥ (2^n - 1)/n. The full conjecture
  (with constant c > 0 independent of n) is open.

  Known bounds:
  - Lower: N ≥ √(2/π) · 2^n / √n (Dubroff-Fox-Xu 2021)
  - Upper: minimum N ≤ 0.22009 · 2^n (Conway-Guy 1968)
  - Exact values (OEIS A005318): f(1)=1, f(2)=2, f(3)=4, f(4)=7, f(5)=13

  NOTE: A previous version of this file (proved by Aristotle) had two bugs:
  1. hasDistinctSubsetSums was trivially False: it required injectivity
     of S ↦ (S.filter (· ∈ A)).sum id on ALL Finsets, but {0} and ∅
     always give the same filtered sum (both map to ∅.sum = 0).
     This made all theorems vacuously true.
  2. The theorem claimed N ≥ 2^(n-1), which is mathematically FALSE
     for n ≥ 4. Counterexample: {3,5,6,7} has 4 elements, all 16
     subset sums distinct, and max = 7 < 8 = 2^3.
     (See OEIS A005318: f(4) = 7.)
  Both issues are fixed in this version.
-/

import Mathlib

open Finset

/-- A finite set of natural numbers has distinct subset sums if distinct
    subsets always have different sums. -/
def hasDistinctSubsetSums (A : Finset ℕ) : Prop :=
  ∀ (S T : Finset ℕ), S ⊆ A → T ⊆ A → S.sum id = T.sum id → S = T

/-- Sidon-like spacing: distinct subsets of A have distinct sums. -/
theorem subset_sums_spacing {A : Finset ℕ}
    (hDistinct : hasDistinctSubsetSums A)
    (S T : Finset ℕ) (hS : S ⊆ A) (hT : T ⊆ A) (hST : S ≠ T) :
    S.sum id ≠ T.sum id :=
  fun heq => hST (hDistinct S T hS hT heq)

/-- Erdős Problem #1 (counting bound): If A ⊆ {1,...,N} has n elements
    with distinct subset sums, then n·N + 1 ≥ 2^n.

    Proof: The 2^n subsets of A have distinct sums, each in [0, n·N].
    By pigeonhole, 2^n values fit into n·N + 1 slots. -/
theorem erdos_1_counting_bound {A : Finset ℕ} {N : ℕ}
    (hA : ∀ a ∈ A, a ≤ N)
    (hDistinct : hasDistinctSubsetSums A) :
    2 ^ A.card ≤ A.card * N + 1 := by
  -- The sum function is injective on powerset(A)
  have hinj : Set.InjOn (fun (S : Finset ℕ) => S.sum id) (↑A.powerset : Set (Finset ℕ)) := by
    intro S hS T hT heq
    rw [Finset.mem_coe, Finset.mem_powerset] at hS hT
    exact hDistinct S T hS hT heq
  -- Image of the injective map has the same cardinality
  have himg_card : (A.powerset.image (fun S => S.sum id)).card = 2 ^ A.card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_powerset]
  -- Each sum is in [0, |A|*N], so image ⊆ range(|A|*N + 1)
  have himg_sub : A.powerset.image (fun S => S.sum id) ⊆ Finset.range (A.card * N + 1) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨S, hSmem, rfl⟩ := hx
    rw [Finset.mem_powerset] at hSmem
    rw [Finset.mem_range]
    suffices S.sum id ≤ A.card * N by omega
    calc S.sum id
      ≤ S.sum (fun _ => N) :=
          Finset.sum_le_sum (fun a ha => hA a (hSmem ha))
      _ = S.card * N := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ A.card * N :=
          Nat.mul_le_mul_right N (Finset.card_le_card hSmem)
  -- Combine: 2^n = |image| ≤ |range| = n*N + 1
  calc 2 ^ A.card
    = (A.powerset.image (fun S => S.sum id)).card := himg_card.symm
    _ ≤ (Finset.range (A.card * N + 1)).card := Finset.card_le_card himg_sub
    _ = A.card * N + 1 := Finset.card_range _

/-- Corollary: N ≥ (2^n - 1)/n for n ≥ 1. -/
theorem erdos_1_lower_bound {A : Finset ℕ} {N : ℕ}
    (hA : ∀ a ∈ A, a ≤ N)
    (hA_card : A.card ≥ 1)
    (hDistinct : hasDistinctSubsetSums A) :
    N ≥ (2 ^ A.card - 1) / A.card := by
  have hcount := erdos_1_counting_bound hA hDistinct
  -- hcount : 2^n ≤ n*N + 1; need (2^n - 1)/n ≤ N
  -- In ℕ: 2^n ≤ n*N + 1 implies 2^n - 1 ≤ n*N (omega), then use div monotonicity
  have hcard_pos : 0 < A.card := hA_card
  have h1 : 2 ^ A.card - 1 ≤ A.card * N := by omega
  calc (2 ^ A.card - 1) / A.card
      ≤ A.card * N / A.card := Nat.div_le_div_right h1
    _ = N := Nat.mul_div_cancel_left N hcard_pos

/-- The Erdős $500 conjecture: there exists an absolute constant c > 0
    such that any set with n elements and distinct subset sums has
    maximum element ≥ c · 2^n.

    Status: OPEN. Best lower bound: N ≥ Ω(2^n / √n) (Dubroff-Fox-Xu 2021).
    Best upper bound on minimum N: 0.22009 · 2^n (Conway-Guy 1968). -/
def erdos_1_conjecture : Prop :=
  ∃ c : ℚ, c > 0 ∧ ∀ (A : Finset ℕ) (N : ℕ),
    (∀ a ∈ A, a ≤ N) →
    (∀ a ∈ A, 0 < a) →
    hasDistinctSubsetSums A →
    (c * 2 ^ A.card : ℚ) ≤ N

/-
## Summary

**Problem Status: OPEN ($500 prize)**

Erdős Problem #1 asks whether a set of n positive integers with
distinct subset sums must have maximum element ≥ c · 2^n for some
absolute constant c > 0.

**Theorems (3)**:
- erdos_1_counting_bound: 2^n ≤ n·N + 1 (pigeonhole on subset sums)
- erdos_1_lower_bound: N ≥ (2^n - 1)/n (corollary)
- subset_sums_spacing: S ≠ T ⊆ A → sum(S) ≠ sum(T)

**Axioms (0)**, **Sorries (0)**

**Definitions (2)**:
- hasDistinctSubsetSums: ∀ S T ⊆ A, sum(S) = sum(T) → S = T
- erdos_1_conjecture: ∃ c > 0, ∀ A with DSS, max(A) ≥ c · 2^|A|

**Bug fixes from previous version (Aristotle-proved)**:
1. DEFINITION BUG: hasDistinctSubsetSums was trivially False. The old
   definition `Function.Injective (fun S => S.filter (· ∈ A) |>.sum id)`
   required injectivity on ALL Finset ℕ, not just subsets of A. Since
   {0} and ∅ always give the same filtered sum, the predicate was never
   satisfiable, making all theorems vacuously true.
2. FALSE CLAIM: The old theorem stated N ≥ 2^(n-1). This is false for
   n ≥ 4: the set {3,5,6,7} has 4 elements, 16 distinct subset sums,
   and max = 7 < 8 = 2^3. (OEIS A005318 confirms f(4) = 7.)
   The correct bound is N ≥ (2^n - 1)/n.

References:
- Erdős (1955): Problems and results in additive number theory
- Conway, Guy (1968): Upper bound construction
- Lunnon (1988): Exact values for small n
- Dubroff, Fox, Xu (2021): Best known lower bound N ≥ √(2/π) · 2^n / √n
-/
