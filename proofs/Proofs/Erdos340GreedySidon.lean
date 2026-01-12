/-
Copyright (c) 2026 LeanGenius Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanGenius AI Research
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Order.Filter.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős Problem #340: Greedy Sidon Sequence Growth

## Problem Statement

Let A = {1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, ...} be the greedy Sidon sequence,
constructed by iteratively including the smallest positive integer that preserves
the Sidon property (all pairwise sums are distinct).

**Conjecture**: For all ε > 0, |A ∩ {1,...,N}| ≫ N^(1/2 - ε)

**Best known**: |A ∩ {1,...,N}| ≥ Ω(N^(1/3))

## Current State of Research (as of 2026)

| Construction | Growth Rate | Reference |
|--------------|-------------|-----------|
| Greedy (Mian-Chowla) | N^(1/3) | Trivial bound, unimproved for 80+ years |
| General Sidon | N^(√2-1) ≈ N^0.414 | Ruzsa (1998) |
| Singer construction | (1-o(1))N^(1/2) | Singer (1938), perfect difference sets |
| Random | N^(1/2) whp | Probabilistic argument |
| **Conjecture** | N^(1/2-ε) | Erdős, still OPEN |

**Key Gap**: The greedy sequence is conjectured to grow like N^(1/2-ε) but the best
proven bound is only N^(1/3). The gap between 1/3 and 1/2 is the heart of this problem.

**Why it's hard**: The greedy construction is deterministic but hard to analyze.
Random constructions achieve better bounds but are non-constructive.

## References

- [erdosproblems.com/340](https://www.erdosproblems.com/340)
- OEIS A005282: Mian-Chowla sequence
- Singer (1938): Perfect difference sets give h(N) ≥ (1-o(1))N^(1/2)
- Ruzsa (1998): Explicit Sidon set with N^(√2-1+o(1)) elements
- Cheng (2024): Greedy Sidon sets for linear forms (J. Number Theory)

## Mathematical Background

A **Sidon set** (also called B₂ sequence) is a set A of positive integers such that
all pairwise sums a + b (with a ≤ b, a,b ∈ A) are distinct.

Equivalently: if a + b = c + d with a,b,c,d ∈ A and a ≤ b, c ≤ d, then a = c and b = d.

The **greedy Sidon sequence** starts with 1, then repeatedly adds the smallest positive
integer that maintains the Sidon property.
-/

open Finset Filter Set
open scoped Pointwise

namespace Erdos340

/-! ## Part 1: Sidon Set Definition -/

/-- A finite set A is a Sidon set if all pairwise sums are distinct.
    Equivalently: a + b = c + d with a ≤ b, c ≤ d implies (a,b) = (c,d). -/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/-- Alternative characterization: the sumset A + A has no repeated elements. -/
def IsSidon' (A : Finset ℕ) : Prop :=
  (A + A).card = A.card * (A.card + 1) / 2

/-- Empty set is trivially Sidon. -/
theorem isSidon_empty : IsSidon ∅ := by
  intro a b c d ha
  simp at ha

/-- Singleton is Sidon. -/
theorem isSidon_singleton (n : ℕ) : IsSidon {n} := by
  intro a b c d ha hb hc hd hab hcd heq
  simp at ha hb hc hd
  constructor <;> omega

/-- Pair {a, b} with a < b is Sidon iff 2a ≠ a + b and a + b ≠ 2b
    (which is always true when a ≠ b). -/
theorem isSidon_pair {a b : ℕ} (h : a < b) : IsSidon ({a, b} : Finset ℕ) := by
  intro x y z w hx hy hz hw hxy hzw heq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz hw
  -- Case analysis on which elements x, y, z, w are
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
  rcases hz with rfl | rfl <;> rcases hw with rfl | rfl <;>
  constructor <;> omega

/-! ## Part 2: Basic Sidon Properties -/

/-- Subset of a Sidon set is Sidon. -/
theorem IsSidon.subset {A B : Finset ℕ} (hA : IsSidon A) (hBA : B ⊆ A) : IsSidon B := by
  intro a b c d ha hb hc hd hab hcd heq
  exact hA a b c d (hBA ha) (hBA hb) (hBA hc) (hBA hd) hab hcd heq

/-- Key lemma: In a Sidon set, all pairwise differences are distinct.
    If a - b = c - d with a > b, c > d, then (a,b) = (c,d).

    Proof: a - b = c - d implies a + d = c + b. Rewriting as d + a = b + c,
    the Sidon property on the pairs (d,a) and (b,c) forces d = b and a = c. -/
theorem IsSidon.diff_injective {A : Finset ℕ} (hA : IsSidon A)
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : b < a) (hcd : d < c) (heq : a - b = c - d) : a = c ∧ b = d := by
  -- Key step: a - b = c - d with a > b, c > d implies a + d = c + b
  have h : a + d = c + b := by
    have h1 : a - b + b = a := Nat.sub_add_cancel (le_of_lt hab)
    have h2 : c - d + d = c := Nat.sub_add_cancel (le_of_lt hcd)
    calc a + d = (a - b + b) + d := by rw [h1]
      _ = (a - b) + (b + d) := by rw [Nat.add_assoc]
      _ = (c - d) + (b + d) := by rw [heq]
      _ = (c - d) + (d + b) := by rw [Nat.add_comm b d]
      _ = (c - d + d) + b := by rw [← Nat.add_assoc]
      _ = c + b := by rw [h2]
  -- Rewrite as d + a = b + c to apply Sidon
  have h' : d + a = b + c := by rw [Nat.add_comm d a, Nat.add_comm b c]; exact h
  -- Need d ≤ a and b ≤ c to apply Sidon to (d,a) and (b,c)
  -- Case analysis: if d > a or b > c, we get contradictions
  by_cases hda : d ≤ a
  · by_cases hbc : b ≤ c
    · -- Main case: d ≤ a and b ≤ c
      -- Sidon gives d = b and a = c
      have := hA d a b c hd ha hb hc hda hbc h'
      exact ⟨this.2, this.1.symm⟩
    · -- b > c case: leads to contradiction
      push_neg at hbc
      -- We have b < a, d < c, d ≤ a, c < b
      -- So d < c < b < a, meaning d < b < a and c < b
      -- Apply Sidon to (c, b) and (d, a): c + b = d + a
      have h'' : c + b = d + a := by rw [Nat.add_comm c b]; exact h'.symm
      have := hA c b d a hc hb hd ha (le_of_lt hbc) hda h''
      -- This gives c = d and b = a, but d < c and b < a: contradiction
      omega
  · -- d > a case: leads to contradiction
    push_neg at hda
    -- We have d > a, but also b < a, d < c
    -- Apply Sidon to (a, d) and (b, c) or similar
    by_cases hbc : b ≤ c
    · -- d > a, b ≤ c
      have h'' : a + d = b + c := by rw [Nat.add_comm] at h'; exact h'
      have := hA a d b c ha hd hb hc (le_of_lt hda) hbc h''
      -- This gives a = b and d = c, but b < a: contradiction
      omega
    · push_neg at hbc
      -- d > a, b > c: we have c < b < a and a < d < c, contradiction
      omega

/-! ### Ordered Pairs and Difference Sets -/

/-- The set of ordered pairs (a, b) with a < b from a finset A. -/
def orderedPairsLt (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  A.offDiag.filter (fun p => p.1 < p.2)

/-- The difference function on pairs. -/
def pairDiff : ℕ × ℕ → ℕ := fun p => p.2 - p.1

/-- For a Sidon set, the difference map is injective on ordered pairs. -/
theorem sidon_pairDiff_injective {A : Finset ℕ} (hA : IsSidon A) :
    Set.InjOn pairDiff (orderedPairsLt A : Set (ℕ × ℕ)) := by
  intro ⟨a, b⟩ hab ⟨c, d⟩ hcd heq
  simp only [orderedPairsLt, Finset.coe_filter, Finset.mem_offDiag,
    Set.mem_setOf_eq] at hab hcd
  obtain ⟨⟨ha, hb, _⟩, hlt_ab⟩ := hab
  obtain ⟨⟨hc, hd, _⟩, hlt_cd⟩ := hcd
  simp only [pairDiff] at heq
  -- Use diff_injective: if b - a = d - c with a < b, c < d, then (b, a) = (d, c)
  have := hA.diff_injective hb ha hd hc hlt_ab hlt_cd heq
  ext <;> omega

/-- The difference set of a Sidon set has cardinality equal to the number of ordered pairs. -/
theorem sidon_diffSet_card {A : Finset ℕ} (hA : IsSidon A) :
    (Finset.image pairDiff (orderedPairsLt A)).card = (orderedPairsLt A).card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy heq
  exact sidon_pairDiff_injective hA hx hy heq

/-- Bijection: orderedPairsLt A ↔ powersetCard 2 A -/
theorem orderedPairsLt_card_via_choose (A : Finset ℕ) :
    (orderedPairsLt A).card = A.card.choose 2 := by
  rw [← Finset.card_powersetCard 2 A]
  apply Finset.card_bij (fun p _ => ({p.1, p.2} : Finset ℕ))
  · -- i_mem: (a, b) ∈ orderedPairsLt A → {a, b} ∈ powersetCard 2 A
    intro ⟨a, b⟩ hp
    simp only [orderedPairsLt, Finset.mem_filter, Finset.mem_offDiag] at hp
    obtain ⟨⟨ha, hb, hab⟩, hlt⟩ := hp
    rw [Finset.mem_powersetCard]
    constructor
    · intro x hx
      simp at hx
      rcases hx with rfl | rfl <;> assumption
    · rw [Finset.card_eq_two]
      exact ⟨a, b, ne_of_lt hlt, rfl⟩
  · -- i_inj: different pairs give different 2-subsets
    intro ⟨a, b⟩ hp ⟨c, d⟩ hq heq
    simp only [orderedPairsLt, Finset.mem_filter, Finset.mem_offDiag] at hp hq
    obtain ⟨⟨_, _, _⟩, hlt_ab⟩ := hp
    obtain ⟨⟨_, _, _⟩, hlt_cd⟩ := hq
    have h : a = c ∧ b = d := by
      simp only [Finset.ext_iff, Finset.mem_insert, Finset.mem_singleton] at heq
      have ha_cd : a = c ∨ a = d := by simpa using (heq a).mp (by left; rfl)
      have hb_cd : b = c ∨ b = d := by simpa using (heq b).mp (by right; rfl)
      have hc_ab : c = a ∨ c = b := by simpa using (heq c).mpr (by left; rfl)
      have hd_ab : d = a ∨ d = b := by simpa using (heq d).mpr (by right; rfl)
      omega
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · -- surjective: every 2-element subset comes from some ordered pair
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    obtain ⟨hS_sub, hS_card⟩ := hS
    rw [Finset.card_eq_two] at hS_card
    obtain ⟨a, b, hab, hS_eq⟩ := hS_card
    rcases lt_or_gt_of_ne hab with h | h
    · use (a, b)
      refine ⟨?_, ?_⟩
      · simp only [orderedPairsLt, Finset.mem_filter, Finset.mem_offDiag]
        refine ⟨⟨?_, ?_, ?_⟩, h⟩
        · exact hS_sub (by simp [hS_eq])
        · exact hS_sub (by simp [hS_eq])
        · exact hab
      · exact hS_eq.symm
    · use (b, a)
      refine ⟨?_, ?_⟩
      · simp only [orderedPairsLt, Finset.mem_filter, Finset.mem_offDiag]
        refine ⟨⟨?_, ?_, ?_⟩, h⟩
        · exact hS_sub (by simp [hS_eq])
        · exact hS_sub (by simp [hS_eq])
        · exact hab.symm
      · rw [hS_eq, Finset.pair_comm]

/-- The number of ordered pairs (a, b) with a < b in A is n(n-1)/2. -/
theorem orderedPairsLt_card (A : Finset ℕ) :
    (orderedPairsLt A).card = A.card * (A.card - 1) / 2 := by
  rw [orderedPairsLt_card_via_choose, Nat.choose_two_right]

/-- All differences in a Sidon set are positive and bounded by max - min. -/
theorem sidon_diff_pos_bounded {A : Finset ℕ} (hne : A.Nonempty)
    {p : ℕ × ℕ} (hp : p ∈ orderedPairsLt A) :
    0 < pairDiff p ∧ pairDiff p ≤ A.max' hne - A.min' hne := by
  simp only [orderedPairsLt, Finset.mem_filter, Finset.mem_offDiag] at hp
  obtain ⟨⟨ha, hb, _⟩, hlt⟩ := hp
  constructor
  · simp only [pairDiff]; omega
  · simp only [pairDiff]
    have h1 : p.1 ≥ A.min' hne := Finset.min'_le A p.1 ha
    have h2 : p.2 ≤ A.max' hne := Finset.le_max' A p.2 hb
    omega

/-! ### Difference Set Approach (Aristotle's proof) -/

/-- The set of positive differences between elements of A. -/
def diffSet (A : Finset ℕ) : Finset ℕ :=
  ((A ×ˢ A).filter (fun x => x.2 < x.1)).image (fun x => x.1 - x.2)

/-- The difference set is contained in [1, max A]. -/
lemma diffSet_subset_Icc (A : Finset ℕ) (hne : A.Nonempty) :
    diffSet A ⊆ Finset.Icc 1 (A.max' hne) := by
  intro d hd
  obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ b < a ∧ d = a - b := by
    unfold diffSet at hd; aesop
  exact Finset.mem_Icc.mpr ⟨by omega,
    hab.2.symm ▸ Nat.sub_le_of_le_add (by linarith [Finset.le_max' A a ha, Finset.le_max' A b hb])⟩

/-- The size of the difference set of a Sidon set A is |A|(|A|-1)/2. -/
lemma card_diffSet_eq (A : Finset ℕ) (hA : IsSidon A) :
    (diffSet A).card = A.card * (A.card - 1) / 2 := by
  -- Calculate the size of pairs (a, b) in A where b < a
  have hS_card : ((A ×ˢ A).filter (fun x => x.2 < x.1)).card = A.card * (A.card - 1) / 2 := by
    have hS_card : ((A ×ˢ A).filter (fun x => x.2 < x.1)).card = Finset.card (Finset.powersetCard 2 A) := by
      refine Finset.card_bij (fun x _ => {x.2, x.1}) ?_ ?_ ?_
      · grind
      · simp +contextual [Finset.Subset.antisymm_iff, Finset.subset_iff]; grind
      · intro b hb; rw [Finset.mem_powersetCard] at hb
        rcases Finset.card_eq_two.mp hb.2 with ⟨x, y, hxy⟩
        cases lt_trichotomy x y <;> aesop
    rw [hS_card, Finset.card_powersetCard, Nat.choose_two_right]
  -- Since differences are injective on pairs, image has same cardinality
  have h_inj : ∀ x y : ℕ × ℕ, x ∈ (A ×ˢ A).filter (fun x => x.2 < x.1) →
      y ∈ (A ×ˢ A).filter (fun x => x.2 < x.1) → x.1 - x.2 = y.1 - y.2 → x = y := by
    intros x y hx hy hxy
    have h_eq : x.1 + y.2 = y.1 + x.2 := by
      linarith [Nat.sub_add_cancel (show x.2 ≤ x.1 from le_of_lt (Finset.mem_filter.mp hx).2),
                Nat.sub_add_cancel (show y.2 ≤ y.1 from le_of_lt (Finset.mem_filter.mp hy).2)]
    -- Use Sidon property to conclude pairs are equal
    have h_pair_eq : x.1 = y.1 ∧ y.2 = x.2 ∨ x.1 = x.2 ∧ y.2 = y.1 := by
      have h_pair_eq : ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
          a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d := hA
      contrapose! h_pair_eq; grind
    grind
  rw [← hS_card, show diffSet A = Finset.image (fun x : ℕ × ℕ => x.1 - x.2)
      (Finset.filter (fun x : ℕ × ℕ => x.2 < x.1) (A ×ˢ A)) from rfl,
      Finset.card_image_of_injOn fun x hx y hy hxy => h_inj x y hx hy hxy]

/-- For a Sidon set A with n elements, the largest element is at least n(n-1)/2.

    Proof: There are C(n,2) = n(n-1)/2 distinct positive differences.
    These are distinct positive integers in [1, max(A)].
    By pigeonhole, max(A) ≥ n(n-1)/2. -/
theorem sidon_lower_bound (A : Finset ℕ) (hA : IsSidon A) (hne : A.Nonempty) :
    A.max' hne ≥ A.card * (A.card - 1) / 2 := by
  have h_card_diffSet : (diffSet A).card = A.card * (A.card - 1) / 2 := card_diffSet_eq A hA
  exact h_card_diffSet ▸ le_trans (Finset.card_le_card (diffSet_subset_Icc A hne)) (by simp)

/-- Upper bound: A Sidon subset of {1,...,N} has at most √(2N) + 1 elements.

    Proof: For a Sidon set with n elements, max(A) ≥ n(n-1)/2 by sidon_lower_bound.
    If A ⊆ {1,...,N}, then N ≥ max(A) ≥ n(n-1)/2, so n(n-1) ≤ 2N.
    This gives n ≤ (1 + √(1+8N))/2 < √(2N) + 1.

    Note: The Erdős-Turán bound is actually √N + O(N^{1/4}), which is stronger.
    That requires counting sums rather than differences. -/
theorem sidon_upper_bound_weak (A : Finset ℕ) (hA : IsSidon A) (N : ℕ)
    (hAN : ∀ a ∈ A, a ≤ N) : A.card ≤ Nat.sqrt (2 * N) + 1 := by
  by_cases hempty : A.Nonempty
  · -- Non-empty case: use sidon_lower_bound
    have hmax_bound : A.max' hempty ≤ N := by
      apply Finset.max'_le A hempty
      intro a ha
      exact hAN a ha
    have hcard_bound : A.card * (A.card - 1) / 2 ≤ N :=
      le_trans (sidon_lower_bound A hA hempty) hmax_bound
    -- From n(n-1)/2 ≤ N we prove n ≤ √(2N) + 1
    -- Key insight: if n ≥ √(2N) + 2, then n - 1 ≥ √(2N) + 1 > √(2N)
    -- So (n-1)² > 2N, hence n(n-1) ≥ (n-1)² + (n-1) > 2N, contradicting n(n-1)/2 ≤ N
    by_contra h
    push_neg at h
    have hn : A.card ≥ Nat.sqrt (2 * N) + 2 := h
    have hcard_ge2 : A.card ≥ 2 := by omega
    -- n - 1 ≥ √(2N) + 1 > √(2N), so (n-1)² > 2N
    have h1 := Nat.lt_succ_sqrt (2 * N)
    -- (√(2N)+1)² > 2N by definition of sqrt
    -- Since A.card - 1 ≥ √(2N) + 1, we have (A.card - 1)² ≥ (√(2N)+1)² > 2N
    have hn1_ge : A.card - 1 ≥ Nat.sqrt (2 * N) + 1 := by omega
    have h_sq : (A.card - 1) * (A.card - 1) > 2 * N := by nlinarith
    -- n(n-1) ≥ (n-1)² + (n-1) > 2N (using n ≥ (n-1) + 1)
    have h_prod : A.card * (A.card - 1) > 2 * N := by
      -- We have A.card ≥ 2, so A.card - 1 ≥ 1
      -- A.card * (A.card - 1) ≥ (A.card - 1) * (A.card - 1) + (A.card - 1)
      --                       ≥ (A.card - 1)² + 1 > 2N
      have hge1 : A.card - 1 ≥ 1 := by omega
      -- A.card * (A.card - 1) = (A.card - 1 + 1) * (A.card - 1) = (A.card - 1)² + (A.card - 1)
      have h_eq : A.card * (A.card - 1) = (A.card - 1) * (A.card - 1) + (A.card - 1) := by
        have : A.card = A.card - 1 + 1 := by omega
        nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ A.card)]
      -- (A.card - 1)² > 2N and (A.card - 1) ≥ 1
      linarith
    -- n(n-1) > 2N means n(n-1)/2 > N (since for n(n-1) > 2N, n(n-1)/2 ≥ (2N+1)/2 > N for integer division)
    -- Actually n(n-1)/2 ≥ ⌊n(n-1)/2⌋ and n(n-1) > 2N means n(n-1) ≥ 2N + 1, so n(n-1)/2 ≥ N + 1/2, so ⌊n(n-1)/2⌋ ≥ N
    -- But we need > N, which requires n(n-1) ≥ 2N + 2
    have h_prod2 : A.card * (A.card - 1) ≥ 2 * N + 2 := by
      -- n(n-1) = (n-1)² + (n-1) ≥ (2N+1) + (√(2N)+1) ≥ 2N + 2 for N ≥ 0
      have : A.card - 1 ≥ 1 := by omega
      nlinarith
    have h_div : A.card * (A.card - 1) / 2 ≥ N + 1 := Nat.le_div_iff_mul_le (by omega : 0 < 2) |>.mpr (by omega)
    omega
  · -- Empty set case
    simp only [Finset.not_nonempty_iff_eq_empty] at hempty
    simp [hempty]

/-- The Erdős-Turán upper bound: A Sidon subset of {1,...,N} has ≤ √N + O(N^{1/4}) elements.

    This uses counting sums (not differences) and is the optimal bound up to lower order terms.
    The proof requires showing |A + A| ≤ 2N and |A + A| ≥ n(n+1)/2, giving n ≲ √(4N) = 2√N.
    The actual bound √N + O(N^{1/4}) comes from a more careful analysis. -/
theorem sidon_upper_bound (A : Finset ℕ) (hA : IsSidon A) (N : ℕ)
    (hAN : ∀ a ∈ A, a ≤ N) : A.card ≤ Nat.sqrt N + Nat.sqrt (Nat.sqrt N) + 1 := by
  sorry -- Erdős-Turán bound requires more sophisticated counting

/-! ## Part 3: Greedy Sidon Sequence Construction -/

/-- Check if adding n to A preserves the Sidon property (Prop version). -/
def CanAddProp (A : Finset ℕ) (n : ℕ) : Prop :=
  n ∉ A ∧ IsSidon (A ∪ {n})

/-- The greedy Sidon sequence exists and is unique.
    We axiomatize its values directly for computational efficiency. -/
axiom greedySidonSeq : ℕ → ℕ

/-- The greedy Sidon sequence starts at 1. -/
axiom greedySidonSeq_zero : greedySidonSeq 0 = 1

/-- The greedy Sidon sequence is strictly increasing. -/
axiom greedySidonSeq_strictMono : StrictMono greedySidonSeq

/-- The set of first n+1 terms is always Sidon. -/
axiom greedySidonSeq_isSidon (n : ℕ) :
  IsSidon (Finset.image greedySidonSeq (Finset.range (n + 1)))

/-- The greedy property: greedySidon(n+1) is the smallest value > greedySidon(n)
    that can be added while preserving Sidon. -/
axiom greedySidonSeq_greedy (n : ℕ) :
  ∀ m, greedySidonSeq n < m → m < greedySidonSeq (n + 1) →
    ¬IsSidon (Finset.image greedySidonSeq (Finset.range (n + 1)) ∪ {m})

/-- Alias for compatibility. -/
noncomputable def greedySidon : ℕ → ℕ := greedySidonSeq

/-- The first n+1 elements of the greedy Sidon sequence as a set. -/
noncomputable def greedySidonSet (n : ℕ) : Finset ℕ :=
  Finset.image greedySidon (Finset.range (n + 1))

/-! ## Part 4: Computational Verification -/

-- These would require decidable instances; marking as axioms for now
axiom greedySidon_0 : greedySidon 0 = 1
axiom greedySidon_1 : greedySidon 1 = 2
axiom greedySidon_2 : greedySidon 2 = 4
axiom greedySidon_3 : greedySidon 3 = 8
axiom greedySidon_4 : greedySidon 4 = 13
axiom greedySidon_5 : greedySidon 5 = 21
axiom greedySidon_6 : greedySidon 6 = 31
axiom greedySidon_7 : greedySidon 7 = 45
axiom greedySidon_8 : greedySidon 8 = 66
axiom greedySidon_9 : greedySidon 9 = 81
axiom greedySidon_10 : greedySidon 10 = 97

/-- The greedy Sidon sequence is strictly increasing. -/
theorem greedySidon_strictMono : StrictMono greedySidon :=
  greedySidonSeq_strictMono

/-- The greedy Sidon set is always a Sidon set. -/
theorem greedySidonSet_isSidon (n : ℕ) : IsSidon (greedySidonSet n) :=
  greedySidonSeq_isSidon n

/-! ## Part 5: Growth Rate Bounds -/

/-- Count of greedy Sidon elements up to N. -/
noncomputable def greedySidonCount (N : ℕ) : ℕ :=
  (Set.range greedySidon ∩ Set.Icc 1 N).ncard

/-- **Known Result**: The greedy Sidon sequence grows at least like N^(1/3).

This is the trivial lower bound from the greedy construction. -/
theorem greedySidon_growth_third :
    ∃ C : ℝ, C > 0 ∧ ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1/3 : ℝ) ≤ C * (greedySidonCount N : ℝ) := by
  sorry

/-- **Main Conjecture (Erdős #340)**: For all ε > 0, the growth is at least N^(1/2 - ε).

This is OPEN - the conjecture has not been proven or disproven.

## Potential Research Approaches

1. **Improve the N^(1/3) bound**: Any improvement beyond 1/3 would be publishable.
   The key obstacle is understanding why greedy doesn't "waste" too much space.

2. **Structural analysis**: Study the difference set A - A. If we can show the greedy
   sequence doesn't have unexpectedly many small differences, this could improve bounds.

3. **Probabilistic comparison**: Compare greedy to random. If greedy is "almost random"
   in some sense, we might inherit the N^(1/2) random bound with losses.

4. **Local-to-global**: Prove good behavior on intervals [N, 2N], then glue together.

5. **Density increment**: If |A ∩ [1,N]| < N^α, show this forces structure that allows
   continuing further. Similar to Roth's theorem density increment.

## Intermediate Goals (Formalization Targets)

- [ ] Prove N^(1/3) bound rigorously (known, needs formalization)
- [ ] Formalize Erdős-Turán upper bound: |A| ≤ N^(1/2) + O(N^(1/4))
- [ ] Prove greedy achieves N^(1/3+ε) for some ε > 0 (would be new!)
- [ ] Analyze difference set density
-/
theorem erdos_340 (ε : ℝ) (hε : ε > 0) :
    ∃ C : ℝ, C > 0 ∧ ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ ((1:ℝ)/2 - ε) ≤ C * (greedySidonCount N : ℝ) := by
  sorry

/-! ## Part 6: Difference Set Properties

The difference set A - A plays a key role in understanding Sidon sets.
For a Sidon set, each non-zero difference d = a - b (with a, b ∈ A, a ≠ b)
appears at most once. This means |A - A| = |A|² - |A| + 1.

Understanding which integers appear as differences in the greedy sequence
could provide insights into its growth rate. -/

/-- The difference set A - A of the greedy Sidon sequence. -/
def greedySidonDiffSet : Set ℤ :=
  {d : ℤ | ∃ a b : ℕ, a ∈ Set.range greedySidon ∧ b ∈ Set.range greedySidon ∧ d = a - b}

/-- 22 is in the difference set: 204 - 182 = 22. -/
theorem _22_mem_diffSet : (22 : ℤ) ∈ greedySidonDiffSet := by
  sorry -- Computational verification

/-- Open question: Is 33 in the difference set? -/
theorem _33_mem_diffSet_iff : 33 ∈ greedySidonDiffSet ↔ True := by
  sorry -- Unknown

end Erdos340
