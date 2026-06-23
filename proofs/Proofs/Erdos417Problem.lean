/-
Erdős Problem #417: Counting Totient Values

Source: https://erdosproblems.com/417
Status: OPEN

Statement:
Define:
- V'(x) = |{φ(m) : 1 ≤ m ≤ x}| (distinct totient values from inputs ≤ x)
- V(x) = |{n ≤ x : n ∈ range(φ)}| (totient values that are ≤ x)

Does the limit V(x)/V'(x) exist? Is it > 1? Erdős conjectured it may be ∞.

Key Observations:
- V'(x) ≤ V(x) trivially (every totient ≤ x from m ≤ x is a totient ≤ x)
- V'(x) counts with multiplicity constraint (only from small inputs)
- V(x) counts all totients ≤ x regardless of input size
- The ratio measures "density" of totient values vs their appearances

Example:
- φ(1) = 1, φ(2) = 1, φ(3) = 2, φ(4) = 2, φ(5) = 4, φ(6) = 2
- For x = 6: V'(6) = |{1,2,4}| = 3
- For x = 4: V(4) includes 1,2,4 (all totients), so V(4) ≥ 3

References:
- Erdős [Er79e]
- Erdős, Graham [ErGr80]
- Erdős [Er98] (conjectured infinite limit)
- OEIS A264810, A061070
- Related: Problem #416

Copyright 2025 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import Mathlib

open Nat Set Filter Finset

namespace Erdos417

/- ## Part I: Basic Definitions -/

/--
**V'(x): Distinct Totient Values from Small Inputs**

Count of distinct values in {φ(m) : 1 ≤ m ≤ x}.
This is the number of different totient values achieved by inputs up to x.
-/
noncomputable def V' (x : ℕ) : ℕ :=
  (Finset.image totient (Finset.range (x + 1))).card

/--
**The Range of Euler's Totient Function**

A natural number n is a totient value if n = φ(m) for some m.
Not every number is a totient: for instance, no n with φ(m) = 2k+1 > 1.
-/
def IsTotientValue (n : ℕ) : Prop :=
  ∃ m : ℕ, m > 0 ∧ totient m = n

/--
**V(x): Totient Values Up to x**

Count of integers n ≤ x that are in the range of φ.
This counts all totient values ≤ x, regardless of input size.
-/
noncomputable def V (x : ℕ) : ℕ :=
  (Finset.filter (fun n => ∃ m, totient m = n) (Finset.range (x + 1))).card

/- ## Part II: Basic Properties -/

/-- V'(x) ≤ V(x): every distinct totient from inputs ≤ x is a totient value ≤ x.

    Proof: If n = φ(m) for some m ≤ x, then n ≤ m ≤ x (by totient_le) and
    n is a totient value (witnessed by m). -/
theorem V'_le_V (x : ℕ) : V' x ≤ V x := by
  unfold V' V
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_image] at hn
  obtain ⟨m, hm, rfl⟩ := hn
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr (lt_of_le_of_lt (totient_le m) (Finset.mem_range.mp hm)),
    m, rfl⟩

/-- 1 is always a totient value (φ(1) = 1, φ(2) = 1). -/
theorem one_is_totient_value : IsTotientValue 1 := by
  use 1
  simp [totient]

/-- 2 is a totient value (φ(3) = 2, φ(4) = 2, φ(6) = 2). -/
theorem two_is_totient_value : IsTotientValue 2 := by
  use 3
  constructor
  · omega
  · native_decide

/-- Odd numbers > 1 are not totient values.

    Proof: For m > 2, φ(m) is even (Nat.totient_even). For m ∈ {1,2},
    φ(m) = 1. So no odd n > 1 is a totient value. -/
theorem odd_gt_one_not_totient (n : ℕ) (hn : n > 1) (hodd : Odd n) :
    ¬IsTotientValue n := by
  intro ⟨m, hm_pos, hm_eq⟩
  by_cases hm2 : m ≤ 2
  · -- m ∈ {1, 2}: φ(m) = 1 but n > 1
    have : m = 1 ∨ m = 2 := by omega
    rcases this with rfl | rfl
    · rw [totient_one] at hm_eq; omega
    · rw [totient_prime prime_two] at hm_eq; omega
  · -- m > 2: φ(m) is even, contradicts odd n
    push_neg at hm2
    have heven := totient_even hm2
    rw [← hm_eq] at heven
    obtain ⟨k₁, hk₁⟩ := heven
    obtain ⟨k₂, hk₂⟩ := hodd
    omega

/-- V' is monotone non-decreasing. -/
theorem V'_mono {x y : ℕ} (h : x ≤ y) : V' x ≤ V' y := by
  unfold V'
  exact Finset.card_le_card (Finset.image_subset_image (Finset.range_mono (by omega)))

/-- V is monotone non-decreasing. -/
theorem V_mono {x y : ℕ} (h : x ≤ y) : V x ≤ V y := by
  unfold V
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))

/-- 0 is not a totient value (φ(m) ≥ 1 for all m ≥ 1). -/
theorem zero_not_totient_value : ¬IsTotientValue 0 := by
  intro ⟨m, hm, heq⟩
  have := Nat.totient_pos hm
  omega

/-- 4 is a totient value: φ(5) = 4. -/
theorem four_is_totient_value : IsTotientValue 4 := by
  use 5
  constructor
  · omega
  · native_decide

/-- V'(x) ≥ 1 for x ≥ 1: since φ(1) = 1, the value 1 is always in the image. -/
theorem V'_pos (x : ℕ) (hx : x ≥ 1) : V' x ≥ 1 := by
  unfold V'
  have h1 : 1 ∈ Finset.image totient (Finset.range (x + 1)) := by
    rw [Finset.mem_image]
    exact ⟨1, Finset.mem_range.mpr (by omega), totient_one⟩
  exact Finset.card_pos.mpr ⟨1, h1⟩

/-- V(x) ≥ 1 for x ≥ 1: since φ(1) = 1 ≤ x, the value 1 is counted. -/
theorem V_pos (x : ℕ) (hx : x ≥ 1) : V x ≥ 1 := by
  unfold V
  have h1 : 1 ∈ Finset.filter (fun n => ∃ m, totient m = n) (Finset.range (x + 1)) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (by omega), 1, totient_one⟩
  exact Finset.card_pos.mpr ⟨1, h1⟩

/- ## Part III: The Main Questions -/

/--
**Erdős Problem #417, Question 1 (OPEN)**

Does the limit V(x)/V'(x) exist as x → ∞?
-/
def erdos417LimitExists : Prop :=
  ∃ L : ℝ, Tendsto (fun x : ℕ => (V x : ℝ) / V' x) atTop (nhds L)

/--
**Erdős Problem #417, Question 2 (OPEN)**

Is V(x)/V'(x) > 1 for large x? (It's trivially ≥ 1)
-/
def erdos417RatioGtOne : Prop :=
  ∀ᶠ x in atTop, (V x : ℝ) / V' x > 1

/--
**Erdős's Conjecture (OPEN)**

Erdős conjectured in [Er98] that V(x)/V'(x) → ∞.
-/
def erdos417ConjectureInfinite : Prop :=
  Tendsto (fun x : ℕ => (V x : ℝ) / V' x) atTop atTop

-- NOTE: erdos417LimitExists (finite limit) is INCONSISTENT with
-- erdos417ConjectureInfinite (limit = ∞). If V(x)/V'(x) → ∞, then
-- no finite L exists with V(x)/V'(x) → L. The original problem asks
-- "does the limit exist?" as a question, not an assertion. We keep
-- only Erdős's conjecture (ratio → ∞) as the axiom.

axiom erdos_417_conjecture : erdos417ConjectureInfinite

/-- The ratio V(x)/V'(x) > 1 for large x follows from the conjecture:
    if V(x)/V'(x) → ∞, it is eventually > 1 (indeed eventually > any bound). -/
theorem erdos_417_ratio_gt_one : erdos417RatioGtOne :=
  (Filter.tendsto_atTop.mp erdos_417_conjecture 2).mono (fun _ hx => by linarith)

/- ## Part IV: Intuition for the Conjecture -/

/--
**Why V(x) Might Be Much Larger Than V'(x)**

V'(x) only counts totients from small inputs (m ≤ x).
V(x) counts ALL totients ≤ x, including those from large m.

For large m, φ(m) can be quite small (e.g., φ(2^k) = 2^(k-1)).
So there are many totients ≤ x coming from m > x.

Example: 2^10 = 1024, but φ(2^10) = 512. So 512 ∈ V(600) but 512 ∉ V'(600).
-/

/- ## Part V: Connection to Problem #416 -/

/--
**Problem #416**

Problem #416 asks about the structure of the totient range more directly.
Both problems concern understanding which integers appear as totient values.
-/

/- ## Part VI: Totient Value Structure -/

/-- Every power of 2 (≥ 1) is a totient value: φ(2^(k+1)) = 2^k. -/
theorem pow_two_totient_value (k : ℕ) : IsTotientValue (2^k) := by
  use 2^(k+1)
  constructor
  · exact Nat.pos_pow_of_pos (k+1) (by norm_num)
  · rw [Nat.totient_prime_pow_succ Nat.prime_two]
    ring

/-- For prime p, p-1 is a totient value: φ(p) = p-1. -/
theorem prime_pred_totient_value (p : ℕ) (hp : p.Prime) : IsTotientValue (p - 1) := by
  use p
  exact ⟨hp.pos, totient_prime hp⟩

/-- Euler's totient is either 0 (m=0), 1 (m=1,2), or even (m≥3).
    This structural constraint limits V(x) to counting at most 0, 1, and even numbers. -/
theorem totient_zero_one_or_even (m : ℕ) :
    totient m = 0 ∨ totient m = 1 ∨ Even (totient m) := by
  rcases le_or_lt m 2 with hm | hm
  · interval_cases m
    · left; decide
    · right; left; exact totient_one
    · right; left; rw [totient_prime Nat.prime_two]
  · right; right; exact totient_even (by omega)

/-- All elements counted by V are 0, 1, or even. This gives V(x) ≤ ⌊x/2⌋ + 2. -/
theorem V_element_structure (n x : ℕ)
    (hn : n ∈ Finset.filter (fun n => ∃ m, totient m = n) (Finset.range (x + 1))) :
    n = 0 ∨ n = 1 ∨ Even n := by
  rw [Finset.mem_filter] at hn
  obtain ⟨_, m, hm⟩ := hn
  have := totient_zero_one_or_even m
  rwa [hm] at this

/-- p-1 is even for primes p ≥ 3 (used for totient value structure). -/
theorem prime_sub_one_even (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ p) : Even (p - 1) := by
  have hodd := hp.odd_of_ne_two (by omega)
  obtain ⟨k, hk⟩ := hodd
  exact ⟨k, by omega⟩

/- ## Part VII: Asymptotic Estimates -/

/--
**Asymptotic Behavior**

Known: V(x) ~ cx/log(x) for some constant c (density of totient values).
V'(x) also grows roughly like x/log(x), but the constants may differ.
The question is whether their ratio has a limit and what it is.
-/

/- ## Part VIII: Why This Is Hard -/

/--
**The Challenge**

Understanding V(x)/V'(x) requires knowing:
1. The "efficiency" of small inputs at producing totient values
2. How many totients ≤ x come from inputs > x
3. The multiplicative structure of totient values

The conjecture V(x)/V'(x) → ∞ suggests that most totients ≤ x
come from large inputs, making V(x) much larger than V'(x).
-/

/- ## Part IX: Summary -/

/--
**Erdős Problem #417: Summary**

**Question 1:** Does lim V(x)/V'(x) exist?
**Question 2:** Is V(x)/V'(x) > 1 for large x?
**Conjecture:** V(x)/V'(x) → ∞

**Status:** OPEN

**Key Concepts:**
- V'(x) = distinct totients from inputs ≤ x
- V(x) = all totients ≤ x
- V'(x) ≤ V(x) trivially

**Related:**
- Problem #416
- OEIS A264810, A061070
- Totient value characterization
-/
theorem erdos_417_summary :
    -- The trivial inequality
    ∀ x, V' x ≤ V x := V'_le_V

/-- The three open questions bundled together. -/
def erdos_417_open_questions : Prop :=
  erdos417LimitExists ∧ erdos417RatioGtOne ∧ erdos417ConjectureInfinite

end Erdos417
