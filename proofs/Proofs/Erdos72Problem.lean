/-
  Erdős Problem #72: Unavoidable Cycle Lengths

  Source: https://erdosproblems.com/72
  Status: SOLVED (affirmatively)
  Prize: $100

  Statement:
  Is there a set A ⊂ ℕ of density 0 and a constant c > 0 such that every
  graph on sufficiently many vertices with average degree ≥ c contains
  a cycle whose length is in A?

  Answer: YES

  Key Results:
  - Bollobás (1977): Works for infinite arithmetic progressions with even numbers
  - Verstraëte (2005): Non-constructive existence proof
  - Liu & Montgomery (2020): Powers of 2 work (contradicting Erdős's intuition)

  References:
  [Bo77] Bollobás, "Cycles modulo k" (1977)
  [Ve05] Verstraëte, "Unavoidable cycle lengths" (2005)
  [LM20] Liu-Montgomery, "A proof of the Erdős-Hajnal conjecture on cycle lengths" (2020)

  Tags: graph-theory, extremal-combinatorics, cycles, density
-/

import Mathlib

namespace Erdos72

open SimpleGraph Finset Filter Topology
open scoped Classical

/- ## Part I: Density of Sets of Natural Numbers -/

/-- The counting function for a set A up to n. -/
noncomputable def countingFunction (A : Set ℕ) (n : ℕ) : ℕ :=
  (Finset.filter (· ∈ A) (Finset.range (n + 1))).card

/-- A set A ⊂ ℕ has density 0 if |A ∩ [1,n]|/n → 0 as n → ∞. -/
def hasDensityZero (A : Set ℕ) : Prop :=
  Tendsto (fun n : ℕ => (countingFunction A n : ℝ) / n) atTop (nhds 0)

/-- Powers of 2 form a set of density 0. -/
def powersOfTwo : Set ℕ := {n | ∃ k : ℕ, n = 2 ^ k}

/-- Powers of 2 have density 0 (only log₂(n) elements up to n). -/
theorem powersOfTwo_density_zero : hasDensityZero powersOfTwo := by
  -- Step 1: the count up to `n` is at most `Nat.log 2 n + 1`, via the injection
  -- `2 ^ k ↦ Nat.log 2 (2 ^ k) = k` into `range (Nat.log 2 n + 1)`.
  have hcount : ∀ n, countingFunction powersOfTwo n ≤ Nat.log 2 n + 1 := by
    intro n
    have hle : (Finset.filter (· ∈ powersOfTwo) (Finset.range (n + 1))).card
        ≤ (Finset.range (Nat.log 2 n + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun m => Nat.log 2 m)
      · intro m hm
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hm
        obtain ⟨hmn, k, rfl⟩ := hm
        simp only [Finset.coe_range, Set.mem_Iio]
        rw [Nat.log_pow (by norm_num)]
        have h2k : 2 ^ k ≤ n := Nat.lt_succ_iff.mp hmn
        calc k = Nat.log 2 (2 ^ k) := (Nat.log_pow (by norm_num) k).symm
          _ ≤ Nat.log 2 n := Nat.log_mono_right h2k
          _ < Nat.log 2 n + 1 := Nat.lt_succ_self _
      · intro a ha b hb hab
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at ha hb
        obtain ⟨_, ka, rfl⟩ := ha
        obtain ⟨_, kb, rfl⟩ := hb
        simp only at hab
        rw [Nat.log_pow (by norm_num), Nat.log_pow (by norm_num)] at hab
        rw [hab]
    simpa [countingFunction] using hle
  -- Step 2: the majorant `(Real.logb 2 n + 1) / n` tends to 0.
  have hmaj : Tendsto (fun n : ℕ => (Real.logb 2 n + 1) / n) atTop (𝓝 0) := by
    have hreal : Tendsto (fun x : ℝ => (Real.logb 2 x + 1) / x) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => Real.logb 2 x / x) atTop (𝓝 0) := by
        have := Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 1 one_ne_zero
        simpa using this
      have h2 : Tendsto (fun x : ℝ => (1 : ℝ) / x) atTop (𝓝 0) :=
        (tendsto_const_nhds).div_atTop tendsto_id
      have hadd := h1.add h2
      simp only [add_zero] at hadd
      refine hadd.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [add_div]
    exact hreal.comp tendsto_natCast_atTop_atTop
  -- Step 3: squeeze 0 ≤ count / n ≤ majorant.
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) hmaj
  have hnum : (countingFunction powersOfTwo n : ℝ) ≤ Real.logb 2 n + 1 := by
    have hb := Real.natLog_le_logb n 2
    norm_num at hb
    calc (countingFunction powersOfTwo n : ℝ)
        ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) := by exact_mod_cast hcount n
      _ = (Nat.log 2 n : ℝ) + 1 := by push_cast; ring
      _ ≤ Real.logb 2 n + 1 := by linarith
  gcongr

/-- An arithmetic progression with common difference d starting at a. -/
def arithmeticProgression (a d : ℕ) : Set ℕ := {n | ∃ k : ℕ, n = a + k * d}

/-- Arithmetic progressions have positive density, not 0. -/
theorem arithmeticProgression_positive_density (a d : ℕ) (hd : d > 0) :
    ¬hasDensityZero (arithmeticProgression a d) := by
  intro h
  -- Nat lower bound: for `n ≥ a` the count is at least `(n - a) / d + 1`, via the
  -- injection `k ↦ a + k * d` of `range ((n - a) / d + 1)` into the counted set.
  have hcount : ∀ n, a ≤ n →
      (n - a) / d + 1 ≤ countingFunction (arithmeticProgression a d) n := by
    intro n han
    have hle : (Finset.range ((n - a) / d + 1)).card
        ≤ (Finset.filter (· ∈ arithmeticProgression a d) (Finset.range (n + 1))).card := by
      apply Finset.card_le_card_of_injOn (fun k => a + k * d)
      · intro k hk
        simp only [Finset.coe_range, Set.mem_Iio] at hk
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range]
        refine ⟨?_, k, rfl⟩
        have hkle : k ≤ (n - a) / d := Nat.lt_succ_iff.mp hk
        have h1 : k * d ≤ (n - a) / d * d := Nat.mul_le_mul_right d hkle
        have h2 : (n - a) / d * d ≤ n - a := Nat.div_mul_le_self (n - a) d
        omega
      · intro x _ y _ hxy
        simp only at hxy
        have hxyd : x * d = y * d := by omega
        exact Nat.eq_of_mul_eq_mul_right hd hxyd
    simpa [countingFunction] using hle
  -- The lower-bound density `L n = ((n:ℝ) - a) / (d * n)` tends to `1 / d > 0`.
  have hL : Tendsto (fun n : ℕ => ((n : ℝ) - a) / (d * n)) atTop (𝓝 (1 / d)) := by
    have e1 : Tendsto (fun n : ℕ => (a : ℝ) / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (a : ℝ)
    have e2 : Tendsto (fun n : ℕ => (1 - (a : ℝ) / n) * (1 / d)) atTop
        (𝓝 ((1 - 0) * (1 / d))) :=
      (tendsto_const_nhds.sub e1).mul tendsto_const_nhds
    simp only [sub_zero, one_mul] at e2
    refine e2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  -- Eventually `L n ≤ count n / n`, so the assumed limit 0 would force `1 / d ≤ 0`.
  have hev : (fun n : ℕ => ((n : ℝ) - a) / (d * n))
      ≤ᶠ[atTop] (fun n : ℕ => (countingFunction (arithmeticProgression a d) n : ℝ) / n) := by
    filter_upwards [eventually_ge_atTop a, eventually_gt_atTop 0] with n han hn0
    have hc := hcount n han
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    set C := countingFunction (arithmeticProgression a d) n
    have step1 : (n - a) / d * d + d ≤ C * d := by
      calc (n - a) / d * d + d = ((n - a) / d + 1) * d := by ring
        _ ≤ C * d := Nat.mul_le_mul_right d hc
    have step2 : n - a < (n - a) / d * d + d := by
      have hdm := Nat.div_add_mod (n - a) d
      have hmod := Nat.mod_lt (n - a) hd
      nlinarith [hdm, hmod, Nat.mul_comm d ((n - a) / d)]
    have hnat : n - a < C * d := lt_of_lt_of_le step2 step1
    have hreal : (n : ℝ) - a ≤ (C : ℝ) * d := by
      have hcast : ((n - a : ℕ) : ℝ) ≤ ((C * d : ℕ) : ℝ) := by exact_mod_cast le_of_lt hnat
      rw [Nat.cast_sub han] at hcast
      push_cast at hcast
      linarith
    rw [← div_div]
    gcongr
    rw [div_le_iff₀ hd']
    exact hreal
  have hcontra := le_of_tendsto_of_tendsto hL h hev
  have hpos : (0 : ℝ) < 1 / d := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  linarith

/- ## Part II: Graph Definitions -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The average degree of a finite simple graph. -/
noncomputable def averageDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  (∑ v : V, G.degree v : ℝ) / Fintype.card V

/-- A graph has average degree at least c. -/
def hasAverageDegreeAtLeast (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) : Prop :=
  averageDegree G ≥ c

/-- The set of cycle lengths that appear in a graph. -/
def cycleLengths (G : SimpleGraph V) : Set ℕ :=
  {k | ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ p.length = k}

/-- A graph contains a cycle of length in the set A. -/
def containsCycleIn (G : SimpleGraph V) (A : Set ℕ) : Prop :=
  ∃ k ∈ A, k ∈ cycleLengths G

/- ## Part III: The Unavoidable Cycle Length Property -/

/-- A set A ⊂ ℕ is unavoidable with threshold c if every sufficiently large graph
    with average degree ≥ c contains a cycle whose length is in A. -/
def isUnavoidable (A : Set ℕ) (c : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V],
    Fintype.card V ≥ n₀ →
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      hasAverageDegreeAtLeast G c → containsCycleIn G A

/-- A set A ⊂ ℕ is strongly unavoidable if there exists some threshold c. -/
def isStronglyUnavoidable (A : Set ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ isUnavoidable A c

/- ## Part IV: The Main Problem -/

/-- **Erdős Problem #72 (Affirmative Solution)**

    There exists a set A ⊂ ℕ of density 0 that is strongly unavoidable.
    That is, there exists c > 0 such that every sufficiently large graph
    with average degree ≥ c contains a cycle whose length is in A.
-/
def Erdos72Statement : Prop :=
  ∃ A : Set ℕ, hasDensityZero A ∧ isStronglyUnavoidable A

/- ## Part V: Known Results (Axiomatized) -/

/- **Bollobás (1977)**

    If A is an infinite arithmetic progression containing even numbers,
    then A is strongly unavoidable.

    Note: Arithmetic progressions have positive density, so this doesn't
    directly solve the problem, but shows the cycle-forcing phenomenon.
-/
/- **Verstraëte (2005)**

    Non-constructively proved that Erdős Problem #72 has an affirmative answer.
    Some density-0 set A exists with the required property.
-/
/-- **Liu-Montgomery (2020)**

    The set of powers of 2 is strongly unavoidable.
    This was surprising as Erdős believed powers of 2 would NOT work.
-/
axiom liu_montgomery_powers_of_two : isStronglyUnavoidable powersOfTwo

/-- Combining Liu-Montgomery with the density result gives the main theorem. -/
theorem erdos_72_solved : Erdos72Statement := by
  use powersOfTwo
  exact ⟨powersOfTwo_density_zero, liu_montgomery_powers_of_two⟩

/- ## Part VI: Erdős's Incorrect Conjecture -/

/-- Erdős believed that for powers of 2, no constant threshold would work,
    but rather the required average degree would grow with graph size.
    Liu-Montgomery proved this wrong. -/
def erdos_incorrect_belief : Prop :=
  ¬isStronglyUnavoidable powersOfTwo

/-- Liu-Montgomery refuted Erdős's belief. -/
theorem erdos_was_wrong : ¬erdos_incorrect_belief :=
  fun h => h liu_montgomery_powers_of_two

/- ## Part VII: Other Density-0 Sets -/

/-- Perfect squares. -/
def perfectSquares : Set ℕ := {n | ∃ k : ℕ, n = k ^ 2}

/-- Perfect squares have density 0. -/
theorem perfectSquares_density_zero : hasDensityZero perfectSquares := by
  -- Step 1: the count up to `n` is at most `Nat.sqrt n + 1`, via the injection
  -- `k ^ 2 ↦ Nat.sqrt (k ^ 2) = k` into `range (Nat.sqrt n + 1)`.
  have hcount : ∀ n, countingFunction perfectSquares n ≤ Nat.sqrt n + 1 := by
    intro n
    have hle : (Finset.filter (· ∈ perfectSquares) (Finset.range (n + 1))).card
        ≤ (Finset.range (Nat.sqrt n + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun m => Nat.sqrt m)
      · intro m hm
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hm
        obtain ⟨hmn, k, rfl⟩ := hm
        simp only [Finset.coe_range, Set.mem_Iio]
        rw [Nat.sqrt_eq']
        have hkn : k ^ 2 ≤ n := Nat.lt_succ_iff.mp hmn
        calc k = Nat.sqrt (k ^ 2) := (Nat.sqrt_eq' k).symm
          _ ≤ Nat.sqrt n := Nat.sqrt_le_sqrt hkn
          _ < Nat.sqrt n + 1 := Nat.lt_succ_self _
      · intro a ha b hb hab
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at ha hb
        obtain ⟨_, ka, rfl⟩ := ha
        obtain ⟨_, kb, rfl⟩ := hb
        simp only at hab
        rw [Nat.sqrt_eq', Nat.sqrt_eq'] at hab
        rw [hab]
    simpa [countingFunction] using hle
  -- Step 2: the majorant `(Real.sqrt n + 1) / n = n^(-1/2) + 1/n` tends to 0.
  have hmaj : Tendsto (fun n : ℕ => (Real.sqrt n + 1) / n) atTop (𝓝 0) := by
    have hreal : Tendsto (fun x : ℝ => (Real.sqrt x + 1) / x) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => Real.sqrt x / x) atTop (𝓝 0) := by
        have hr := tendsto_rpow_neg_atTop (y := (1 / 2 : ℝ)) (by norm_num)
        refine hr.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        have key : Real.sqrt x / x = x ^ (-(1 / 2) : ℝ) := by
          rw [Real.sqrt_eq_rpow]
          nth_rw 2 [← Real.rpow_one x]
          rw [← Real.rpow_sub hx]
          norm_num
        rw [key]
      have h2 : Tendsto (fun x : ℝ => (1 : ℝ) / x) atTop (𝓝 0) :=
        (tendsto_const_nhds).div_atTop tendsto_id
      have hadd := h1.add h2
      simp only [add_zero] at hadd
      refine hadd.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [add_div]
    exact hreal.comp tendsto_natCast_atTop_atTop
  -- Step 3: squeeze 0 ≤ count / n ≤ majorant.
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) hmaj
  have hnum : (countingFunction perfectSquares n : ℝ) ≤ Real.sqrt n + 1 := by
    calc (countingFunction perfectSquares n : ℝ)
        ≤ ((Nat.sqrt n + 1 : ℕ) : ℝ) := by exact_mod_cast hcount n
      _ = (Nat.sqrt n : ℝ) + 1 := by push_cast; ring
      _ ≤ Real.sqrt n + 1 := by linarith [Real.nat_sqrt_le_real_sqrt (a := n)]
  gcongr

/-- It remains unknown whether perfect squares are strongly unavoidable. -/
def openQuestion_squares : Prop := isStronglyUnavoidable perfectSquares

/-- Even numbers of the form 2^k (subset of powers of 2, all even). -/
theorem powersOfTwo_all_even (n : ℕ) (hn : n ∈ powersOfTwo) (hn_pos : n > 0) :
    Even n ∨ n = 1 := by
  obtain ⟨k, rfl⟩ := hn
  cases k with
  | zero => right; rfl
  | succ k => left; exact ⟨2^k, by ring⟩

/- ## Part VIII: Quantitative Bounds -/

/-- The optimal threshold for a set A. -/
noncomputable def optimalThreshold (A : Set ℕ) : ℝ :=
  sInf {c : ℝ | c > 0 ∧ isUnavoidable A c}

/- Liu-Montgomery gives some explicit bound for powers of 2. -/
/-- Finding the exact optimal threshold for powers of 2 remains open. -/
def openQuestion_optimal_threshold : Prop :=
  ∃ c : ℝ, optimalThreshold powersOfTwo = c ∧ c < 100

/- ## Part IX: Generalizations -/

/-- A set A with controlled growth: |A ∩ [1,n]| ≤ f(n) for slow-growing f. -/
def hasControlledGrowth (A : Set ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, countingFunction A n ≤ f n

/- Liu-Montgomery actually proves a more general result for sets with
    logarithmic growth of even numbers. -/
end Erdos72

/-
## Summary

This file formalizes Erdős Problem #72 on unavoidable cycle lengths.

**The Problem**: Does there exist a density-0 set A ⊂ ℕ and constant c > 0
such that every large graph with average degree ≥ c contains a cycle
whose length is in A?

**Answer**: YES (solved affirmatively)

**Key Results**:
1. Bollobás (1977): Arithmetic progressions with even numbers work
2. Verstraëte (2005): Non-constructive existence proof
3. Liu-Montgomery (2020): Powers of 2 work (contradicting Erdős's belief)

**What We Formalize**:
1. Density 0 for sets of natural numbers
2. Average degree and cycle lengths in graphs
3. The unavoidability property
4. Main theorem statement and solution
5. Key results as axioms

**Erdős's Error**: Erdős believed powers of 2 would NOT work and that
the required average degree would grow with graph size. Liu-Montgomery
proved a constant threshold suffices.

**Open Questions**:
- Optimal threshold for powers of 2?
- Do perfect squares work?
- Algorithmic implications?
-/
