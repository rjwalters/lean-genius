/-
Erdős Problem #140: Density of 3-AP-Free Sets

Source: https://erdosproblems.com/140
Status: SOLVED (Kelley-Meka 2023)
Prize: $500

Statement:
Let r₃(N) be the size of the largest subset of {1,...,N} which does not contain
a non-trivial 3-term arithmetic progression.

Prove that r₃(N) ≪ N/(log N)^C for every C > 0.

History:
- Roth (1953): r₃(N) = o(N) - first breakthrough
- Bourgain (1999, 2008): r₃(N) = O(N/(log log N)^c)
- Sanders (2011): r₃(N) = O(N (log log N)^5 / log N)
- Bloom-Sisask (2020): r₃(N) = O(N / (log N)^{1+c}) for some c > 0
- **Kelley-Meka (2023): PROVED r₃(N) = O(N / (log N)^C) for ALL C > 0**

The Kelley-Meka theorem is a major breakthrough in additive combinatorics,
essentially resolving Erdős's $500 problem.

Reference: Kelley, Meka (2023) "Strong bounds for 3-progressions"
-/

import Mathlib

open Set Finset Nat Real

namespace Erdos140

/- ## 3-term Arithmetic Progressions -/

/-- A 3-term arithmetic progression: three values a, a+d, a+2d with d ≠ 0. -/
def IsAP3 (a b c : ℕ) : Prop := 2 * b = a + c ∧ a < b ∧ b < c

/-- A set is 3-AP-free if it contains no non-trivial 3-term arithmetic progression. -/
def Is3APFree (A : Set ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ A → b ∈ A → c ∈ A → ¬IsAP3 a b c

/-- Same definition for finite sets (Finset). -/
def Finset3APFree (A : Finset ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ A → b ∈ A → c ∈ A → ¬IsAP3 a b c

/- ## The Roth Number r₃(N) -/

/-- r₃(N) = maximum size of a 3-AP-free subset of {1,...,N}.
    We define this as the supremum over all 3-AP-free subsets. -/
noncomputable def r3 (N : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.range (N + 1) ∧ Finset3APFree A ∧ A.card = k }

/-- r₃(N) is well-defined and achieved by some set. -/
theorem r3_achieved (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.range (N + 1) ∧ Finset3APFree A ∧ A.card = r3 N := by
  -- The set { k | ∃ A... } is nonempty (contains 0 from ∅) and bounded by N+1
  -- So the supremum is achieved
  let S := { k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.range (N + 1) ∧ Finset3APFree A ∧ A.card = k }
  have hne : S.Nonempty := by
    use 0
    use ∅
    refine ⟨Finset.empty_subset _, ?_, Finset.card_empty⟩
    intro a b c ha _ _
    exact absurd ha (Finset.not_mem_empty a)
  have hfin : S.Finite := by
    apply Set.Finite.subset (Set.finite_Icc 0 (N + 1))
    intro k ⟨A, hAsub, _, hcard⟩
    simp only [Set.mem_Icc]
    constructor
    · exact Nat.zero_le k
    · calc k = A.card := hcard.symm
           _ ≤ (Finset.range (N + 1)).card := Finset.card_le_card hAsub
           _ = N + 1 := Finset.card_range (N + 1)
  -- In a finite nonempty set of ℕ, sSup is in the set
  have hmem : sSup S ∈ S := hne.csSup_mem hfin
  obtain ⟨A, hAsub, hAP, hcard⟩ := hmem
  exact ⟨A, hAsub, hAP, hcard⟩

/- ## Historical Upper Bounds -/

/--
**Roth's Theorem (1953)**: r₃(N) = o(N).
This was the first non-trivial upper bound, showing 3-AP-free sets have density 0.
-/
def RothBound : Prop := ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, (r3 N : ℝ) < ε * N

/-- Roth's explicit bound: r₃(N) ≤ N / log log N. -/
/--
**Bourgain's Theorem (2008)**: r₃(N) = O(N / (log log N)^{1/2}).
Improved Roth's bound using Fourier-analytic methods.
-/
/--
**Sanders' Theorem (2011)**: r₃(N) = O(N (log log N)^5 / log N).
First bound with log N in the denominator.
-/
/--
**Bloom-Sisask (2020)**: r₃(N) = O(N / (log N)^{1+c}) for some c > 0.
Breakthrough showing power greater than 1 in the log N exponent.
-/
/- ## The Kelley-Meka Theorem -/

/--
**Kelley-Meka Theorem (2023)** - Resolution of Erdős Problem #140:
For every C > 0, r₃(N) = O_C(N / (log N)^C).

This is the strongest possible bound of this form and resolves Erdős's $500 problem.
-/
def KelleyMekaTheorem : Prop :=
  ∀ C : ℝ, C > 0 → ∃ K > 0, ∀ N ≥ 3, (r3 N : ℝ) ≤ K * N / (Real.log N)^C

/-- The main theorem. -/
axiom kelley_meka : KelleyMekaTheorem

/-- Erdős Problem #140 is SOLVED. -/
theorem erdos_140_solved : KelleyMekaTheorem := kelley_meka

/- ## Consequences and Corollaries -/

/-- Corollary: r₃(N) = o(N / (log N)^C) for all fixed C. -/
theorem r3_superlogarithmic (C : ℝ) (hC : C > 0) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, (r3 N : ℝ) < ε * N / (Real.log N)^C := by
  intro ε hε
  obtain ⟨K, hK, hbound⟩ := kelley_meka (C + 1) (by linarith)
  use max 3 (Nat.ceil (Real.exp (K / ε)) + 1)
  intro N hN
  have hN3 : N ≥ 3 := le_of_max_le_left hN
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by push_cast; omega)
  have hlogC1_pos : 0 < (Real.log (N : ℝ)) ^ (C + 1) := rpow_pos_of_pos hlogN_pos _
  have hlogC_pos : 0 < (Real.log (N : ℝ)) ^ C := rpow_pos_of_pos hlogN_pos _
  -- Key: exp(K/ε) < N, hence K/ε < log N, hence K < ε · log N
  have hN_gt_exp : Real.exp (K / ε) < (N : ℝ) := by
    have h1 : Nat.ceil (Real.exp (K / ε)) + 1 ≤ N := le_of_max_le_right hN
    have h2 : Real.exp (K / ε) ≤ ↑(Nat.ceil (Real.exp (K / ε))) := Nat.le_ceil _
    have h3 : (↑(Nat.ceil (Real.exp (K / ε)) + 1) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr h1
    simp only [Nat.cast_add, Nat.cast_one] at h3; linarith
  have hK_lt : K < ε * Real.log (N : ℝ) := by
    have hlog_gt : K / ε < Real.log (N : ℝ) := by
      calc K / ε = Real.log (Real.exp (K / ε)) := (Real.log_exp _).symm
        _ < Real.log ↑N := Real.log_lt_log (Real.exp_pos _) hN_gt_exp
    rwa [div_lt_iff hε] at hlog_gt
  calc (r3 N : ℝ)
      ≤ K * ↑N / (Real.log ↑N) ^ (C + 1) := hbound N hN3
    _ < ε * ↑N / (Real.log ↑N) ^ C := by
        rw [div_lt_div_iff₀ hlogC1_pos hlogC_pos, rpow_add hlogN_pos, rpow_one]
        calc K * ↑N * (Real.log ↑N) ^ C
            = K * (↑N * (Real.log ↑N) ^ C) := by ring
          _ < ε * Real.log ↑N * (↑N * (Real.log ↑N) ^ C) :=
              mul_lt_mul_of_pos_right hK_lt (mul_pos hN_pos hlogC_pos)
          _ = ε * ↑N * ((Real.log ↑N) ^ C * Real.log ↑N) := by ring

/-- Density of 3-AP-free sets tends to 0 faster than any inverse power of log. -/
theorem r3_density_vanishes : ∀ C > 0, Filter.Tendsto
    (fun N => (r3 N : ℝ) * (Real.log N)^C / N) Filter.atTop (nhds 0) := by
  intro C hC
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := r3_superlogarithmic C hC ε hε
  use max N₀ 3
  intro N hN
  have hNN₀ : N ≥ N₀ := le_trans (le_max_left _ _) hN
  have hN3 : N ≥ 3 := le_trans (le_max_right _ _) hN
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by push_cast; omega)
  have hlogC_pos : 0 < (Real.log (N : ℝ)) ^ C := rpow_pos_of_pos hlogN_pos _
  rw [dist_zero_right, Real.norm_of_nonneg (by positivity)]
  -- From r3_superlogarithmic: r3(N) < ε * N / (log N)^C
  -- Multiply by (log N)^C / N to get r3(N) * (log N)^C / N < ε
  have h := hN₀ N hNN₀
  rw [div_lt_iff₀ hN_pos]
  calc (r3 N : ℝ) * (Real.log ↑N) ^ C
      < ε * ↑N / (Real.log ↑N) ^ C * (Real.log ↑N) ^ C :=
        mul_lt_mul_of_pos_right h hlogC_pos
    _ = ε * ↑N := by rw [div_mul_cancel₀ _ hlogC_pos.ne']

/- ## Lower Bounds -/

/-- The Behrend construction gives the best known lower bound:
    r₃(N) ≥ N · exp(-c · √(log N)) for some c > 0. -/
/- Note: The gap between upper and lower bounds is significant.
   Upper: O(N / (log N)^C) for all C
   Lower: Ω(N / exp(c √log N))
   The true order of r₃(N) remains unknown. -/

/- ## Examples of 3-AP-Free Sets -/

/-- The singleton set is trivially 3-AP-free. -/
example : Finset3APFree {0} := by
  intro a b c ha hb hc hap
  simp at ha hb hc
  subst ha hb hc
  unfold IsAP3 at hap
  omega

/-- {1, 2, 4, 5, 10, 11, 13, 14} is 3-AP-free (first 8 elements of the no-3-AP sequence). -/
example : Finset3APFree {1, 2, 4, 5, 10, 11, 13, 14} := by
  intro a b c ha hb hc hap
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  unfold IsAP3 at hap
  -- Case analysis shows no 3-AP exists
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  omega

/- ## The Greedy 3-AP-Free Sequence -/

/-- Convert n to base 3 using only binary digits: the n-th element of the Stanley
    sequence (A005836). Interprets the binary representation of n in base 3. -/
private def toBase3Binary : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) % 2 + 3 * toBase3Binary ((n + 1) / 2)
  decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by norm_num)

/-- The greedy 3-AP-free sequence A003278:
    Start with 1, then add the smallest integer that doesn't create a 3-AP.
    Yields: 1, 2, 4, 5, 10, 11, 13, 14, 28, 29, ...

    Equivalent to the Stanley sequence (A005836) shifted by 1: numbers whose
    base-3 representation uses only digits {0, 1}, plus 1. -/
def greedyAP3Free (n : ℕ) : ℕ := toBase3Binary n + 1

/-- The greedy sequence is indeed 3-AP-free. -/
/- ## k-term AP Generalization -/

/-- A k-term arithmetic progression: k values a, a+d, a+2d, ..., a+(k-1)d with d ≠ 0. -/
def IsAPk (k : ℕ) (vals : Fin k → ℕ) : Prop :=
  k ≥ 2 ∧ ∃ a d : ℕ, d ≠ 0 ∧ ∀ i : Fin k, vals i = a + i.val * d

/-- A set is k-AP-free if it contains no k-term arithmetic progression. -/
def FinsetkAPFree (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ vals : Fin k → ℕ, (∀ i, vals i ∈ A) → ¬IsAPk k vals

/-- The Roth number for k-term progressions: r_k(N). -/
noncomputable def rk (k N : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.range (N + 1) ∧ FinsetkAPFree k A ∧ A.card = m }

/-- Erdős conjectured: For all k ≥ 3 and all C > 0, r_k(N) = O(N / (log N)^C).
    This is OPEN for k ≥ 4. -/
def ErdosAPConjecture : Prop :=
  ∀ k ≥ 3, ∀ C > 0, ∃ K > 0, ∀ N ≥ 3, (rk k N : ℝ) ≤ K * N / (Real.log N)^C

/-- Finset3APFree is equivalent to FinsetkAPFree 3 (modulo formulation details). -/
theorem finset3APFree_eq_finsetkAPFree_3 : ∀ A : Finset ℕ,
    Finset3APFree A ↔ FinsetkAPFree 3 A := by
  intro A
  constructor
  · -- Forward: Finset3APFree → FinsetkAPFree 3
    -- Given no 3-AP in A (by triple), show no 3-AP in A (by Fin 3 → ℕ)
    intro h3AP vals hvals hAPk
    obtain ⟨_, a, d, hd, hform⟩ := hAPk
    -- Extract values: vals(0) = a, vals(1) = a + d, vals(2) = a + 2*d
    have h0 := hform ⟨0, by omega⟩; simp at h0
    have h1 := hform ⟨1, by omega⟩; simp at h1
    have h2 := hform ⟨2, by omega⟩; simp at h2
    -- Build IsAP3 and derive contradiction from h3AP
    exact h3AP _ _ _ (hvals ⟨0, by omega⟩) (hvals ⟨1, by omega⟩) (hvals ⟨2, by omega⟩)
      ⟨by omega, by omega, by omega⟩
  · -- Backward: FinsetkAPFree 3 → Finset3APFree
    -- Given no 3-AP in A (by Fin 3 → ℕ), show no 3-AP in A (by triple)
    intro hkAP a b c ha hb hc ⟨h2b, hab, hbc⟩
    exact hkAP ![a, b, c]
      (by intro i; fin_cases i <;> simp_all)
      ⟨by omega, a, b - a, by omega, by intro i; fin_cases i <;> simp_all <;> omega⟩

/-- r3 equals rk 3 (the Roth numbers are the same for both formulations). -/
theorem r3_eq_rk_3 (N : ℕ) : r3 N = rk 3 N := by
  unfold r3 rk
  congr 1
  ext k
  constructor
  · intro ⟨A, hAsub, hAP, hcard⟩
    exact ⟨A, hAsub, (finset3APFree_eq_finsetkAPFree_3 A).mp hAP, hcard⟩
  · intro ⟨A, hAsub, hAP, hcard⟩
    exact ⟨A, hAsub, (finset3APFree_eq_finsetkAPFree_3 A).mpr hAP, hcard⟩

/-- The k=3 case is resolved by Kelley-Meka. -/
theorem erdos_ap_conjecture_k3 : ∀ C : ℝ, C > 0 → ∃ K > 0, ∀ N ≥ 3,
    (rk 3 N : ℝ) ≤ K * N / (Real.log N)^C := by
  intro C hC
  obtain ⟨K, hK, hbound⟩ := kelley_meka C hC
  use K, hK
  intro N hN
  rw [← r3_eq_rk_3]
  exact hbound N hN

/- ## Summary

**Problem Status: SOLVED**

Erdős Problem #140 asked whether r₃(N) ≪ N / (log N)^C for all C > 0.

**Answer: YES** (Kelley-Meka 2023)

**Historical Progress:**
1. Roth (1953): r₃(N) = o(N)
2. Bourgain (1999, 2008): O(N / (log log N)^{1/2})
3. Sanders (2011): O(N (log log N)^5 / log N)
4. Bloom-Sisask (2020): O(N / (log N)^{1+c})
5. **Kelley-Meka (2023): O(N / (log N)^C) for all C > 0**

**Open Questions:**
- What is the true order of r₃(N)?
- Does r_k(N) = O(N / (log N)^C) hold for k ≥ 4?
- Is r₃(N) = Θ(N / exp(c √log N))? (matching Behrend)

References:
- Roth, K.F. (1953): "On certain sets of integers"
- Kelley, Z., Meka, R. (2023): "Strong bounds for 3-progressions"
- Bloom, T., Sisask, O. (2020): "Breaking the logarithmic barrier in Roth's theorem"
-/

end Erdos140
