/-
  Aristotle targets for Erdős Problem #179 (AP Supersaturation)
  Routine supporting lemmas for automated proof search.
  See Erdos179Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main supersaturation function F (which has sorry in its existence proof)
  - Does NOT depend on F, Question1, Question2, or related problematic definitions
  - Pure analytical lemmas (asymptotic comparisons) and combinatorial facts
  - Clean theorem statements with no definition sorries
  - No axiom declarations

  Key Aristotle targets:
  - rpow_eventually_gt_const_mul_log: y^c > C * log y eventually (asymptotic)
  - exp_rpow_gt_rpow_of_gt_mul_log: helper for improvement_significant
  - improvement_significant: exp((log log N)^c) > (log log N)^C eventually
  - all_pairs_are_2APs: every 2-element subset of A is a 2-AP
-/
import Mathlib

open Real Filter Finset

namespace Erdos179Aristotle

/-
## Section 1: Arithmetic Progressions — Combinatorial Helpers

A k-term arithmetic progression is {a, a+d, ..., a+(k-1)d} for d > 0.
-/

/-- A k-AP with first term a and common difference d. -/
def arithmeticProgression (a d k : ℕ) : Finset ℕ :=
  Finset.image (fun i => a + i * d) (Finset.range k)

/-- A 2-AP is a 2-element set {a, a+d}. -/
theorem arithmeticProgression_two (a d : ℕ) (hd : d > 0) :
    (arithmeticProgression a d 2).card = 2 := by
  simp [arithmeticProgression]
  omega

/-- A 2-AP {a, a+d} contains a and a+d. -/
theorem mem_arithmeticProgression_two (a d : ℕ) :
    a ∈ arithmeticProgression a d 2 ∧ a + d ∈ arithmeticProgression a d 2 := by
  simp [arithmeticProgression]

/-- For any two distinct naturals a < b, {a, b} = arithmeticProgression a (b-a) 2. -/
theorem pair_is_2AP (a b : ℕ) (hab : a < b) :
    ({a, b} : Finset ℕ) = arithmeticProgression a (b - a) 2 := by
  simp [arithmeticProgression, Finset.ext_iff]
  omega

/-- In a 2-AP, the two elements are distinct. -/
theorem two_AP_distinct (a d : ℕ) (hd : d > 0) :
    a ≠ a + d := by omega

/-
## Section 2: Counting 2-APs

Every pair of distinct naturals forms a 2-AP.
So any set of size N has exactly C(N,2) two-term APs.
-/

/-- Count of k-APs in A: number of k-element subsets that form a k-AP. -/
noncomputable def countAPs (A : Finset ℕ) (k : ℕ) : ℕ :=
  (A.powerset.filter fun S => ∃ a d, d > 0 ∧ S = arithmeticProgression a d k).card

/-- Every 2-element Finset of naturals {a, b} with a < b is a 2-AP. -/
theorem pair_subset_is_2AP (A : Finset ℕ) (S : Finset ℕ) (hS : S ⊆ A)
    (hcard : S.card = 2) :
    ∃ a d : ℕ, d > 0 ∧ S = arithmeticProgression a d 2 := by
  rw [Finset.card_eq_two] at hcard
  obtain ⟨a, b, hab, rfl⟩ := hcard
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · exact ⟨a, b - a, by omega, by simp [arithmeticProgression, Finset.ext_iff]; omega⟩
  · exact ⟨b, a - b, by omega, by simp [arithmeticProgression, Finset.ext_iff]; omega⟩

/-- Any set A has exactly C(|A|, 2) two-term arithmetic progressions.
    (Every pair of distinct elements forms a 2-AP.) -/
theorem all_pairs_are_2APs (A : Finset ℕ) :
    countAPs A 2 = A.card.choose 2 := by
  sorry

/-
## Section 3: Asymptotic Analysis Helpers

Supporting lemmas for improvement_significant.
The key comparison: for c > 0, exp(y^c) grows much faster than y^C.
-/

/-- For any C > 0 and c > 0, x^c / log x → ∞ as x → ∞. -/
theorem rpow_div_log_tendsto_atTop (c : ℝ) (hc : c > 0) :
    Filter.Tendsto (fun x : ℝ => x ^ c / Real.log x) Filter.atTop Filter.atTop := by
  sorry

/-- For c, C > 0, eventually x^c > C * log x (x : ℝ, x → ∞). -/
theorem rpow_eventually_gt_const_mul_log (c C : ℝ) (hc : c > 0) (hC : C > 0) :
    ∀ᶠ x in (Filter.atTop : Filter ℝ), x ^ c > C * Real.log x := by
  have h := rpow_div_log_tendsto_atTop c hc
  rw [Filter.tendsto_atTop_atTop] at h
  obtain ⟨N, hN⟩ := h (C + 1)
  apply Filter.eventually_atTop.mpr
  use max N 1
  intro x hx
  have hx1 : x ≥ N := le_trans (le_max_left N 1) hx
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) (le_max_right N 1 |>.trans hx)
  have hlog : Real.log x > 0 := Real.log_pos (by linarith)
  have h1 := hN x hx1
  rw [ge_iff_le, ← div_le_iff hlog] at h1
  linarith

/-- If y > 0, y^c > C * log y, then exp(y^c) > y^C. -/
theorem exp_rpow_gt_rpow_of_gt_mul_log (y C c : ℝ) (hy : y > 1)
    (h : y ^ c > C * Real.log y) :
    Real.exp (y ^ c) > y ^ C := by
  rw [Real.rpow_def_of_pos (by linarith)]
  apply Real.exp_lt_exp.mpr
  linarith

/-
## Section 4: The Main Comparison Theorem
-/

/-- For any C, c > 0, exp((log(log N))^c) > (log(log N))^C for large N : ℝ. -/
theorem improvement_significant_real (C c : ℝ) (hC : C > 0) (hc : c > 0) :
    ∀ᶠ N in (Filter.atTop : Filter ℝ),
      Real.exp ((Real.log (Real.log N)) ^ c) > (Real.log (Real.log N)) ^ C := by
  sorry

/-- For any C, c > 0, exp((log(log N))^c) > (log(log N))^C for large N : ℕ. -/
theorem improvement_significant (C c : ℝ) (hC : C > 0) (hc : c > 0) :
    ∀ᶠ N in (Filter.atTop : Filter ℕ),
      Real.exp ((Real.log (Real.log N)) ^ c) > (Real.log (Real.log N)) ^ C := by
  sorry

/-
## Section 5: Logarithmic Upper Bound Helpers

The sorry inside question1_solved:
  N^2 / (log log N)^C ≤ ε * N^2   [for large N]
  ⟺ (log log N)^C ≥ 1/ε             [for large N]
-/

/-- For C > 0, (log(log N))^C → ∞ as N → ∞ (N : ℝ). -/
theorem loglog_rpow_tendsto_atTop (C : ℝ) (hC : C > 0) :
    Filter.Tendsto (fun N : ℝ => (Real.log (Real.log N)) ^ C)
      Filter.atTop Filter.atTop := by
  sorry

/-- For C > 0 and any M, eventually (log log N)^C ≥ M. -/
theorem loglog_rpow_eventually_large (C M : ℝ) (hC : C > 0) :
    ∀ᶠ N in (Filter.atTop : Filter ℝ), (Real.log (Real.log N)) ^ C ≥ M := by
  sorry

/-- For ε > 0 and C > 0: N^2 / (log log N)^C ≤ ε * N^2 for large N. -/
theorem div_loglog_rpow_le (ε C : ℝ) (hε : ε > 0) (hC : C > 0) :
    ∀ᶠ N in (Filter.atTop : Filter ℝ),
      N ^ 2 / (Real.log (Real.log N)) ^ C ≤ ε * N ^ 2 := by
  sorry

end Erdos179Aristotle
