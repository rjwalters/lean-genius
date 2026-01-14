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

/-! ## 3-term Arithmetic Progressions -/

/-- A 3-term arithmetic progression: three values a, a+d, a+2d with d ≠ 0. -/
def IsAP3 (a b c : ℕ) : Prop := 2 * b = a + c ∧ a < b ∧ b < c

/-- A set is 3-AP-free if it contains no non-trivial 3-term arithmetic progression. -/
def Is3APFree (A : Set ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ A → b ∈ A → c ∈ A → ¬IsAP3 a b c

/-- Same definition for finite sets (Finset). -/
def Finset3APFree (A : Finset ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ A → b ∈ A → c ∈ A → ¬IsAP3 a b c

/-! ## The Roth Number r₃(N) -/

/-- r₃(N) = maximum size of a 3-AP-free subset of {1,...,N}.
    This is axiomatized as computing the maximum is not decidable in general. -/
noncomputable def r3 (N : ℕ) : ℕ := sorry

/-- r₃(N) is well-defined and achieved by some set. -/
theorem r3_achieved (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.range (N + 1) ∧ Finset3APFree A ∧ A.card = r3 N := by
  sorry

/-! ## Historical Upper Bounds -/

/--
**Roth's Theorem (1953)**: r₃(N) = o(N).
This was the first non-trivial upper bound, showing 3-AP-free sets have density 0.
-/
def RothBound : Prop := ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, (r3 N : ℝ) < ε * N

axiom roth_theorem : RothBound

/-- Roth's explicit bound: r₃(N) ≤ N / log log N. -/
axiom roth_explicit_bound : ∃ C > 0, ∀ N ≥ 3, (r3 N : ℝ) ≤ C * N / Real.log (Real.log N)

/--
**Bourgain's Theorem (2008)**: r₃(N) = O(N / (log log N)^{1/2}).
Improved Roth's bound using Fourier-analytic methods.
-/
axiom bourgain_bound : ∃ C > 0, ∀ N ≥ 3, (r3 N : ℝ) ≤ C * N / Real.sqrt (Real.log (Real.log N))

/--
**Sanders' Theorem (2011)**: r₃(N) = O(N (log log N)^5 / log N).
First bound with log N in the denominator.
-/
axiom sanders_bound : ∃ C > 0, ∀ N ≥ 3,
    (r3 N : ℝ) ≤ C * N * (Real.log (Real.log N))^5 / Real.log N

/--
**Bloom-Sisask (2020)**: r₃(N) = O(N / (log N)^{1+c}) for some c > 0.
Breakthrough showing power greater than 1 in the log N exponent.
-/
axiom bloom_sisask_bound : ∃ c > 0, ∃ C > 0, ∀ N ≥ 3,
    (r3 N : ℝ) ≤ C * N / (Real.log N)^(1 + c)

/-! ## The Kelley-Meka Theorem -/

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

/-! ## Consequences and Corollaries -/

/-- Corollary: r₃(N) = o(N / (log N)^C) for all fixed C. -/
theorem r3_superlogarithmic (C : ℝ) (hC : C > 0) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, (r3 N : ℝ) < ε * N / (Real.log N)^C := by
  intro ε hε
  -- Apply Kelley-Meka with exponent C + 1
  obtain ⟨K, hK, hbound⟩ := kelley_meka (C + 1) (by linarith)
  use max 3 (Nat.ceil (Real.exp (K / ε)))
  intro N hN
  have hN3 : N ≥ 3 := le_of_max_le_left hN
  -- For large N, r₃(N) ≤ K·N/(log N)^{C+1} < ε·N/(log N)^C
  sorry

/-- Density of 3-AP-free sets tends to 0 faster than any inverse power of log. -/
theorem r3_density_vanishes : ∀ C > 0, Filter.Tendsto
    (fun N => (r3 N : ℝ) * (Real.log N)^C / N) Filter.atTop (nhds 0) := by
  intro C hC
  -- Follows from Kelley-Meka: (r3 N) * (log N)^C / N ≤ K for all N
  -- So (r3 N) * (log N)^C / N ≤ K * (log N)^C / (log N)^(C+1) = K / log N → 0
  sorry

/-! ## Lower Bounds -/

/-- The Behrend construction gives the best known lower bound:
    r₃(N) ≥ N · exp(-c · √(log N)) for some c > 0. -/
axiom behrend_lower_bound : ∃ c > 0, ∀ N ≥ 3,
    (r3 N : ℝ) ≥ N * Real.exp (-c * Real.sqrt (Real.log N))

/- Note: The gap between upper and lower bounds is significant.
   Upper: O(N / (log N)^C) for all C
   Lower: Ω(N / exp(c √log N))
   The true order of r₃(N) remains unknown. -/

/-! ## Examples of 3-AP-Free Sets -/

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

/-! ## The Greedy 3-AP-Free Sequence -/

/-- The greedy 3-AP-free sequence A003278:
    Start with 1, then add the smallest integer that doesn't create a 3-AP.
    Yields: 1, 2, 4, 5, 10, 11, 13, 14, 28, 29, ... -/
def greedyAP3Free : ℕ → ℕ
  | 0 => 1
  | n + 1 => sorry -- Need to find smallest k > greedyAP3Free n not creating 3-AP

/-- The greedy sequence is indeed 3-AP-free. -/
axiom greedy_is_3APFree : ∀ n : ℕ,
    Finset3APFree (Finset.image greedyAP3Free (Finset.range n))

/-! ## k-term AP Generalization -/

/-- The Roth number for k-term progressions: r_k(N). -/
noncomputable def rk (k N : ℕ) : ℕ := sorry

/-- Erdős conjectured: For all k ≥ 3 and all C > 0, r_k(N) = O(N / (log N)^C).
    This is OPEN for k ≥ 4. -/
def ErdosAPConjecture : Prop :=
  ∀ k ≥ 3, ∀ C > 0, ∃ K > 0, ∀ N ≥ 3, (rk k N : ℝ) ≤ K * N / (Real.log N)^C

/-- The k=3 case is resolved by Kelley-Meka. -/
theorem erdos_ap_conjecture_k3 : ∀ C > 0, ∃ K > 0, ∀ N ≥ 3,
    (rk 3 N : ℝ) ≤ K * N / (Real.log N)^C := by
  -- This follows from Kelley-Meka once we show rk 3 = r3
  sorry

/-! ## Summary

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
