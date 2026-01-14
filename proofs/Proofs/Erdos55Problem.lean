/-
  Erdős Problem #55: Ramsey r-Complete Sets

  Source: https://erdosproblems.com/55
  Status: SOLVED (Conlon-Fox-Pham 2021)
  Prize: $250

  Statement:
  A set of integers A is Ramsey r-complete if, whenever A is r-coloured,
  all sufficiently large integers can be written as a monochromatic sum
  of elements of A. Prove any non-trivial bounds about the growth rate
  of such an A for r > 2.

  History:
  - Burr-Erdős (1985): For r=2, showed c(log N)² ≤ |A ∩ [1,N]| ≤ C(log N)³
  - Burr: The k-th powers are Ramsey r-complete for every r,k ≥ 1
  - Conlon-Fox-Pham (2021): SOLVED - optimal growth is Θ(r(log N)²)

  The solution shows:
  - Upper bound: ∃ r-Ramsey complete A with |A ∩ [1,N]| ≪ r(log N)²
  - Lower bound: If |A ∩ [1,N]| ≤ cr(log N)² for all large N, then A is
    not r-Ramsey complete (for some universal c > 0)

  This file formalizes the definitions and main results.
-/

import Mathlib

open Finset BigOperators

namespace Erdos55

/-! ## Core Definitions -/

/-- An r-coloring of a set A assigns each element one of r colors. -/
def Coloring (A : Set ℕ) (r : ℕ) := A → Fin r

/-- A monochromatic subset under a coloring: all elements have the same color. -/
def IsMonochromatic {A : Set ℕ} {r : ℕ} (S : Set ℕ) (c : Coloring A r)
    (hSA : S ⊆ A) : Prop :=
  ∃ color : Fin r, ∀ x : ℕ, ∀ hx : x ∈ S, c ⟨x, hSA hx⟩ = color

/-- The set of finite sums of elements from a set S (with repetition allowed). -/
def FiniteSums (S : Set ℕ) : Set ℕ :=
  { n | ∃ (k : ℕ) (f : Fin k → ℕ), (∀ i, f i ∈ S) ∧ n = ∑ i, f i }

/-- A set A is **Ramsey r-complete** if for every r-coloring of A,
    there exists a monochromatic subset whose finite sums cover all
    sufficiently large integers. -/
def IsRamseyComplete (A : Set ℕ) (r : ℕ) : Prop :=
  ∀ c : Coloring A r, ∃ (S : Set ℕ) (hSA : S ⊆ A) (N₀ : ℕ),
    IsMonochromatic S c hSA ∧ ∀ n ≥ N₀, n ∈ FiniteSums S

/-- The counting function: |A ∩ [1, N]| -/
noncomputable def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard (A ∩ Set.Icc 1 N)

/-! ## Growth Rate Bounds -/

/-- A set has growth rate at most f if |A ∩ [1,N]| ≤ f(N) for large N. -/
def HasGrowthAtMost (A : Set ℕ) (f : ℕ → ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ N ≥ N₀, (countingFunction A N : ℝ) ≤ f N

/-- A set has growth rate at least f if |A ∩ [1,N]| ≥ f(N) for large N. -/
def HasGrowthAtLeast (A : Set ℕ) (f : ℕ → ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ N ≥ N₀, f N ≤ (countingFunction A N : ℝ)

/-! ## Main Results -/

/--
**Burr-Erdős Lower Bound (1985)**:
For r = 2, if A is Ramsey 2-complete, then A cannot grow slower than (log N)².

More precisely: there exists c > 0 such that no Ramsey 2-complete set A
can satisfy |A ∩ [1,N]| ≤ c(log N)² for all large N.
-/
axiom burr_erdos_lower_bound :
    ∃ c : ℝ, c > 0 ∧
    ∀ A : Set ℕ, IsRamseyComplete A 2 →
      ¬HasGrowthAtMost A (fun N => c * (Real.log N)^2)

/--
**Burr-Erdős Upper Bound (1985)**:
There exists a Ramsey 2-complete set A with |A ∩ [1,N]| ≪ (log N)³.
-/
axiom burr_erdos_upper_bound :
    ∃ A : Set ℕ, ∃ C : ℝ, C > 0 ∧
    IsRamseyComplete A 2 ∧ HasGrowthAtMost A (fun N => C * (Real.log N)^3)

/--
**Burr's Theorem**: The set of k-th powers is Ramsey r-complete for all r, k ≥ 1.
-/
axiom powers_ramsey_complete (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    IsRamseyComplete { n | ∃ m : ℕ, n = m^k } r

/-! ## The Solution: Conlon-Fox-Pham (2021) -/

/--
**Conlon-Fox-Pham Upper Bound (2021)**:
For every r ≥ 2, there exists an r-Ramsey complete set A with
|A ∩ [1,N]| ≪ r(log N)².

This constructs sets with optimal growth rate.
-/
axiom cfp_upper_bound (r : ℕ) (hr : 2 ≤ r) :
    ∃ A : Set ℕ, ∃ C : ℝ, C > 0 ∧
    IsRamseyComplete A r ∧ HasGrowthAtMost A (fun N => C * r * (Real.log N)^2)

/--
**Conlon-Fox-Pham Lower Bound (2021)**:
There exists a universal constant c > 0 such that if A ⊆ ℕ satisfies
|A ∩ [1,N]| ≤ cr(log N)² for all large N, then A is not r-Ramsey complete.

This shows the upper bound is tight up to constants.
-/
axiom cfp_lower_bound :
    ∃ c : ℝ, c > 0 ∧
    ∀ r : ℕ, 2 ≤ r →
    ∀ A : Set ℕ, HasGrowthAtMost A (fun N => c * r * (Real.log N)^2) →
      ¬IsRamseyComplete A r

/--
**Erdős Problem 55 (SOLVED)**:
The optimal growth rate for r-Ramsey complete sets is Θ(r(log N)²).

Combining the upper and lower bounds from Conlon-Fox-Pham:
- Upper: ∃ r-Ramsey complete A with |A ∩ [1,N]| ≤ C·r(log N)²
- Lower: If |A ∩ [1,N]| ≤ c·r(log N)², then A is not r-Ramsey complete

This resolves the problem for all r ≥ 2.
-/
theorem erdos_55_solution :
    -- Upper bound: optimal growth is achievable
    (∀ r : ℕ, 2 ≤ r → ∃ A : Set ℕ, ∃ C : ℝ, C > 0 ∧
      IsRamseyComplete A r ∧ HasGrowthAtMost A (fun N => C * r * (Real.log N)^2)) ∧
    -- Lower bound: cannot do better
    (∃ c : ℝ, c > 0 ∧ ∀ r : ℕ, 2 ≤ r → ∀ A : Set ℕ,
      HasGrowthAtMost A (fun N => c * r * (Real.log N)^2) → ¬IsRamseyComplete A r) := by
  constructor
  · intro r hr
    exact cfp_upper_bound r hr
  · exact cfp_lower_bound

/-! ## Corollaries -/

/-- For r = 2, the optimal growth rate is Θ((log N)²). -/
theorem optimal_growth_r2 :
    -- Upper bound: Θ((log N)²) is achievable for r=2
    (∃ A : Set ℕ, ∃ C : ℝ, C > 0 ∧
      IsRamseyComplete A 2 ∧ HasGrowthAtMost A (fun N => C * (Real.log N)^2)) ∧
    -- Lower bound: cannot do better than (log N)²
    (∃ c : ℝ, c > 0 ∧ ∀ A : Set ℕ,
      HasGrowthAtMost A (fun N => c * (Real.log N)^2) → ¬IsRamseyComplete A 2) := by
  constructor
  · -- From cfp_upper_bound with r=2
    obtain ⟨A, C, hC, hRam, hGrowth⟩ := cfp_upper_bound 2 (by norm_num)
    refine ⟨A, 2 * C, by linarith, hRam, ?_⟩
    obtain ⟨N₀, hN₀⟩ := hGrowth
    use N₀
    intro N hN
    calc (countingFunction A N : ℝ) ≤ C * 2 * (Real.log N)^2 := hN₀ N hN
      _ = 2 * C * (Real.log N)^2 := by ring
  · -- From cfp_lower_bound with r=2
    obtain ⟨c, hc, hLower⟩ := cfp_lower_bound
    refine ⟨2 * c, by linarith, ?_⟩
    intro A hA
    apply hLower 2 (by norm_num)
    obtain ⟨N₀, hN₀⟩ := hA
    use N₀
    intro N hN
    calc (countingFunction A N : ℝ) ≤ 2 * c * (Real.log N)^2 := hN₀ N hN
      _ = c * 2 * (Real.log N)^2 := by ring

/-! ## Historical Notes

The problem asked for "non-trivial bounds" on the growth rate of Ramsey
r-complete sets for r > 2. The Burr-Erdős paper (1985) established the
case r = 2, with a gap between (log N)² and (log N)³.

Conlon, Fox, and Pham (2021) completely resolved the problem:
1. The correct growth rate is Θ(r(log N)²) for all r ≥ 2
2. For r = 2, this closes the (log N)² vs (log N)³ gap from Burr-Erdős
3. The linear dependence on r is optimal

The construction for the upper bound uses carefully chosen subsets of
powers of 2, while the lower bound uses probabilistic coloring arguments.

References:
- Burr-Erdős (1985): "A Ramsey-type property in additive number theory"
- Conlon-Fox-Pham (2021): "Subset sums, completeness and colorings"
-/

end Erdos55
