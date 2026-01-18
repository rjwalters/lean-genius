/-
  Erdős Problem #442: LCM Sums Over Dense Subsets

  Source: https://erdosproblems.com/442
  Status: SOLVED (DISPROVED by Tao, 2024)

  Statement:
  Let A ⊆ ℕ be a set of natural numbers such that
    (1/log log x) · Σ_{n∈A, n≤x} 1/n → ∞
  Must it be true that
    (Σ_{n∈A, n≤x} 1/n)^{-2} · Σ_{a,b∈A, a<b≤x} 1/lcm(a,b) → ∞?

  Answer: NO

  Tao [2024] showed this is FALSE: there exists A ⊂ ℕ such that
  - Σ_{n∈A, n≤x} 1/n ≫ exp((1/2 + o(1))√(log log x) · log log log x)
  - Yet the normalized LCM sum stays bounded!

  Tao also proved this is OPTIMAL: if the reciprocal sum grows faster
  than exp(O(√(log log x) · log log log x)), then the LCM sum DOES diverge.

  Reference: Tao, T., "Dense sets of natural numbers with unusually
             large least common multiples". arXiv:2407.04226 (2024)

  Tags: number-theory, lcm, dense-sets, reciprocal-sum, counterexample
-/

import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.FilterProduct
import Mathlib.Tactic

namespace Erdos442

open Nat BigOperators Filter Real Set Classical

/-! ## Part I: Background and Definitions -/

/-- Log⁺(x) = max(log x, 1), ensuring positivity for all x > 0. -/
noncomputable def logPlus (x : ℝ) : ℝ := max (Real.log x) 1

/-- Iterated log⁺: log₂⁺(x) = log⁺(log⁺(x)). -/
noncomputable def log2Plus (x : ℝ) : ℝ := logPlus (logPlus x)

/-- Triple iterated log⁺: log₃⁺(x) = log⁺(log⁺(log⁺(x))). -/
noncomputable def log3Plus (x : ℝ) : ℝ := logPlus (log2Plus x)

/-- log⁺ is always at least 1. -/
theorem logPlus_ge_one (x : ℝ) : logPlus x ≥ 1 := le_max_right _ _

/-- For large x, log⁺(x) = log(x). -/
theorem logPlus_eq_log {x : ℝ} (hx : x ≥ Real.exp 1) : logPlus x = Real.log x := by
  unfold logPlus
  have h : Real.log x ≥ 1 := by
    rw [ge_iff_le, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hx
  exact max_eq_left h

/-! ## Part II: The Reciprocal Sum -/

/-- The set of elements of A that are at most N. -/
def boundedSet (A : Set ℕ) (N : ℕ) : Set ℕ := A ∩ Set.Icc 1 N

/-- The reciprocal sum Σ_{n∈A, n≤N} 1/n.
    We use Finset.Icc and filter with classical decidability. -/
noncomputable def reciprocalSum (A : Set ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (· ∈ A), (1 : ℝ) / n

/-- The harmonic sum over full [1,N] is positive for N ≥ 1. -/
theorem harmonicSum_pos {N : ℕ} (hN : N ≥ 1) :
    ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n > 0 := by
  apply Finset.sum_pos
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    have hi1 : (1 : ℕ) ≤ i := hi.1
    have hcast : (0 : ℝ) < i := by exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hi1)
    exact div_pos one_pos hcast
  · exact ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩⟩

/-! ## Part III: The LCM Sum -/

/-- The upper triangular pairs in A ∩ [1,N]: {(a,b) | a,b ∈ A, 1 ≤ a < b ≤ N}. -/
def upperPairs (A : Set ℕ) (N : ℕ) : Set (ℕ × ℕ) :=
  { p | p.1 ∈ A ∧ p.2 ∈ A ∧ 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ N }

/-- The LCM sum Σ_{a,b∈A, a<b≤N} 1/lcm(a,b). -/
noncomputable def lcmSum (A : Set ℕ) (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
          (fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 < p.2),
    (1 : ℝ) / (p.1.lcm p.2)

/-- The normalized LCM sum: (Σ 1/n)^{-2} · (Σ 1/lcm(a,b)). -/
noncomputable def normalizedLcmSum (A : Set ℕ) (N : ℕ) : ℝ :=
  (reciprocalSum A N)⁻¹ ^ 2 * lcmSum A N

/-! ## Part IV: The Density Condition -/

/-- The density condition: (1/log log x) · Σ 1/n → ∞.
    This says A is "dense" in the sense that its reciprocal sum
    grows faster than log log x. -/
def isDenseSubset (A : Set ℕ) : Prop :=
  Tendsto (fun N : ℕ => reciprocalSum A N / log2Plus N) atTop atTop

/-- Example: The primes satisfy the density condition
    (by Mertens' theorem, Σ_{p≤x} 1/p ~ log log x). -/
axiom primes_are_dense : isDenseSubset { p : ℕ | Nat.Prime p }

/-! ## Part V: The Main Conjecture and Its Refutation -/

/-- Erdős asked: Does density imply LCM divergence?
    That is, if (1/log log x) · Σ 1/n → ∞, must
    (Σ 1/n)^{-2} · Σ 1/lcm(a,b) → ∞? -/
def Erdos442Conjecture : Prop :=
  ∀ A : Set ℕ, isDenseSubset A →
    Tendsto (fun N => normalizedLcmSum A N) atTop atTop

/-- **Erdős Problem #442**: Tao proved the conjecture is FALSE.

    There exists A ⊂ ℕ such that:
    - A is dense (reciprocal sum grows faster than 1/log log x)
    - Yet the normalized LCM sum stays bounded!

    This is surprising because one might expect that "more elements"
    means "more LCM interactions" which should dominate. -/
axiom tao_counterexample : ¬ Erdos442Conjecture

/-- The answer to Erdős Problem #442 is FALSE. -/
theorem erdos_442_answer : False ↔ Erdos442Conjecture := by
  constructor
  · intro h; exact h.elim
  · intro h; exact tao_counterexample h

/-! ## Part VI: Tao's Construction -/

/-- Tao's counterexample set A has reciprocal sum growing at a specific rate:
    Σ_{n∈A, n≤x} 1/n = exp((1/2 + o(1)) · √(log log x) · log log log x)

    This is MUCH faster than log log x, but there's a precise threshold. -/
noncomputable def TaoGrowthRate (x : ℝ) : ℝ :=
  Real.exp ((1/2) * Real.sqrt (log2Plus x) * log3Plus x)

/-- There exists Tao's counterexample set with the claimed properties. -/
axiom tao_construction :
  ∃ A : Set ℕ,
    -- The reciprocal sum grows at Tao's rate
    (∃ f : ℝ → ℝ, (f =o[atTop] (1 : ℝ → ℝ)) ∧
      ∀ᶠ N : ℕ in atTop, reciprocalSum A N =
        Real.exp ((1/2 + f N) * Real.sqrt (log2Plus N) * log3Plus N)) ∧
    -- Yet the normalized LCM sum is bounded
    (∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, normalizedLcmSum A N ≤ C)

/-! ## Part VII: Optimality -/

/-- Tao also proved the threshold is SHARP: if the reciprocal sum
    grows faster than exp(C · √(log log x) · log log log x) for any C,
    then the normalized LCM sum DOES diverge. -/
def FasterThanThreshold (A : Set ℕ) : Prop :=
  ∀ C : ℝ, C > 0 →
    ∀ᶠ N : ℕ in atTop, reciprocalSum A N >
      Real.exp (C * Real.sqrt (log2Plus N) * log3Plus N)

/-- If A grows faster than Tao's threshold, LCM divergence holds. -/
axiom tao_optimality :
  ∀ A : Set ℕ, FasterThanThreshold A →
    Tendsto (fun N => normalizedLcmSum A N) atTop atTop

/-! ## Part VIII: Key Insight: Why the Counterexample Works -/

/-- The key insight is about STRUCTURE vs DENSITY.

    Tao's set A is constructed so that elements share many prime factors
    in a controlled way. This makes:
    - The reciprocal sum large (many elements)
    - But lcm(a,b) also large (shared factors don't reduce lcm much)

    The careful balance ensures the normalized sum stays bounded. -/
theorem structure_insight : True := trivial

/-- The construction uses "smooth numbers" (numbers with only small
    prime factors) arranged in a specific pattern. -/
theorem smooth_numbers_hint : True := trivial

/-! ## Part IX: LCM Properties -/

/-- Basic LCM property: lcm(a,b) · gcd(a,b) = a · b. -/
theorem lcm_gcd_identity (a b : ℕ) : a.lcm b * a.gcd b = a * b :=
  Nat.lcm_mul_gcd a b

/-- For coprime numbers, lcm(a,b) = a · b. -/
theorem lcm_coprime {a b : ℕ} (h : a.Coprime b) : a.lcm b = a * b := by
  rw [Nat.lcm, h.gcd_eq_one, Nat.div_one]

/-- 1/lcm(a,b) = gcd(a,b)/(a·b) for positive a,b. -/
theorem one_div_lcm (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (1 : ℝ) / (a.lcm b) = (a.gcd b : ℝ) / ((a : ℝ) * b) := by
  have hlcm : a.lcm b ≠ 0 := Nat.lcm_ne_zero ha hb
  have key := lcm_gcd_identity a b
  field_simp
  push_cast
  calc (a : ℝ) * b = ((a * b : ℕ) : ℝ) := by norm_cast
    _ = ((a.lcm b * a.gcd b : ℕ) : ℝ) := by rw [key]
    _ = (a.lcm b : ℝ) * (a.gcd b : ℝ) := by push_cast; ring

/-! ## Part X: Verified Examples -/

/-- Example: lcm(6, 10) = 30 and gcd(6, 10) = 2.
    So 1/30 = 2/(6·10) = 2/60 = 1/30. ✓ -/
example : (6 : ℕ).lcm 10 = 30 := by native_decide

example : (6 : ℕ).gcd 10 = 2 := by native_decide

/-- Example: For coprime 3 and 5, lcm(3,5) = 15 = 3 × 5. -/
example : (3 : ℕ).lcm 5 = 15 := by native_decide

/-! ## Part XI: Summary -/

/-- **Summary of Erdős Problem #442**

    **Question**: If A ⊂ ℕ has reciprocal sum growing faster than log log x,
    must the normalized LCM sum diverge?

    **Answer**: NO (Tao 2024)

    **Key points**:
    1. Tao constructed an explicit counterexample
    2. The counterexample has reciprocal sum ~ exp((1/2+o(1))√(log log x)·log log log x)
    3. The threshold is sharp: faster growth DOES imply divergence
    4. The construction uses carefully structured smooth numbers

    **Significance**: This resolves a 44-year-old question from Erdős-Graham [1980]
    and reveals a precise threshold for when density implies LCM divergence. -/
theorem erdos_442_summary :
    ¬ Erdos442Conjecture ∧
    ∃ A : Set ℕ, (∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, normalizedLcmSum A N ≤ C) := by
  constructor
  · exact tao_counterexample
  · obtain ⟨A, _, hbounded⟩ := tao_construction
    exact ⟨A, hbounded⟩

end Erdos442

/-!
## Final Notes

This formalization captures Erdős Problem #442, resolved by Terence Tao in 2024.

**The Question**: Does density (reciprocal sum >> log log x) imply
normalized LCM sum divergence?

**The Answer**: NO! Tao's counterexample has:
- Reciprocal sum ~ exp((1/2+o(1))√(log log x)·log log log x)
- But normalized LCM sum stays bounded

**What's remarkable**:
1. The threshold is EXACT: exp(C√(log log x)·log log log x) for any C
2. Above this threshold, LCM divergence DOES hold
3. The construction uses sophisticated smooth number techniques

**Historical significance**: This resolves a problem from Erdős-Graham
"Old and New Problems in Combinatorial Number Theory" [1980, p.88].
-/
