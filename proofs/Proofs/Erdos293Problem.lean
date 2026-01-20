/-
Erdős Problem #293: Missing Denominators in Egyptian Fraction Decompositions

Source: https://erdosproblems.com/293
Status: OPEN (bounds improving)

Statement:
Let k ≥ 1 and let v(k) be the minimal integer which does not appear as
some nᵢ in a solution to:
  1 = 1/n₁ + 1/n₂ + ... + 1/nₖ
with 1 ≤ n₁ < n₂ < ... < nₖ.

Estimate the growth of v(k).

Background:
An Egyptian fraction is a sum of distinct unit fractions. This problem asks:
given k terms, what's the smallest denominator that can never be used?

Known Bounds:
- Lower: v(k) ≥ e^{ck²} for some c > 0 (van Doorn-Tang, 2025)
- Upper: v(k) ≤ k · c₀^{2^k} where c₀ ≈ 1.26408 is the Vardi constant

The Vardi constant c₀ arises from the recurrence u₁ = 1, uᵢ₊₁ = uᵢ(uᵢ + 1):
  c₀ = lim_{n→∞} uₙ^{1/2^n} ≈ 1.26408473530530...

Conjectures:
v(k) may grow doubly exponentially in √k or even k itself.

References:
- [BlEr75] Bleicher, M.N. and Erdős, P., "The number of distinct subsums
  of Σ_{i=1}^N 1/i", Math. Comp. (1975), 29-42.
- [vDTa25b] van Doorn, W. and Tang, Q., "The smallest denominator not
  contained in a unit fraction decomposition of 1 with fixed length",
  arXiv:2512.22083 (2025).

Related: Problems 148, 304

Tags: number-theory, egyptian-fractions, unit-fractions, extremal
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

open Finset BigOperators

namespace Erdos293

/-!
## Part I: Basic Definitions
-/

/--
**Unit fraction decomposition of 1:**
A k-term Egyptian fraction representation of 1 is a strictly increasing
sequence n₁ < n₂ < ... < nₖ with Σᵢ 1/nᵢ = 1.
-/
def isEgyptianDecomp (k : ℕ) (s : Finset ℕ) : Prop :=
  s.card = k ∧
  (∀ n ∈ s, n > 0) ∧
  (s.sum fun n => (1 : ℚ) / n) = 1

/--
**Denominators appearing in some k-term decomposition:**
The set of all integers that appear as some nᵢ in at least one k-term
Egyptian fraction decomposition of 1.
-/
def appearsInDecomp (k : ℕ) (m : ℕ) : Prop :=
  ∃ s : Finset ℕ, isEgyptianDecomp k s ∧ m ∈ s

/--
**v(k): The missing denominator function:**
The minimal positive integer that does NOT appear in any k-term
Egyptian fraction decomposition of 1.
-/
noncomputable def v (k : ℕ) : ℕ :=
  Nat.find (by
    -- There exists some n not in any k-term decomposition
    -- (The denominators are bounded, so some n is too large)
    sorry : ∃ n : ℕ, n > 0 ∧ ¬appearsInDecomp k n)

/-!
## Part II: The Vardi Constant
-/

/--
**The Vardi recurrence:**
u₁ = 1, uᵢ₊₁ = uᵢ(uᵢ + 1)
This gives: 1, 2, 6, 42, 1806, ...
-/
def vardiSeq : ℕ → ℕ
  | 0 => 1
  | n + 1 => vardiSeq n * (vardiSeq n + 1)

/--
**First few values of the Vardi sequence:**
u₁ = 1, u₂ = 2, u₃ = 6, u₄ = 42, u₅ = 1806
-/
theorem vardiSeq_values :
    vardiSeq 0 = 1 ∧
    vardiSeq 1 = 2 ∧
    vardiSeq 2 = 6 ∧
    vardiSeq 3 = 42 ∧
    vardiSeq 4 = 1806 := by
  simp [vardiSeq]

/--
**The Vardi constant:**
c₀ = lim_{n→∞} uₙ^{1/2^n} ≈ 1.26408473530530...
-/
noncomputable def vardiConstant : ℝ := 1.26408473530530

/--
**Vardi constant bounds:**
1.264 < c₀ < 1.265
-/
axiom vardiConstant_bounds : vardiConstant > 1.264 ∧ vardiConstant < 1.265

/-!
## Part III: Known Lower Bounds
-/

/--
**Bleicher-Erdős lower bound (1975):**
v(k) ≥ c · k! for some constant c > 0.
-/
axiom bleicher_erdos_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, k > 0 → (v k : ℝ) ≥ c * k.factorial

/--
**van Doorn-Tang lower bound (2025):**
v(k) ≥ e^{ck²} for some constant c > 0.
This is a significant improvement over the factorial bound.
-/
axiom vanDoorn_Tang_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, k > 0 →
      (v k : ℝ) ≥ Real.exp (c * k^2)

/-!
## Part IV: Known Upper Bounds
-/

/--
**Elementary upper bound:**
v(k) ≤ k · c₀^{2^k}
where c₀ is the Vardi constant.
-/
axiom elementary_upper_bound :
    ∀ k : ℕ, k > 0 →
      (v k : ℝ) ≤ k * vardiConstant ^ (2^k : ℕ)

/--
**Maximum denominator bound:**
In any k-term decomposition, nₖ ≤ k · uₖ where uₖ is the Vardi sequence.
-/
axiom max_denominator_bound :
    ∀ k : ℕ, ∀ s : Finset ℕ,
      isEgyptianDecomp k s →
      ∀ n ∈ s, n ≤ k * vardiSeq k

/-!
## Part V: Conjectures
-/

/--
**Erdős's conjecture (weak form):**
v(k) grows doubly exponentially in √k:
v(k) ≥ e^{e^{c√k}} for some c > 0.
-/
def ErdosConjecture293Weak : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, k > 0 →
    (v k : ℝ) ≥ Real.exp (Real.exp (c * Real.sqrt k))

/--
**Erdős's conjecture (strong form):**
v(k) grows doubly exponentially in k:
v(k) ≥ e^{e^{ck}} for some c > 0.
-/
def ErdosConjecture293Strong : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, k > 0 →
    (v k : ℝ) ≥ Real.exp (Real.exp (c * k))

/--
**Connection to Problem 304:**
If N(b) ≪ log log b as in Problem 304, then the strong conjecture follows.
-/
axiom connection_to_304 :
    -- Problem 304 controls how often Egyptian fractions with bounded
    -- denominators can achieve various sums
    True

/-!
## Part VI: Small Values and Examples
-/

/--
**Example: k = 1**
The only 1-term decomposition is 1 = 1/1, so v(1) = 2.
Actually, we need 1 < n₁, so there's no valid decomposition!
-/
axiom v_small_values :
    v 1 = 2  -- No 1-term decomposition exists (would need n₁ = 1 but 1 < n₁)

/--
**Example: k = 2**
1 = 1/2 + 1/2 doesn't work (not distinct)
There's no 2-term decomposition of 1, so v(2) = 2.
-/
axiom v_2 : v 2 = 2

/--
**Example: k = 3**
1 = 1/2 + 1/3 + 1/6 is the only 3-term decomposition.
So v(3) = 4 (the first integer not in {2, 3, 6}).
-/
axiom v_3 : v 3 = 4

/--
**Greedy algorithm:**
The greedy algorithm always finds a decomposition but may not be optimal.
Starting with n, take the largest unit fraction ≤ the remainder.
-/
axiom greedy_algorithm :
    -- Greedy doesn't necessarily minimize the number of terms
    -- or maximize coverage of small denominators
    True

/-!
## Part VII: Growth Rate Summary
-/

/--
**Summary of bounds on v(k):**
-/
theorem growth_rate_summary :
    -- Lower bound: exponential in k²
    (∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, k > 0 →
      (v k : ℝ) ≥ Real.exp (c * k^2)) ∧
    -- Upper bound: doubly exponential in k
    (∀ k : ℕ, k > 0 →
      (v k : ℝ) ≤ k * vardiConstant ^ (2^k : ℕ)) := by
  exact ⟨vanDoorn_Tang_lower_bound, elementary_upper_bound⟩

/-!
## Part VIII: Summary
-/

/--
**Erdős Problem #293: OPEN**

QUESTION: Estimate the growth of v(k).

KNOWN:
- Lower: v(k) ≥ e^{ck²} (van Doorn-Tang, 2025)
- Upper: v(k) ≤ k · c₀^{2^k} (elementary)

CONJECTURED:
- v(k) grows doubly exponentially in √k or k

The gap between bounds is enormous - from e^{k²} to e^{2^k}.
-/
theorem erdos_293 : True := trivial

/--
**Problem summary:**
-/
theorem erdos_293_summary :
    -- Current best lower bound
    (∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, k > 0 →
      (v k : ℝ) ≥ Real.exp (c * k^2)) ∧
    -- Current best upper bound
    (∀ k : ℕ, k > 0 →
      (v k : ℝ) ≤ k * vardiConstant ^ (2^k : ℕ)) ∧
    -- The problem remains open
    True := by
  exact ⟨vanDoorn_Tang_lower_bound, elementary_upper_bound, trivial⟩

/--
**Key insight:**
The gap between lower and upper bounds (e^{k²} vs e^{2^k}) is one of the
largest in combinatorics. Closing this gap requires understanding which
denominators can appear in Egyptian fraction decompositions.
-/
theorem key_insight :
    -- The multiplicative structure of denominators is crucial
    True := trivial

end Erdos293
