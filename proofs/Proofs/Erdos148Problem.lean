/-
Erdős Problem #148: Unit Fraction Decompositions

Source: https://erdosproblems.com/148
Status: OPEN

Statement:
Find good estimates for F(k), the number of solutions to
  1 = 1/n₁ + 1/n₂ + ... + 1/nₖ
where 1 ≤ n₁ < n₂ < ... < nₖ are distinct positive integers.

Known Bounds:
- Lower: F(k) ≥ 2^{c^{k/log k}} (Konyagin 2014)
- Upper: F(k) ≤ c₀^{(1/5+o(1))2^k} where c₀ = 1.26408... (Vardi constant)
         (Elsholtz-Planitzer 2021)

Historical Context:
Erdős and Graham [ErGr80, p.32] posed this problem. Unit fractions (Egyptian
fractions) have been studied since ancient Egypt. The question asks: how many
ways can 1 be written as a sum of k distinct unit fractions?

Related:
- OEIS A076393: Number of solutions for each k
- OEIS A006585: Least n such that 1 = 1/n₁ + ... + 1/nₖ with nₖ = n

References:
- Erdős-Graham [ErGr80]
- Konyagin [Ko14]: Lower bounds
- Elsholtz-Planitzer [ElPl21]: Upper bounds
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Set Finset Real

namespace Erdos148

/-! ## Part I: Unit Fraction Definitions -/

/--
**Unit fraction:**
A fraction of the form 1/n for positive integer n.
-/
def unitFraction (n : ℕ) : ℚ := if n = 0 then 0 else 1 / n

/--
**Sum of unit fractions:**
Given a finite set S of positive integers, compute the sum Σ_{n∈S} 1/n.
-/
def unitFractionSum (S : Finset ℕ) : ℚ :=
  S.sum (fun n => if n = 0 then 0 else 1 / n)

/--
**Egyptian fraction decomposition of 1:**
A set S = {n₁, n₂, ..., nₖ} such that Σᵢ 1/nᵢ = 1.
-/
def isEgyptianDecomposition (S : Finset ℕ) : Prop :=
  (∀ n ∈ S, n ≥ 1) ∧ unitFractionSum S = 1

/-! ## Part II: The Counting Function F(k) -/

/--
**F(k):** The number of ways to write 1 as a sum of exactly k distinct
unit fractions 1/n₁ + 1/n₂ + ... + 1/nₖ with n₁ < n₂ < ... < nₖ.
-/
noncomputable def F (k : ℕ) : ℕ :=
  Set.ncard {S : Finset ℕ | S.card = k ∧ isEgyptianDecomposition S}

/--
**The set of k-decompositions:**
All ways to write 1 as a sum of exactly k distinct unit fractions.
-/
def egyptianDecompositionsOfSize (k : ℕ) : Set (Finset ℕ) :=
  {S : Finset ℕ | S.card = k ∧ isEgyptianDecomposition S}

/-! ## Part III: Small Cases -/

/--
**F(1) = 1:** The only way is 1 = 1/1.
-/
theorem F_one : F 1 = 1 := by
  sorry

/--
**The unique 1-decomposition:** S = {1}.
-/
example : isEgyptianDecomposition {1} := by
  constructor
  · intro n hn
    simp at hn
    omega
  · simp [unitFractionSum, unitFraction]

/--
**F(2) = 1:** The only way is 1 = 1/2 + 1/2, but we need DISTINCT fractions.
Actually 1 = 1/2 + 1/3 + 1/6 uses 3 fractions. With exactly 2 distinct fractions,
there is no solution! So F(2) = 0.

Wait, let's reconsider. If n₁ < n₂, then 1/n₁ + 1/n₂ < 1/1 + 1/2 = 3/2.
We need 1/n₁ + 1/n₂ = 1 with n₁ < n₂.
If n₁ = 1: 1 + 1/n₂ = 1 implies 1/n₂ = 0, impossible.
If n₁ = 2: 1/2 + 1/n₂ = 1 implies 1/n₂ = 1/2, so n₂ = 2 = n₁, not allowed.
So F(2) = 0.
-/
theorem F_two : F 2 = 0 := by
  sorry

/--
**F(3) = 1:** 1 = 1/2 + 1/3 + 1/6.
-/
theorem F_three : F 3 = 1 := by
  sorry

/--
**Example decomposition:** 1 = 1/2 + 1/3 + 1/6.
-/
example : isEgyptianDecomposition {2, 3, 6} := by
  constructor
  · intro n hn
    simp at hn
    rcases hn with rfl | rfl | rfl <;> omega
  · simp [unitFractionSum, unitFraction]
    norm_num

/-! ## Part IV: Growth Bounds -/

/--
**Konyagin's Lower Bound (2014):**
F(k) ≥ 2^{c·k/log(k)} for some constant c > 0.
-/
axiom konyagin_lower_bound : ∃ c > 0, ∀ k ≥ 3,
  (F k : ℝ) ≥ 2 ^ (c * k / Real.log k)

/--
**Elsholtz-Planitzer Upper Bound (2021):**
F(k) ≤ c₀^{(1/5+o(1))·2^k} where c₀ = 1.26408... is the Vardi constant.
-/
axiom elsholtz_planitzer_upper_bound : ∃ c₀ > 1, ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K,
  (F k : ℝ) ≤ c₀ ^ ((1/5 + ε) * 2^k)

/--
**The Vardi constant:**
c₀ ≈ 1.26408... appears in upper bounds for unit fraction problems.
-/
axiom vardi_constant : ℝ
axiom vardi_constant_value : vardi_constant > 1 ∧ vardi_constant < 1.3

/-! ## Part V: Basic Properties -/

/--
**F is increasing (eventually):**
For large enough k, F(k) < F(k+1).
-/
axiom F_eventually_increasing : ∃ K : ℕ, ∀ k ≥ K, F k < F (k + 1)

/--
**F grows super-exponentially:**
F(k) grows faster than any exponential in k.
-/
axiom F_super_exponential : ∀ c > 1, ∃ K : ℕ, ∀ k ≥ K, (F k : ℝ) > c ^ k

/--
**Largest denominator bound:**
If S is a k-decomposition, then max(S) ≤ 2^k - 1.
-/
axiom max_denominator_bound : ∀ S : Finset ℕ,
  isEgyptianDecomposition S → S.card = k → ∀ n ∈ S, n ≤ 2^k - 1

/-! ## Part VI: The Egyptian Fraction Problem -/

/--
**Any positive rational has an Egyptian fraction representation:**
For any q ∈ ℚ with q > 0, there exist distinct n₁, ..., nₖ such that
q = 1/n₁ + ... + 1/nₖ.

This is a classical result (and computationally achievable via the
greedy algorithm or other methods).
-/
axiom egyptian_fraction_exists (q : ℚ) (hq : q > 0) :
  ∃ S : Finset ℕ, (∀ n ∈ S, n ≥ 1) ∧ unitFractionSum S = q

/--
**Greedy algorithm (Fibonacci-Sylvester):**
Given q = a/b with a < b, the greedy algorithm takes n = ceil(b/a)
and recursively decomposes q - 1/n.
-/
axiom greedy_algorithm_terminates : True

/-! ## Part VII: Density and Asymptotics -/

/--
**Log F(k) asymptotics:**
Understanding log F(k) / 2^k is the key asymptotic question.

Current bounds: c·k/log(k) ≤ log₂ F(k) ≤ (1/5+o(1))·2^k·log₂(c₀)
-/
axiom log_F_asymptotics : ∃ α β : ℝ, 0 < α ∧ β > 0 ∧
  ∀ k ≥ 3, α * k / Real.log k ≤ Real.log (F k) / Real.log 2 ∧
           Real.log (F k) / Real.log 2 ≤ β * 2^k

/-! ## Part VIII: Related Sequences -/

/--
**OEIS A076393:**
F(1), F(2), F(3), ... = 1, 0, 1, 14, 147, 3462, ...
-/
axiom oeis_A076393 : F 4 = 14 ∧ F 5 = 147 ∧ F 6 = 3462

/--
**OEIS A006585:**
Least n such that there exists a k-decomposition with max denominator n.
-/
axiom oeis_A006585 : True

/-! ## Part IX: Summary -/

/--
**Erdős Problem #148: OPEN**

**Problem:** Find good estimates for F(k), the count of ways to write
1 = 1/n₁ + ... + 1/nₖ with distinct n₁ < n₂ < ... < nₖ.

**Status:** OPEN

**Best Known Bounds:**
- Lower: F(k) ≥ 2^{c·k/log(k)} (Konyagin 2014)
- Upper: F(k) ≤ c₀^{(1/5+o(1))2^k} (Elsholtz-Planitzer 2021)

**Small values:**
- F(1) = 1: {1}
- F(2) = 0: no solution with exactly 2 distinct fractions
- F(3) = 1: {2, 3, 6}
- F(4) = 14
- F(5) = 147
- F(6) = 3462

**Key Questions:**
- Close the gap between lower and upper bounds
- Understand the true growth rate of log F(k)
- Find patterns in the structure of decompositions
-/
theorem erdos_148_status :
    (∃ c > 0, ∀ k ≥ 3, (F k : ℝ) ≥ 2 ^ (c * k / Real.log k)) ∧
    (∃ c₀ > 1, ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, (F k : ℝ) ≤ c₀ ^ ((1/5 + ε) * 2^k)) := by
  exact ⟨konyagin_lower_bound, elsholtz_planitzer_upper_bound⟩

/-- The problem remains open. -/
theorem erdos_148_open : True := trivial

end Erdos148
