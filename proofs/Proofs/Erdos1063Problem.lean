/-
# Erdős Problem #1063: Binomial Coefficient Divisibility

**Source:** [erdosproblems.com/1063](https://erdosproblems.com/1063)
**Status:** OPEN (Erdős–Selfridge, 1983)

## Statement

Let k ≥ 2. Define n_k ≥ 2k as the least n such that (n - i) | C(n,k)
for all but one 0 ≤ i < k. Estimate n_k.

## Background

Erdős and Selfridge (1983) proved that for n ≥ 2k, at least one
value 0 ≤ i < k exists where (n - i) does not divide C(n,k).
This problem asks for the threshold n_k where all but one of the
divisibilities hold.

Known values: n_2 = 4, n_3 = 6, n_4 = 9, n_5 = 12.
Monier (1985): n_k ≤ k! for k ≥ 3.
Cambie: n_k ≤ k · lcm(2,...,k-1) ≤ e^{(1+o(1))k}.

## Approach

We define the divisibility condition, the threshold n_k, verify
small cases, and state the known bounds as axioms.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Erdos1063

/- ## Part I: Divisibility Condition -/

/--
(n - i) divides C(n, k) for a given n, k, i.
-/
def DividesChoose (n k i : ℕ) : Prop :=
  i < k ∧ n ≥ 2 * k ∧ (n - i) ∣ Nat.choose n k

/--
The count of values 0 ≤ i < k for which (n - i) | C(n, k).
-/
def divisibilityCount (n k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun i => (n - i) ∣ Nat.choose n k)).card

/--
All but one of {n, n-1, ..., n-k+1} divide C(n, k).
-/
@[reducible] def AllButOneDivide (n k : ℕ) : Prop :=
  n ≥ 2 * k ∧ divisibilityCount n k ≥ k - 1

/- ## Part II: The Threshold n_k -/

/--
n_k is the least n ≥ 2k such that all but one of
{n, n-1, ..., n-k+1} divide C(n, k).
-/
def IsThreshold (nk k : ℕ) : Prop :=
  AllButOneDivide nk k ∧
  ∀ m : ℕ, m < nk → m ≥ 2 * k → ¬AllButOneDivide m k

/- ## Part III: Erdős–Selfridge Result -/

/--
**Erdős–Selfridge (1983):**
For n ≥ 2k, at least one value 0 ≤ i < k has
(n - i) ∤ C(n, k).

That is, you can never have ALL of {n, n-1, ..., n-k+1}
divide C(n, k).
-/
axiom erdos_selfridge_nondivisibility :
  ∀ k : ℕ, k ≥ 2 →
    ∀ n : ℕ, n ≥ 2 * k →
      divisibilityCount n k < k

/- ## Part IV: Known Small Values -/

/--
n_2 = 4: C(4,2) = 6, and 4 ∤ 6 but 3 | 6.
So all but one (i.e., 1 out of 2) of {4,3} divides C(4,2).
Minimality is vacuous since 2·2 = 4. -/
theorem threshold_k2 : IsThreshold 4 2 := by
  refine ⟨⟨by norm_num, by native_decide⟩, fun m hm hge => by omega⟩

/--
n_3 = 6: C(6,3) = 20, and 5 | 20, 4 | 20, but 6 ∤ 20.
Minimality is vacuous since 2·3 = 6. -/
theorem threshold_k3 : IsThreshold 6 3 := by
  refine ⟨⟨by norm_num, by native_decide⟩, fun m hm hge => by omega⟩

/--
n_4 = 9: C(9,4) = 126, and 9 | 126, 7 | 126, 6 | 126, but 8 ∤ 126.
Minimality checked at m = 8: C(8,4) = 70 has only 2 divisors from {8,7,6,5}. -/
theorem threshold_k4 : IsThreshold 9 4 := by
  refine ⟨⟨by norm_num, by native_decide⟩, ?_⟩
  intro m hm hge
  have : m = 8 := by omega
  subst this; native_decide

/--
n_5 = 12: C(12,5) = 792, and 12 | 792, 11 | 792, 9 | 792, 8 | 792, but 10 ∤ 792.
Minimality checked at m ∈ {10, 11}: neither achieves 4 divisors. -/
theorem threshold_k5 : IsThreshold 12 5 := by
  refine ⟨⟨by norm_num, by native_decide⟩, ?_⟩
  intro m hm hge
  have : m = 10 ∨ m = 11 := by omega
  rcases this with rfl | rfl <;> native_decide

/- ## Part V: Upper Bounds -/

/--
**Monier (1985):** n_k ≤ k! for k ≥ 3.
-/
axiom monier_factorial_bound :
  ∀ k : ℕ, k ≥ 3 →
    ∃ nk : ℕ, IsThreshold nk k ∧ nk ≤ Nat.factorial k

/--
**Cambie:** n_k ≤ k · lcm(2, 3, ..., k-1) ≤ e^{(1+o(1))k}.
This is a significant improvement over the factorial bound.
-/
axiom cambie_lcm_bound :
  ∀ k : ℕ, k ≥ 3 →
    ∃ nk : ℕ, IsThreshold nk k ∧
      nk ≤ k * Nat.factorial (k - 1)  -- crude bound; true bound uses lcm

/--
**The main open question (Erdős Problem #1063):**
What is the true growth rate of n_k? In particular,
is n_k polynomial in k, or does it grow exponentially?
-/
def ErdosProblem1063 : Prop :=
  ∃ C : ℕ, C ≥ 1 ∧
    ∀ k : ℕ, k ≥ 2 →
      ∃ nk : ℕ, IsThreshold nk k ∧ nk ≤ k ^ C

/- ## Part V.5: Unified Existence -/

/--
**Existence of the threshold**: for every k ≥ 2, there exists some n_k
satisfying `IsThreshold`. This combines the small-case witnesses
(`threshold_k2`..`threshold_k5`) with Monier's factorial-bound axiom for
k ≥ 3, giving a single uniform existence statement.

The bounds — `monier_factorial_bound` (k!) and `cambie_lcm_bound`
(k · (k-1)!) — both witness existence but with explicit (exponential)
ceilings; this lemma extracts the bare existence without the size bound.
-/
theorem threshold_exists (k : ℕ) (hk : k ≥ 2) :
    ∃ nk : ℕ, IsThreshold nk k := by
  by_cases h3 : k ≥ 3
  · obtain ⟨nk, hth, _⟩ := monier_factorial_bound k h3
    exact ⟨nk, hth⟩
  · have : k = 2 := by omega
    subst this
    exact ⟨4, threshold_k2⟩

/- ## Part VI: Summary -/

/--
**Summary of Erdős Problem #1063:**

Erdős Problem #1063 asks for the growth rate of n_k, the least n ≥ 2k
where all but one of {n,...,n-k+1} divide C(n,k).

**Known values:** n_2 = 4, n_3 = 6, n_4 = 9, n_5 = 12.

**Upper bounds:**
- Monier (1985): n_k ≤ k!
- Cambie: n_k ≤ k · lcm(2,...,k-1) ≤ e^{(1+o(1))k}

**Status:** OPEN — the true growth rate (polynomial vs exponential) is unknown.

**Key structural fact (Erdős-Selfridge):**
Full divisibility (all k values dividing) never occurs for n ≥ 2k.
-/
theorem erdos_1063_summary :
    -- The Erdős-Selfridge non-divisibility holds
    (∀ k : ℕ, k ≥ 2 → ∀ n : ℕ, n ≥ 2 * k → divisibilityCount n k < k) ∧
    -- Monier's factorial bound exists
    (∀ k : ℕ, k ≥ 3 → ∃ nk : ℕ, IsThreshold nk k ∧ nk ≤ Nat.factorial k) := by
  exact ⟨erdos_selfridge_nondivisibility, monier_factorial_bound⟩

end Erdos1063
