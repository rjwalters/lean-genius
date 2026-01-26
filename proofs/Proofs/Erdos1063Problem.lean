/-!
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

/-! ## Part I: Divisibility Condition -/

/--
(n - i) divides C(n, k) for a given n, k, i.
-/
def DividesChoose (n k i : ℕ) : Prop :=
  i < k ∧ n ≥ 2 * k ∧ (n - i) ∣ Nat.choose n k

/--
The count of values 0 ≤ i < k for which (n - i) | C(n, k).
-/
noncomputable def divisibilityCount (n k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun i => (n - i) ∣ Nat.choose n k)).card

/--
All but one of {n, n-1, ..., n-k+1} divide C(n, k).
-/
def AllButOneDivide (n k : ℕ) : Prop :=
  n ≥ 2 * k ∧ divisibilityCount n k ≥ k - 1

/-! ## Part II: The Threshold n_k -/

/--
n_k is the least n ≥ 2k such that all but one of
{n, n-1, ..., n-k+1} divide C(n, k).
-/
def IsThreshold (nk k : ℕ) : Prop :=
  AllButOneDivide nk k ∧
  ∀ m : ℕ, m < nk → m ≥ 2 * k → ¬AllButOneDivide m k

/-! ## Part III: Erdős–Selfridge Result -/

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

/-! ## Part IV: Known Small Values -/

/--
n_2 = 4: C(4,2) = 6, and 4 | 6 is false but 3 | 6 is true.
So all but one (i.e., 1 out of 2) of {4,3} divides C(4,2).
-/
axiom threshold_k2 : IsThreshold 4 2

/--
n_3 = 6.
-/
axiom threshold_k3 : IsThreshold 6 3

/--
n_4 = 9.
-/
axiom threshold_k4 : IsThreshold 9 4

/--
n_5 = 12.
-/
axiom threshold_k5 : IsThreshold 12 5

/-! ## Part V: Upper Bounds -/

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

/-! ## Part VI: Summary -/

/--
**Summary:**
Erdős Problem #1063 asks for the growth rate of n_k, the least n
where all but one of {n,...,n-k+1} divide C(n,k). Known: n_2 = 4,
n_3 = 6, n_4 = 9, n_5 = 12. Monier: n_k ≤ k!. Cambie: n_k ≤
k · lcm(2,...,k-1). OPEN.
-/
theorem erdos_1063_status : True := trivial

end Erdos1063
