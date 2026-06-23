/-
Erdős Problem #650: Divisibility Representation in Intervals

Source: https://erdosproblems.com/650
Status: OPEN

Statement:
Let f(m) be the minimum number of integers in any interval of length 2N on [1,∞)
that are divisible by some element of A, where A ⊆ {1,...,N} has |A| = m.
Estimate f(m) - in particular, is f(m) ≪ m^{1/2}?

Erdős and Sarányi established f(m) ≫ m^{1/2}.

References:
- Erdős and Sarányi: Lower bound f(m) ≫ √m
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

namespace Erdos650

/-
## Part I: Definitions
-/

/--
Given A ⊆ {1,...,N} and an interval [a, a+2N), count how many integers
in this interval are divisible by some element of A.
-/
def countDivisible (A : Finset ℕ) (N a : ℕ) : ℕ :=
  ((Finset.Icc a (a + 2 * N)).filter (fun x =>
    ∃ d ∈ A, d ∣ x)).card

/--
f(A, N) = the minimum count over all intervals of length 2N.
-/
noncomputable def minCoverage (A : Finset ℕ) (N : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ a : ℕ, a ≥ 1 ∧ countDivisible A N a = k}

/--
f(m) = the minimum of minCoverage over all A ⊆ {1,...,N} with |A| = m.
-/
noncomputable def f (m N : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.range (N + 1) ∧
    A.card = m ∧ minCoverage A N = k}

/-
## Part II: Known Bounds
-/

/--
**Erdős-Sarányi Lower Bound**: f(m) ≫ √m.

There exists a constant c > 0 such that for all sufficiently large m and N,
every A ⊆ {1,...,N} with |A| = m covers at least c√m integers in every
interval of length 2N.
-/
axiom erdos_saranyi_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ m N : ℕ, m ≥ 1 → N ≥ m →
      (f m N : ℝ) ≥ c * Real.sqrt m

/-
## Part III: Open Conjecture
-/

/--
**Erdős's Conjecture (OPEN)**: f(m) ≪ √m.

If true, combined with the lower bound this would give f(m) ≍ √m.
-/
axiom erdos_upper_bound_conjecture :
    ∃ C : ℝ, C > 0 ∧ ∀ m : ℕ, m ≥ 1 →
      ∃ N : ℕ, N ≥ m ∧ (f m N : ℝ) ≤ C * Real.sqrt m

/-
## Part IV: Main Theorem
-/

/--
**Erdős Problem #650: OPEN**

The known result: f(m) ≫ √m (Erdős-Sarányi).
The open question: is f(m) ≍ √m?
-/
theorem erdos_650 :
    ∃ c : ℝ, c > 0 ∧ ∀ m N : ℕ, m ≥ 1 → N ≥ m →
      (f m N : ℝ) ≥ c * Real.sqrt m :=
  erdos_saranyi_lower_bound

end Erdos650
