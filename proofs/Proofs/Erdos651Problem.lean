/-
Erdős Problem #651: Exponential Growth of f_k(n)

Source: https://erdosproblems.com/651
Status: DISPROVED (Pohoata-Zakharov, 2022)

Statement:
Let f_k(n) denote the smallest integer such that any f_k(n) points in general
position in ℝ^k contain n points determining a convex polyhedron.

Is it true that f_k(n) > (1 + c_k)^n for some constant c_k > 0?

Answer: NO

Pohoata and Zakharov (2022) proved that f_3(n) ≤ 2^{o(n)}, showing that
even in 3 dimensions, f_k(n) grows slower than any exponential.

Context:
- When k = 2, this is the Erdős-Klein-Szekeres problem (Erdős #107)
- For k = 2, Erdős-Szekeres proved f_2(n) ≤ (2n-4 choose n-2) + 1 ~ 4^n/√n
- One can show f_2(n) > f_3(n) > f_4(n) > ... (monotonicity)
- The question asked whether exponential growth persists in higher dimensions

References:
- Pohoata, C. and Zakharov, D., "Convex polytopes from fewer points",
  arXiv:2208.04878 (2022)
- Erdős [Er97e]
- Erdős-Klein-Szekeres conjecture for k = 2
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Basic

open Real

namespace Erdos651

/-
## Part I: The Convex Position Function

The function f_k(n) from discrete geometry.
-/

/--
**Convex Position Function f_k(n):**
The smallest integer M such that any M points in general position in ℝ^k
contain n points that form the vertices of a convex polytope.

This is axiomatized as an abstract function satisfying the key properties.
-/
axiom convexPositionFn (k n : ℕ) : ℕ

notation "f_" k "(" n ")" => convexPositionFn k n

/-
## Part II: Basic Properties
-/

/--
**Well-Definedness:**
f_k(n) is well-defined for k ≥ 2 and n ≥ k + 1.
(We need at least k+1 points to form a k-dimensional simplex.)
-/
axiom convexPositionFn_pos (k n : ℕ) (hk : k ≥ 2) (hn : n ≥ k + 1) :
    f_ k (n) ≥ n

/--
**Trivial Lower Bound:**
We need at least n points to find n points in convex position.
-/
axiom convexPositionFn_ge_n (k n : ℕ) (hk : k ≥ 2) (hn : n ≥ k + 1) :
    f_ k (n) ≥ n

/--
**Monotonicity in k:**
Higher dimensions make it easier to be in convex position,
so f_k(n) decreases as k increases.
-/
axiom convexPositionFn_mono_k (k n : ℕ) (hk : k ≥ 2) (hn : n ≥ k + 2) :
    f_ (k + 1) (n) ≤ f_ k (n)

/--
**Monotonicity in n:**
Finding more points in convex position requires more points.
-/
axiom convexPositionFn_mono_n (k n : ℕ) (hk : k ≥ 2) (hn : n ≥ k + 1) :
    f_ k (n) ≤ f_ k (n + 1)

/-
## Part III: The k = 2 Case (Erdős-Szekeres)
-/

/--
**Erdős-Szekeres Upper Bound (k = 2):**
For points in the plane, f_2(n) ≤ (2n-4 choose n-2) + 1.

The exact value of f_2(n) is the subject of the Erdős-Klein-Szekeres
conjecture (Erdős Problem #107).
-/
axiom erdos_szekeres_upper (n : ℕ) (hn : n ≥ 3) :
    f_ 2 (n) ≤ Nat.choose (2 * n - 4) (n - 2) + 1

/--
**Erdős-Szekeres Lower Bound (k = 2):**
f_2(n) ≥ 2^(n-2) + 1.
-/
axiom erdos_szekeres_lower (n : ℕ) (hn : n ≥ 3) :
    f_ 2 (n) ≥ 2^(n - 2) + 1

/--
**Known Values for k = 2:**
f_2(3) = 3, f_2(4) = 5, f_2(5) = 9, f_2(6) = 17.
-/
axiom f2_small_values :
    f_ 2 (3) = 3 ∧
    f_ 2 (4) = 5 ∧
    f_ 2 (5) = 9 ∧
    f_ 2 (6) = 17

/-
## Part IV: Erdős's Conjecture
-/

/--
**Erdős's Original Question:**
Does there exist a constant c_k > 0 such that f_k(n) > (1 + c_k)^n?

This would mean exponential growth of f_k(n) in every dimension.
-/
def hasExponentialLowerBound (k : ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ k + 1 →
    (f_ k (n) : ℝ) > (1 + c) ^ (n : ℝ)

/--
**Conjecture for k = 2:**
For the plane, exponential growth holds (this is related to Erdős-Szekeres).
The lower bound f_2(n) ≥ 2^{n-2} + 1 shows c_2 ≥ 1 works.
-/
axiom exponential_holds_k2 : hasExponentialLowerBound 2

/-
## Part V: Pohoata-Zakharov Disproof
-/

/--
**Subexponential Growth:**
A function g : ℕ → ℕ has subexponential growth if for every ε > 0,
eventually g(n) < (1 + ε)^n.
-/
def hasSubexponentialGrowth (g : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    (g n : ℝ) < (1 + ε) ^ (n : ℝ)

/--
**Pohoata-Zakharov Theorem (2022):**
f_3(n) grows subexponentially, i.e., f_3(n) ≤ 2^{o(n)}.

More precisely: for every ε > 0, there exists N such that for all n ≥ N,
f_3(n) ≤ 2^{ε·n}.

This disproves Erdős's conjecture for k = 3 and hence for all k ≥ 3.
-/
axiom pohoata_zakharov_2022 : hasSubexponentialGrowth (convexPositionFn 3)

/--
**Corollary: No Exponential Lower Bound for k = 3:**
There is no constant c > 0 such that f_3(n) > (1 + c)^n for all large n.
-/
axiom no_exponential_lower_bound_k3 : ¬ hasExponentialLowerBound 3

/--
**Corollary for Higher Dimensions:**
Since f_k(n) ≤ f_3(n) for k ≥ 3 (by monotonicity), the exponential
lower bound fails for all k ≥ 3.
-/
axiom no_exponential_lower_bound_k_ge_3 (k : ℕ) (hk : k ≥ 3) :
    ¬ hasExponentialLowerBound k

/-
## Part VI: Main Result
-/

/--
**Erdős Problem #651: DISPROVED**

The answer to Erdős's question is NO: for k ≥ 3, f_k(n) does not
grow exponentially. Pohoata and Zakharov (2022) showed f_3(n) ≤ 2^{o(n)}.

Note: The conjecture IS true for k = 2 (the planar case).
-/
theorem erdos_651 : ¬ (∀ k : ℕ, k ≥ 2 → hasExponentialLowerBound k) := by
  intro h
  have h3 := h 3 (by norm_num : 3 ≥ 2)
  exact no_exponential_lower_bound_k3 h3

/--
**Complete Answer:**
- For k = 2: YES, exponential lower bound holds (Erdős-Szekeres lower bound)
- For k ≥ 3: NO, f_k(n) grows subexponentially (Pohoata-Zakharov)
-/
theorem erdos_651_complete :
    hasExponentialLowerBound 2 ∧
    (∀ k : ℕ, k ≥ 3 → ¬ hasExponentialLowerBound k) :=
  ⟨exponential_holds_k2, no_exponential_lower_bound_k_ge_3⟩

/-
## Part VII: The Dimension Gap
-/

/--
**Dimension Transition:**
There is a qualitative difference between k = 2 and k ≥ 3:
- k = 2: Exponential growth (at least 2^{n-2} + 1)
- k ≥ 3: Subexponential growth (at most 2^{o(n)})

This is a remarkable dimension-dependent phenomenon.
-/
theorem dimension_gap :
    hasExponentialLowerBound 2 ∧ ¬ hasExponentialLowerBound 3 :=
  ⟨exponential_holds_k2, no_exponential_lower_bound_k3⟩

/--
**Convergence of f_k:**
As k → ∞, the constraint of general position becomes less restrictive,
and f_k(n) → n (trivial lower bound).
-/
axiom fk_converges_to_n :
    ∀ n : ℕ, n ≥ 3 → ∃ K : ℕ, ∀ k : ℕ, k ≥ K → f_ k (n) = n

/-
## Part VIII: Summary
-/

/--
**Summary Theorem:**
Erdős Problem #651 asked whether f_k(n) > (1 + c_k)^n for all k ≥ 2.

The answer is:
1. YES for k = 2 (planar case) - Erdős-Szekeres
2. NO for k ≥ 3 - Pohoata-Zakharov (2022)
-/
theorem erdos_651_summary :
    (hasExponentialLowerBound 2) ∧
    (¬ hasExponentialLowerBound 3) ∧
    (∀ k, k ≥ 3 → ¬ hasExponentialLowerBound k) :=
  ⟨exponential_holds_k2, no_exponential_lower_bound_k3, no_exponential_lower_bound_k_ge_3⟩

end Erdos651
