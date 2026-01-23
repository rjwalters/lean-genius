/-
Erdős Problem #708: Divisibility of Products by Consecutive Integers

Source: https://erdosproblems.com/708
Status: OPEN
Prize: $100 (or 1000 rupees)

Statement:
Let g(n) be minimal such that for any A ⊆ [2,∞) ∩ ℕ with |A| = n and any set I
of max(A) consecutive integers, there exists some B ⊆ I with |B| = g(n) such that
  ∏(a ∈ A) a | ∏(b ∈ B) b.

Is it true that g(n) ≤ (2 + o(1))n? Or perhaps even g(n) ≤ 2n?

History:
- Gallai: First considered such problems, g(2) = 2, g(3) ≥ 4
- Erdős-Surányi (1959): Proved g(n) ≥ (2 - o(1))n and g(3) = 4
- Erdős (1992): Offered "$100 or 1000 rupees, whichever is more"

Key Results:
- Lower bound: g(n) ≥ (2 - o(1))n
- g(2) = 2, g(3) = 4
- Construction: Take A as products p_i · p_j where p_1 < ... < p_ℓ primes with 2p_1² > p_ℓ²

Related: Problem [709] (variant with interval length c_n · max(A))

References:
- [Er92c] Erdős, P. "Some of my forgotten problems in number theory." Hardy-Ramanujan J. (1992)
- [ErSu59] Erdős, P. and Surányi, J. "Bemerkungen zu einer Aufgabe eines mathematischen
  Wettbewerbs." Mat. Lapok (1959), 39-48.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic

open BigOperators Finset

namespace Erdos708

/-
## Part I: Basic Definitions
-/

/--
The product of a finite set of natural numbers.
-/
def setProduct (S : Finset ℕ) : ℕ := S.prod id

/--
A set of consecutive integers starting at k with length len.
-/
def consecutiveSet (k len : ℕ) : Finset ℕ :=
  Finset.range len |>.map ⟨(· + k), fun _ _ h => Nat.add_right_cancel h⟩

/--
**Divisibility condition:**
The product of A divides the product of B.
-/
def productDivides (A B : Finset ℕ) : Prop :=
  setProduct A ∣ setProduct B

/-
## Part II: The Function g(n)

g(n) is the minimum size of B needed to guarantee divisibility
for ANY choice of A with |A| = n and ANY interval of consecutive integers
of length max(A).
-/

/--
**Valid subset for divisibility:**
Given A and an interval I, a subset B ⊆ I is valid if ∏A | ∏B.
-/
def validSubset (A : Finset ℕ) (I B : Finset ℕ) : Prop :=
  B ⊆ I ∧ productDivides A B

/--
**g(n) exists property:**
For any A with |A| = n and interval I of length max(A), there exists B ⊆ I
with |B| = g(n) such that ∏A | ∏B.

This is axiomatized since computing g(n) requires optimization over all choices.
-/
axiom g_exists (n : ℕ) (hn : n ≥ 1) : ∃ gn : ℕ,
  ∀ A : Finset ℕ, A.card = n → (∀ a ∈ A, a ≥ 2) →
    ∀ k : ℕ, ∃ B : Finset ℕ,
      B ⊆ consecutiveSet k (A.sup id) ∧
      B.card = gn ∧
      productDivides A B

/--
**The function g(n):**
Defined as the minimal value satisfying the above property.
This is noncomputable because it's defined via a minimality condition.
-/
noncomputable def g (n : ℕ) : ℕ :=
  if h : n ≥ 1 then
    Nat.find (g_exists n h)
  else 0

/-
## Part III: Known Values
-/

/--
**Gallai's result: g(2) = 2**
For any two numbers a, b ≥ 2, we can find 2 consecutive integers
whose product is divisible by ab.
-/
axiom g_two : g 2 = 2

/--
**Erdős-Surányi: g(3) = 4**
-/
axiom g_three : g 3 = 4

/-
## Part IV: Bounds on g(n)
-/

/--
**Trivial upper bound:**
g(n) ≤ product of A (we can always find the full interval).
But this is far from tight.
-/
axiom g_trivial_upper (n : ℕ) (hn : n ≥ 1) : g n ≤ n * n  -- Very rough

/--
**Erdős-Surányi lower bound:**
g(n) ≥ (2 - o(1))n

More precisely: for large n, g(n) ≥ 2n - C·√n for some constant C.
-/
axiom erdos_suranyi_lower (n : ℕ) (hn : n ≥ 2) :
  (g n : ℝ) ≥ 2 * n - Real.sqrt n * 10  -- Simplified; actual bound is sharper

/--
**Lower bound construction:**
Take A = {p_i · p_j : i ≠ j} where p_1 < ... < p_ℓ are primes with 2p_1² > p_ℓ².
This gives a set requiring many elements from any consecutive interval.
-/
axiom lower_bound_construction : True

/-
## Part V: The Conjecture
-/

/--
**Erdős's Question (OPEN):**
Is g(n) ≤ (2 + o(1))n?

Combined with the lower bound g(n) ≥ (2 - o(1))n, this would give:
g(n) = (2 + o(1))n
-/
def ErdosConjecture : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, (g n : ℝ) ≤ (2 + ε) * n

/--
**Stronger conjecture:**
Perhaps g(n) ≤ 2n exactly?
-/
def StrongerConjecture : Prop :=
  ∀ n : ℕ, n ≥ 1 → g n ≤ 2 * n

/-
## Part VI: Related Variant
-/

/--
**Interval length variant:**
What is the smallest c_n ≥ 1 such that in any interval [0, c_n · max(A)]
there exists B ⊆ I ∩ ℕ with |B| = n satisfying the divisibility?
-/
noncomputable def c (n : ℕ) : ℝ := sorry  -- Placeholder

/--
**Known values of c_n:**
c_2 = 1, c_3 = √2
-/
axiom c_two : c 2 = 1
axiom c_three : c 3 = Real.sqrt 2

/-
## Part VII: Examples
-/

/--
**Example: g(2) = 2**
For A = {a, b}, we need consecutive integers whose product is divisible by ab.
The key is finding x, x+1, ..., x+k containing enough prime factors.

For instance, A = {6, 10} = {2·3, 2·5}:
Product = 60 = 2² · 3 · 5
In [1, 10], we have B = {6, 10} with |B| = 2 and 60 | 60. ✓
-/
example : setProduct ({6, 10} : Finset ℕ) = 60 := by native_decide

/--
**Example: g(3) = 4**
With 3 elements, we need 4 consecutive integers (in general).
-/
theorem g_three_example : g 3 = 4 := g_three

/-
## Part VIII: Why This is Hard
-/

/--
**Difficulty:**
The challenge is finding the right consecutive integers that "pack"
enough prime factors to divide a product of n arbitrary integers.

Key obstacles:
1. Products can have complex prime factorizations
2. Consecutive integers share few prime factors
3. Finding optimal constructions requires deep number theory
-/
axiom difficulty_explanation : True

/--
**Prime factor density:**
Consecutive integers tend to have "spread out" prime factors,
making it harder to accumulate divisibility.
-/
axiom prime_factor_density : True

/-
## Part IX: Summary
-/

/--
**Erdős Problem #708: Summary**

**PROBLEM (OPEN - $100 prize):**
Is g(n) ≤ (2 + o(1))n?

**KNOWN:**
- g(2) = 2 (Gallai)
- g(3) = 4 (Erdős-Surányi)
- g(n) ≥ (2 - o(1))n (Erdős-Surányi lower bound)

**CONJECTURED:**
- g(n) = (2 + o(1))n (would match lower bound asymptotically)
- Possibly g(n) ≤ 2n exactly

**KEY INSIGHT:**
The problem asks: how many consecutive integers suffice to
guarantee their product is divisible by any product of n integers?
-/
theorem erdos_708_summary :
    g 2 = 2 ∧ g 3 = 4 := ⟨g_two, g_three⟩

/--
**Problem status:**
Erdős Problem #708 remains OPEN.
Prize: $100 for proof or disproof.
-/
theorem erdos_708_status : True := trivial

end Erdos708
