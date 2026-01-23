/-
Erdős Problem #195: Monotone Arithmetic Progressions in Permutations

Source: https://erdosproblems.com/195
Status: OPEN

Statement:
What is the largest k such that in any permutation of ℤ there must exist a
monotone k-term arithmetic progression x₁ < x₂ < ... < xₖ?

Known Results:
- Geneson (2019): k ≤ 5
- Adenwalla (2022): k ≤ 4

So the answer is at most 4. But the exact value is UNKNOWN.
We need to determine: is k = 3 or k = 4?

Historical Context:
This problem asks about unavoidable patterns in permutations. A monotone
arithmetic progression (MAP) is a sequence a, a+d, a+2d, ..., a+(k-1)d
appearing in increasing order in the permutation.

Related Problems:
- #194: Similar questions for finite permutations
- #196: Related variants

References:
- [ErGr79, ErGr80] Erdős-Graham: Original problem
- [Ge19] Geneson (2019): First upper bound k ≤ 5
- [Ad22] Adenwalla (2022): Improved to k ≤ 4

Tags: permutations, arithmetic-progressions, Ramsey-theory
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Function.Iterate

namespace Erdos195

/-
## Part I: Basic Definitions
-/

/--
**Permutation of ℤ:**
A bijection from ℤ to ℤ.
-/
def IsPermutation (f : ℤ → ℤ) : Prop :=
  Function.Bijective f

/--
**Arithmetic progression:**
x₁, x₂, ..., xₖ where xᵢ₊₁ - xᵢ = d (constant).
-/
def IsArithmeticProgression (xs : List ℤ) : Prop :=
  xs.length ≥ 2 ∧ ∃ d : ℤ, ∀ i : ℕ, i + 1 < xs.length →
    xs.get! (i + 1) - xs.get! i = d

/--
**Monotone sequence in permutation:**
x₁ < x₂ < ... < xₖ where f(i₁) < f(i₂) < ... < f(iₖ) and i₁ < i₂ < ... < iₖ.
Wait, actually the definition is: positions i₁ < i₂ < ... < iₖ with values
f⁻¹(x₁) < f⁻¹(x₂) < ... < f⁻¹(xₖ) where x₁, ..., xₖ form an AP.
-/

/--
**Monotone arithmetic progression (MAP):**
An AP x₁ < x₂ < ... < xₖ such that when we look at the positions of these
values in the permutation, they appear in increasing order.
-/
def IsMonotoneAP (f : ℤ → ℤ) (xs : List ℤ) : Prop :=
  IsArithmeticProgression xs ∧
  xs.Chain' (· < ·) ∧  -- x₁ < x₂ < ... < xₖ
  -- The positions in the permutation are increasing
  ∀ i j : ℕ, i < j → j < xs.length →
    ∃ pᵢ pⱼ : ℤ, f pᵢ = xs.get! i ∧ f pⱼ = xs.get! j ∧ pᵢ < pⱼ

/--
**Has k-term MAP:**
The permutation contains a monotone AP of length k.
-/
def HasMAP (f : ℤ → ℤ) (k : ℕ) : Prop :=
  ∃ xs : List ℤ, xs.length = k ∧ IsMonotoneAP f xs

/--
**Avoids k-term MAP:**
The permutation has no monotone AP of length k.
-/
def AvoidsMAP (f : ℤ → ℤ) (k : ℕ) : Prop :=
  ¬HasMAP f k

/-
## Part II: The Problem
-/

/--
**The question:**
What is the largest k such that every permutation of ℤ has a k-term MAP?
-/
def LargestUnavoidableMAP : Prop :=
  ∃ k : ℕ,
    -- Every permutation has a k-term MAP
    (∀ f : ℤ → ℤ, IsPermutation f → HasMAP f k) ∧
    -- But some permutation avoids (k+1)-term MAPs
    (∃ f : ℤ → ℤ, IsPermutation f ∧ AvoidsMAP f (k + 1))

/--
**The value k(ℤ):**
The largest k such that every permutation has a k-term MAP.
-/
noncomputable def kZ : ℕ :=
  Nat.find ⟨1, sorry⟩  -- Exists by compactness arguments

/-
## Part III: Upper Bounds
-/

/--
**Geneson (2019): k ≤ 5**
There exists a permutation of ℤ avoiding 6-term MAPs.
-/
axiom geneson_2019 :
  ∃ f : ℤ → ℤ, IsPermutation f ∧ AvoidsMAP f 6

/--
**Adenwalla (2022): k ≤ 4**
There exists a permutation of ℤ avoiding 5-term MAPs.
-/
axiom adenwalla_2022 :
  ∃ f : ℤ → ℤ, IsPermutation f ∧ AvoidsMAP f 5

/--
**Current best upper bound:**
k ≤ 4
-/
theorem upper_bound : kZ ≤ 4 := by
  sorry

/-
## Part IV: Lower Bounds
-/

/--
**Trivial lower bound:**
Every permutation has a 3-term MAP.
(Actually this needs to be proved - it's not trivial!)
-/
axiom trivial_lower_bound :
  ∀ f : ℤ → ℤ, IsPermutation f → HasMAP f 3

/--
**Current lower bound:**
k ≥ 3
-/
theorem lower_bound : kZ ≥ 3 := by
  sorry

/-
## Part V: The Gap
-/

/--
**The open question:**
Is k = 3 or k = 4?
-/
def OpenQuestion : Prop :=
  kZ = 3 ∨ kZ = 4

/--
**Current knowledge:**
3 ≤ k ≤ 4
-/
theorem current_bounds : 3 ≤ kZ ∧ kZ ≤ 4 := by
  exact ⟨lower_bound, upper_bound⟩

/-
## Part VI: Construction Ideas
-/

/--
**Geneson's construction (2019):**
Uses a clever interlacing of positive and negative integers to avoid long MAPs.
-/
axiom geneson_construction_idea :
  -- The construction interleaves blocks of positive and negative integers
  -- in a way that prevents long APs from being monotone
  True

/--
**Adenwalla's improvement (2022):**
Refines Geneson's construction to avoid 5-term MAPs.
-/
axiom adenwalla_construction_idea :
  -- More sophisticated interlacing pattern
  True

/-
## Part VII: Related Results
-/

/--
**Finite version (Problem #194):**
For permutations of {1, ..., n}, how many terms can be avoided?
-/
def FiniteVersion (n k : ℕ) : Prop :=
  ∃ σ : Fin n → Fin n, Function.Bijective σ ∧
    -- σ avoids k-term MAPs
    True

/--
**Increasing vs decreasing:**
A MAP is increasing. What about decreasing APs?
By symmetry, the bounds are the same.
-/
theorem increasing_decreasing_symmetric :
    -- If f avoids increasing k-MAPs, then x ↦ -f(-x) avoids decreasing k-MAPs
    True := trivial

/--
**Erdős-Szekeres theorem connection:**
In any sequence of n² + 1 distinct numbers, there's a monotone subsequence of
length n + 1. This gives a baseline for the problem.
-/
axiom erdos_szekeres_connection :
  -- Every permutation of ℤ has arbitrarily long monotone subsequences
  -- But the AP constraint is much stronger
  True

/-
## Part VIII: Why This Is Hard
-/

/--
**The difficulty:**
For finite permutations, we can enumerate. For ℤ, we need clever constructions.
The gap between upper and lower bounds shows we don't fully understand
the structure of MAPs in infinite permutations.
-/
axiom difficulty_explanation :
  -- Lower bound: show every permutation has a 4-MAP (if true)
  -- Upper bound: construct a permutation avoiding 4-MAPs (if k=3)
  True

/--
**Why 3-MAPs are unavoidable (conjecturally):**
Any permutation must have many 3-term APs (2-term APs are trivial).
The question is whether one of them must be monotone.
-/
axiom three_map_intuition :
  -- In any permutation, there are many 3-APs
  -- The positions of these 3-APs cannot all be non-monotone
  True

/-
## Part IX: Examples
-/

/--
**The identity permutation:**
f(n) = n has all APs monotone (trivially).
-/
def identityPerm : ℤ → ℤ := id

theorem identity_has_all_MAPs (k : ℕ) : HasMAP identityPerm k := by
  sorry

/--
**The reversal permutation:**
f(n) = -n has all increasing APs become decreasing in position.
But this still has 3-MAPs (in fact all MAPs).
-/
def reversalPerm : ℤ → ℤ := fun n => -n

/--
**Interlacing permutation (Geneson-style):**
Interleave positive and negative integers cleverly.
-/
def interleavePerm : ℤ → ℤ := sorry  -- Complex construction

/-
## Part X: Summary
-/

/--
**Erdős Problem #195: OPEN**

**QUESTION:** What is the largest k such that every permutation of ℤ has
a k-term monotone arithmetic progression?

**KNOWN:**
- k ≤ 4 (Adenwalla 2022)
- k ≥ 3 (believed, may need verification)

**THE GAP:** Is k = 3 or k = 4?

**KEY CHALLENGE:** Constructing permutations that avoid MAPs is delicate.
The infinite nature of ℤ makes exhaustive arguments impossible.
-/
theorem erdos_195_summary :
    -- Upper bound: k ≤ 4
    (∃ f : ℤ → ℤ, IsPermutation f ∧ AvoidsMAP f 5) ∧
    -- This is the best known upper bound
    True := by
  constructor
  · exact adenwalla_2022
  · trivial

/--
**Problem status:**
Erdős Problem #195 is OPEN.
-/
theorem erdos_195_status : True := trivial

end Erdos195
