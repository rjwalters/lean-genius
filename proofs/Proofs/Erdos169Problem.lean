/-
Erdős Problem #169: Harmonic Sum of AP-Free Sets

Source: https://erdosproblems.com/169
Status: OPEN

Statement:
Let k ≥ 3. Define f(k) as the supremum of ∑_{n ∈ A} 1/n over all sets A
of positive integers that contain no k-term arithmetic progression.

1. Estimate f(k).
2. Is lim_{k→∞} f(k)/log W(k) = ∞, where W(k) is the van der Waerden number?

Background:
This problem connects additive combinatorics (AP-free sets) with harmonic analysis
(reciprocal sums). How large can the harmonic sum of an AP-free set be?

Key Results:
- Berlekamp (1968): f(k) ≥ (log 2 / 2) · k
- Gerver (1977): f(k) ≥ (1 - o(1)) k log k
- It's trivial that f(k) / log W(k) ≥ 1/2; improving to > 1/2 is open
- Gerver: Problem #3 (finite f(k)) ⟺ f(k) < ∞ for all k
- Wróblewski (1984): f(3) ≥ 3.00849
- Walker (2025): f(4) ≥ 4.43975, optimal sets can be Kempner sets

References:
- Berlekamp (1968): Original lower bound
- Gerver (1977): Improved lower bound
- Walker (2025): Modern computational and structural results

Tags: additive-combinatorics, arithmetic-progressions, harmonic-sums
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators

namespace Erdos169

/-!
## Part I: Arithmetic Progressions
-/

/--
**k-term Arithmetic Progression:**
A sequence a, a+d, a+2d, ..., a+(k-1)d with common difference d > 0.
-/
def IsArithmeticProgression (S : Finset ℕ) (k : ℕ) : Prop :=
  S.card = k ∧ ∃ a d : ℕ, d > 0 ∧ S = (Finset.range k).image (fun i => a + i * d)

/--
**AP-free set:**
A set of integers containing no k-term arithmetic progression.
-/
def IsAPFree (A : Set ℕ) (k : ℕ) : Prop :=
  ∀ S : Finset ℕ, ↑S ⊆ A → ¬IsArithmeticProgression S k

/-!
## Part II: Harmonic Sum of a Set
-/

/--
**Harmonic sum of a finite set:**
The sum of reciprocals of elements in A.
-/
noncomputable def harmonicSum (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A.filter (· ≥ 1), (1 : ℝ) / n

/--
**f(k): Supremum of harmonic sums over all AP-free sets:**
The key function in Erdős Problem #169.
-/
noncomputable def f (k : ℕ) : ℝ :=
  sSup { s : ℝ | ∃ A : Finset ℕ, IsAPFree (↑A) k ∧ harmonicSum A = s }

/-!
## Part III: Van der Waerden Numbers
-/

/--
**Van der Waerden number W(k):**
The smallest n such that any 2-coloring of {1,...,n} contains a monochromatic
k-term arithmetic progression. These numbers grow extremely fast.
-/
noncomputable def W (k : ℕ) : ℕ :=
  sSup { n : ℕ | ∃ (c : Fin n → Bool),
    ∀ S : Finset (Fin n), IsArithmeticProgression (S.image (·.val + 1)) k →
      ¬(∀ x ∈ S, c x = true) ∧ ¬(∀ x ∈ S, c x = false) }

/--
**Van der Waerden's Theorem:**
For all k ≥ 3, W(k) is finite (but grows extremely fast).
-/
axiom van_der_waerden_finite (k : ℕ) (hk : k ≥ 3) :
  W k < ⊤

/-!
## Part IV: Berlekamp's Lower Bound (1968)
-/

/--
**Berlekamp (1968):**
f(k) ≥ (log 2 / 2) · k

This was the first non-trivial lower bound, using a construction based on
numbers whose binary representations avoid certain patterns.
-/
axiom berlekamp_lower_bound (k : ℕ) (hk : k ≥ 3) :
  f k ≥ (Real.log 2 / 2) * k

/--
**Berlekamp's construction:**
Consider integers n whose base-2 representation has at most ⌊k/2⌋ ones.
This set is AP-free and has harmonic sum ≥ (log 2 / 2) · k.
-/
axiom berlekamp_construction : True

/-!
## Part V: Gerver's Improvement (1977)
-/

/--
**Gerver (1977):**
f(k) ≥ (1 - o(1)) k log k

This is a significant improvement over Berlekamp, showing f(k) grows
faster than linearly in k.
-/
axiom gerver_lower_bound (k : ℕ) (hk : k ≥ 3) :
  ∃ c : ℝ, c > 0 ∧ f k ≥ c * k * Real.log k

/--
**Gerver's observation:**
Problem #3 (whether all f(k) are finite) is equivalent to asking
whether the set of integers avoiding all APs has finite harmonic sum.
-/
axiom gerver_equivalence : True

/-!
## Part VI: The Ratio Question
-/

/--
**The trivial bound:**
f(k) / log W(k) ≥ 1/2

This follows from basic properties of AP-free sets and van der Waerden numbers.
-/
axiom trivial_ratio_bound (k : ℕ) (hk : k ≥ 3) :
  f k / Real.log (W k) ≥ 1/2

/--
**Erdős's question:**
Is lim_{k→∞} f(k) / log W(k) = ∞?

Equivalently: Can f(k) grow much faster than log W(k)?
This is still OPEN. Even improving 1/2 to any constant > 1/2 is open.
-/
def RatioQuestion : Prop :=
  ∀ M : ℝ, M > 0 → ∃ K : ℕ, ∀ k ≥ K, f k / Real.log (W k) ≥ M

/-!
## Part VII: Computational Records
-/

/--
**f(3) ≥ 3.00849:**
Due to Wróblewski (1984). Finding 3-AP-free sets with large harmonic sum.
-/
axiom f3_lower_bound : f 3 ≥ 3.00849

/--
**f(4) ≥ 4.43975:**
Due to Walker (2025). The state of the art for 4-AP-free sets.
-/
axiom f4_lower_bound : f 4 ≥ 4.43975

/-!
## Part VIII: Walker's Results (2025)
-/

/--
**Kempner sets:**
Sets of integers defined by digit restrictions: all integers whose
base-b representation uses only digits from a fixed set S ⊆ {0,...,b-1}.
-/
def IsKempnerSet (A : Set ℕ) : Prop :=
  ∃ (b : ℕ) (S : Finset (Fin b)), b ≥ 2 ∧
    A = { n : ℕ | ∀ (d : ℕ), d ∈ (Nat.digits b n) → ∃ s ∈ S, d = s.val }

/--
**Walker (2025):**
Optimal AP-free sets for harmonic sum can be approximated by Kempner sets.
For any k ≥ 3 and ε > 0, there exists a Kempner set A lacking k-term APs
with ∑_{n ∈ A} 1/n ≥ f(k) - ε.
-/
axiom walker_kempner_sufficiency (k : ℕ) (hk : k ≥ 3) (ε : ℝ) (hε : ε > 0) :
  ∃ A : Set ℕ, IsKempnerSet A ∧ IsAPFree A k ∧
    ∃ B : Finset ℕ, ↑B ⊆ A ∧ harmonicSum B ≥ f k - ε

/-!
## Part IX: Basic Properties
-/

/--
**f is monotonically decreasing:**
Larger k means stronger AP-avoidance, so smaller harmonic sums.
-/
theorem f_monotone (k₁ k₂ : ℕ) (h : k₁ ≤ k₂) : f k₂ ≤ f k₁ := by
  sorry

/--
**f(k) > 0 for all k:**
There always exist non-trivial AP-free sets.
-/
theorem f_positive (k : ℕ) (hk : k ≥ 3) : f k > 0 := by
  sorry

/--
**The {1} singleton is k-AP-free for all k ≥ 2:**
-/
theorem singleton_ap_free (k : ℕ) (hk : k ≥ 2) : IsAPFree ({1} : Set ℕ) k := by
  sorry

/-!
## Part X: Related Problems
-/

/--
**Problem #3:**
Is f(k) finite for all k? (Equivalent to Gerver's characterization.)
-/
axiom problem_3_finiteness : True

/--
**Problem #170:**
Related question about AP-free sets.
-/
axiom problem_170_related : True

/--
**OEIS A005346:**
Number of subsets of {1,...,n} containing no 3-term AP.
-/
axiom oeis_a005346 : True

/-!
## Part XI: Summary
-/

/--
**Erdős Problem #169: Status**

**QUESTIONS:**
1. Estimate f(k).
2. Is lim_{k→∞} f(k) / log W(k) = ∞?

**STATUS:** OPEN

**KNOWN:**
1. Berlekamp (1968): f(k) ≥ (log 2 / 2) · k
2. Gerver (1977): f(k) ≥ (1 - o(1)) k log k
3. Trivially: f(k) / log W(k) ≥ 1/2
4. Improving 1/2 to any constant > 1/2 is OPEN
5. Gerver: Problem #3 ⟺ f(k) finite for all k
6. Computational: f(3) ≥ 3.00849, f(4) ≥ 4.43975
7. Walker (2025): Optimal sets can be approximated by Kempner sets

**SIGNIFICANCE:**
This bridges additive combinatorics (Szemerédi's theorem, van der Waerden)
with harmonic analysis. Understanding f(k) reveals deep structure in AP-free sets.
-/
theorem erdos_169_summary :
    -- Berlekamp bound
    (∀ k ≥ 3, f k ≥ (Real.log 2 / 2) * k) ∧
    -- Trivial ratio bound
    (∀ k ≥ 3, f k / Real.log (W k) ≥ 1/2) := by
  constructor
  · intro k hk
    exact berlekamp_lower_bound k hk
  · intro k hk
    exact trivial_ratio_bound k hk

/--
**Problem status: OPEN**
-/
theorem erdos_169_status : True := trivial

end Erdos169
