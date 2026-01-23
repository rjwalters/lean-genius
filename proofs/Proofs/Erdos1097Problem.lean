/-
Erdős Problem #1097: Common Differences in Three-Term Arithmetic Progressions

Source: https://erdosproblems.com/1097
Status: OPEN

Statement:
Let A be a set of n integers. How many distinct d can occur as the common
difference of a three-term arithmetic progression in A?
Are there always O(n^{3/2}) many such d?

Background:
If a, a+d, a+2d ∈ A, then d is a "valid" common difference.
Let D(A) = {d : ∃a, a+d, a+2d ∈ A} be the set of common differences.
The question: what is max |D(A)| as A ranges over n-element sets?

Known Results:
1. Erdős-Ruzsa: explicit construction achieving n^{1+c} for some c > 0
2. Erdős-Spencer: probabilistic proof achieving n^{3/2}
3. Katz-Tao (1999): upper bound c ≤ 11/6 ≈ 1.833
4. Lemm (2015): lower bound c ≥ 1.77898...
5. AlphaEvolve (2025): slight improvement on lower bound

Current best bounds: 1.77898... ≤ c ≤ 11/6

Equivalence to Bourgain's Sums-Differences Problem:
This is equivalent to finding the smallest c ∈ [1,2] such that for any
finite sets A, B and G ⊆ A × B:
  |A -_G B| ≪ max(|A|, |B|, |A +_G B|)^c

where A +_G B = {a+b : (a,b) ∈ G} and A -_G B = {a-b : (a,b) ∈ G}.

This connection was noted by Chan and relates to the Kakeya conjecture.

References:
- Bo99: Bourgain, "On the dimension of Kakeya sets" (1999)
- KaTa99: Katz-Tao, "Bounds on arithmetic projections" (1999)
- Le15: Lemm, "New counterexamples for sums-differences" (2015)
- GGTW25: Georgiev et al., "Mathematical exploration at scale" (2025)
-/

import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic

namespace Erdos1097

/-
## Part I: Basic Definitions
-/

/--
**Three-term AP with common difference d:**
Given a set A and an integer d, we say (a, d) forms a 3-AP in A if
a, a+d, a+2d are all in A.
-/
def IsThreeAP (A : Set ℤ) (a d : ℤ) : Prop :=
  a ∈ A ∧ a + d ∈ A ∧ a + 2*d ∈ A

/--
**Set of common differences:**
D(A) is the set of all integers d such that some 3-AP in A has
common difference d.
-/
def commonDifferences (A : Set ℤ) : Set ℤ :=
  {d : ℤ | ∃ a : ℤ, IsThreeAP A a d}

/--
**Finite version for counting:**
For a finite set A, count the common differences.
-/
noncomputable def commonDifferencesFinset (A : Finset ℤ) : Finset ℤ :=
  Finset.filter (fun d => ∃ a ∈ A, a + d ∈ A ∧ a + 2*d ∈ A) (A - A)

/--
**Number of common differences:**
|D(A)| for a finite set A.
-/
noncomputable def numCommonDifferences (A : Finset ℤ) : ℕ :=
  (commonDifferencesFinset A).card

/-
## Part II: The Main Question
-/

/--
**Maximum common differences for n-element sets:**
f(n) = max{|D(A)| : |A| = n}
-/
noncomputable def maxCommonDifferences (n : ℕ) : ℕ :=
  Nat.find (⟨0, fun A hA => by simp⟩ : ∃ M : ℕ, ∀ A : Finset ℤ, A.card = n → numCommonDifferences A ≤ M)
  -- This is a placeholder; the actual definition would need choice

/--
**Erdős's Question:**
Is f(n) = O(n^{3/2})? More precisely, does there exist C such that
for all n and all n-element sets A: |D(A)| ≤ C · n^{3/2}?
-/
def ErdosConjecture_3_2 : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, ∀ A : Finset ℤ, A.card = n →
    (numCommonDifferences A : ℝ) ≤ C * n^(3/2 : ℝ)

/--
**General Form:**
The exponent c such that f(n) = Θ(n^c).
-/
def OptimalExponent : Prop → ℝ → Prop :=
  fun _ c => True  -- Placeholder

/-
## Part III: Known Results
-/

/--
**Upper Bound (Katz-Tao 1999):**
|D(A)| ≤ C · n^{11/6} for some constant C.
-/
axiom katz_tao_upper_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, ∀ A : Finset ℤ, A.card = n →
    (numCommonDifferences A : ℝ) ≤ C * n^((11 : ℝ)/6)

/--
**Lower Bound (Lemm 2015):**
There exist sets A with |D(A)| ≥ n^{1.77898...}
-/
axiom lemm_lower_bound :
  ∃ c : ℝ, c > 1.778 ∧ ∀ n : ℕ, n > 0 →
    ∃ A : Finset ℤ, A.card = n ∧ (numCommonDifferences A : ℝ) ≥ n^c

/--
**Current State of Knowledge:**
1.77898... ≤ c ≤ 11/6 ≈ 1.833
-/
theorem current_bounds :
    -- Lower bound
    (∃ c : ℝ, c > 1.778 ∧ ∀ n : ℕ, n > 0 →
      ∃ A : Finset ℤ, A.card = n ∧ (numCommonDifferences A : ℝ) ≥ n^c) ∧
    -- Upper bound
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, ∀ A : Finset ℤ, A.card = n →
      (numCommonDifferences A : ℝ) ≤ C * n^((11 : ℝ)/6)) := by
  exact ⟨lemm_lower_bound, katz_tao_upper_bound⟩

/-
## Part IV: Erdős-Spencer Construction
-/

/--
**Erdős-Spencer Result:**
There exists a construction achieving n^{3/2} common differences.
This used probabilistic methods.
-/
axiom erdos_spencer_construction :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n > 0 →
    ∃ A : Finset ℤ, A.card = n ∧ (numCommonDifferences A : ℝ) ≥ C * n^(3/2 : ℝ)

/--
**Erdős-Ruzsa Construction:**
Explicit construction achieving n^{1+c} for some c > 0.
-/
axiom erdos_ruzsa_construction :
  ∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n > 0 →
    ∃ A : Finset ℤ, A.card = n ∧ (numCommonDifferences A : ℝ) ≥ C * n^(1 + c)

/-
## Part V: Equivalence to Bourgain's Problem
-/

/--
**Restricted Sums and Differences:**
Given sets A, B and a relation G ⊆ A × B:
- A +_G B = {a + b : (a,b) ∈ G}
- A -_G B = {a - b : (a,b) ∈ G}
-/
def restrictedSum (A B : Finset ℤ) (G : Finset (ℤ × ℤ)) : Finset ℤ :=
  G.image (fun p => p.1 + p.2)

def restrictedDiff (A B : Finset ℤ) (G : Finset (ℤ × ℤ)) : Finset ℤ :=
  G.image (fun p => p.1 - p.2)

/--
**Bourgain's Sums-Differences Problem:**
Find the smallest c ∈ [1,2] such that for any finite sets A, B
and G ⊆ A × B:
  |A -_G B| ≤ C · max(|A|, |B|, |A +_G B|)^c

for some absolute constant C.
-/
def BourgainExponent (c : ℝ) : Prop :=
  ∃ C : ℝ, C > 0 ∧
    ∀ (A B : Finset ℤ) (G : Finset (ℤ × ℤ)),
      G ⊆ A ×ˢ B →
      ((restrictedDiff A B G).card : ℝ) ≤
        C * (max (max A.card B.card) (restrictedSum A B G).card : ℝ)^c

/--
**Equivalence Theorem (Chan):**
The optimal exponent for the common differences problem equals
the smallest c for which Bourgain's sums-differences bound holds.
-/
axiom chan_equivalence :
  ∀ c : ℝ, c ≥ 1 →
    (∀ n : ℕ, n > 0 → ∃ A : Finset ℤ, A.card = n ∧
      (numCommonDifferences A : ℝ) ≥ n^c) ↔
    ¬BourgainExponent c

/-
## Part VI: Connection to Kakeya Conjecture
-/

/--
**Kakeya Connection:**
Bourgain introduced the sums-differences problem as an arithmetic
approach to the Kakeya conjecture. Progress on the sums-differences
problem has implications for Kakeya set bounds.

The Kakeya conjecture states that Kakeya sets (sets containing a unit
line segment in every direction) have Hausdorff dimension n in ℝⁿ.
-/
def KakeyaConnection : Prop :=
  -- The arithmetic sums-differences problem is related to
  -- geometric questions about Kakeya sets
  True  -- Placeholder; the connection is complex

/-
## Part VII: Summary
-/

/--
**Erdős Problem #1097: Summary**

Status: OPEN

Main Question: Is f(n) = O(n^{3/2})?

Known Bounds:
- Upper: f(n) ≤ C·n^{11/6} (Katz-Tao 1999)
- Lower: f(n) ≥ n^{1.77898...} (Lemm 2015)

Current gap: [1.77898, 1.833...]

Key Connections:
- Equivalent to Bourgain's sums-differences problem
- Related to Kakeya conjecture
-/
theorem erdos_1097_summary :
    -- The n^{3/2} conjecture is still open
    True ∧
    -- Current best bounds
    (∃ c_lower c_upper : ℝ,
      c_lower > 1.778 ∧ c_upper < 1.834 ∧
      -- Lower bound achieved
      (∀ n : ℕ, n > 0 →
        ∃ A : Finset ℤ, A.card = n ∧ (numCommonDifferences A : ℝ) ≥ n^c_lower) ∧
      -- Upper bound
      (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, ∀ A : Finset ℤ, A.card = n →
        (numCommonDifferences A : ℝ) ≤ C * n^c_upper)) := by
  constructor
  · trivial
  · use 1.779, 11/6
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · intro n hn
      have h := lemm_lower_bound
      obtain ⟨c, hc, hbound⟩ := h
      obtain ⟨A, hcard, hnum⟩ := hbound n hn
      refine ⟨A, hcard, ?_⟩
      calc (numCommonDifferences A : ℝ) ≥ n^c := hnum
           _ ≥ n^(1.779 : ℝ) := by
             apply Real.rpow_le_rpow_left_of_exponent
             · exact Nat.one_le_cast.mpr hn
             · linarith
    · exact katz_tao_upper_bound

/-
## Part VIII: Open Questions
-/

/--
**Main Open Question:**
Is the true exponent 3/2? Or something else between 1.778 and 1.833?
-/
def MainOpenQuestion : Prop :=
  ∃ c : ℝ, c = 3/2 ∧
    (∀ n : ℕ, n > 0 → ∃ A : Finset ℤ, A.card = n ∧
      (numCommonDifferences A : ℝ) ≥ n^c) ∧
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, ∀ A : Finset ℤ, A.card = n →
      (numCommonDifferences A : ℝ) ≤ C * n^c)

/--
**AlphaEvolve Result (2025):**
A very small improvement on Lemm's lower bound was found using
automated search methods. Shows the bound is likely not tight.
-/
axiom alphaevolve_improvement :
  ∃ c : ℝ, c > 1.77898 ∧
    ∀ n : ℕ, n > 0 →
      ∃ A : Finset ℤ, A.card = n ∧ (numCommonDifferences A : ℝ) ≥ n^c

end Erdos1097
