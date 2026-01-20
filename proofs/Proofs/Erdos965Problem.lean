/-
Erdős Problem #965: Monochromatic Sums in 2-Colorings of ℝ

Source: https://erdosproblems.com/965
Status: DISPROVED (Answer: NO)

Statement:
Is it true that for any 2-coloring of ℝ, there exists a set A ⊆ ℝ with
cardinality ℵ₁ such that all sums a+b (where a ≠ b and a,b ∈ A) are
the same color?

Answer: NO

The answer is negative. Erdős reported he could prove this false assuming
the continuum hypothesis (CH), using methods from his work with Hajnal and Rado.

Later Results:
- Hindman, Leader, and Strauss (2017): Under CH, for any k ≥ 1, there is a
  2-coloring of ℝ such that for any uncountable A ⊆ ℝ, sums of k distinct
  elements cannot be monochromatic.
- Komjáth (2016) and Soukup-Weiss: Proved the result WITHOUT assuming CH.

References:
- Erdős: "Problems and results in combinatorial number theory" (1975)
- Hindman, Leader, Strauss: "Partition regularity and uncountable reals" (2017)
- Komjáth: "Ramsey-type problems" (2016)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Continuum

open Cardinal Set

namespace Erdos965

/-
## Part I: Basic Definitions
-/

/--
**2-Coloring of ℝ:**
A function from ℝ to Bool (true = Red, false = Blue).
-/
def TwoColoring := ℝ → Bool

/--
**Pairwise sums of a set:**
The set of all sums a + b where a ≠ b and both a, b ∈ A.
-/
def PairwiseSums (A : Set ℝ) : Set ℝ :=
  { x | ∃ a b, a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ x = a + b }

/--
**Monochromatic set:**
A set S is monochromatic under coloring c if all elements have the same color.
-/
def IsMonochromatic (c : TwoColoring) (S : Set ℝ) : Prop :=
  (∀ x ∈ S, c x = true) ∨ (∀ x ∈ S, c x = false)

/--
**Aleph-one (ℵ₁):**
The first uncountable cardinal. This represents the cardinality of
the set of countable ordinals.
-/
def aleph_one : Cardinal := Cardinal.aleph 1

/--
**Has cardinality ℵ₁:**
A set has cardinality exactly ℵ₁.
-/
def HasCardinalityAleph1 (A : Set ℝ) : Prop :=
  Cardinal.mk A = aleph_one

/-
## Part II: The Original Conjecture
-/

/--
**Erdős Conjecture #965:**
For any 2-coloring of ℝ, there exists a set A ⊆ ℝ with cardinality ℵ₁
such that all pairwise sums are monochromatic.
-/
def ErdosConjecture965 : Prop :=
  ∀ c : TwoColoring, ∃ A : Set ℝ,
    HasCardinalityAleph1 A ∧ IsMonochromatic c (PairwiseSums A)

/-
## Part III: The Counterexample (Main Result)
-/

/--
**The Conjecture is FALSE:**
There exists a 2-coloring of ℝ such that no uncountable set has
monochromatic pairwise sums.

Erdős proved this under CH using methods from Erdős-Hajnal-Rado.
Later, Komjáth (2016) and Soukup-Weiss proved it without CH.
-/
axiom counterexample_exists :
  ∃ c : TwoColoring, ∀ A : Set ℝ,
    HasCardinalityAleph1 A → ¬ IsMonochromatic c (PairwiseSums A)

/--
**Erdős Problem #965: DISPROVED**
The answer to the conjecture is NO.
-/
theorem erdos_965_disproved : ¬ ErdosConjecture965 := by
  intro hConj
  obtain ⟨c, hc⟩ := counterexample_exists
  obtain ⟨A, hA_card, hA_mono⟩ := hConj c
  exact hc A hA_card hA_mono

/-
## Part IV: Stronger Results
-/

/--
**Generalized k-sums:**
The set of sums of k distinct elements from A.
-/
def KSums (A : Set ℝ) (k : ℕ) : Set ℝ :=
  { x | ∃ S : Finset ℝ, S.card = k ∧ (∀ s ∈ S, s ∈ A) ∧
    x = S.sum id }

/--
**Hindman-Leader-Strauss (2017) under CH:**
For any k ≥ 1, there exists a 2-coloring such that no uncountable set
has monochromatic k-sums.
-/
axiom hindman_leader_strauss_ch (k : ℕ) (hk : k ≥ 1) :
  -- Under CH
  continuum = aleph_one →
  ∃ c : TwoColoring, ∀ A : Set ℝ,
    A.nontrivial → #A > ℵ₀ → ¬ IsMonochromatic c (KSums A k)

/--
**Komjáth (2016) without CH:**
The result holds without assuming the continuum hypothesis.
-/
axiom komjath_unconditional :
  ∃ c : TwoColoring, ∀ A : Set ℝ,
    HasCardinalityAleph1 A → ¬ IsMonochromatic c (PairwiseSums A)

/--
**The counterexample is unconditional:**
We don't need CH to construct a counterexample.
-/
theorem unconditional_counterexample :
    ∃ c : TwoColoring, ∀ A : Set ℝ,
      HasCardinalityAleph1 A → ¬ IsMonochromatic c (PairwiseSums A) :=
  komjath_unconditional

/-
## Part V: Related Ramsey Properties
-/

/--
**Countable sets are insufficient:**
Note that for COUNTABLE sets, the Ramsey property CAN hold.
The key difficulty is with uncountable sets.
-/
axiom countable_ramsey_possible :
  ∀ c : TwoColoring, ∃ A : Set ℝ,
    A.Countable ∧ A.Infinite ∧ IsMonochromatic c (PairwiseSums A)

/--
**The gap between countable and uncountable:**
The jump from countable to uncountable cardinality changes the
Ramsey behavior fundamentally.
-/
theorem countable_vs_uncountable :
    (∀ c, ∃ A : Set ℝ, A.Countable ∧ A.Infinite ∧
      IsMonochromatic c (PairwiseSums A)) ∧
    (∃ c, ∀ A : Set ℝ, HasCardinalityAleph1 A →
      ¬ IsMonochromatic c (PairwiseSums A)) := by
  constructor
  · exact countable_ramsey_possible
  · exact komjath_unconditional

/-
## Part VI: Connection to Erdős-Hajnal-Rado
-/

/--
**Erdős-Hajnal-Rado methods:**
The original proof by Erdős used partition calculus techniques
developed with Hajnal and Rado in their work on infinite combinatorics.
-/
axiom erdos_hajnal_rado_methods : True

/--
**Partition calculus:**
The broader theory of how to color infinite structures to avoid
or guarantee certain monochromatic patterns.
-/
def PartitionCalculus : Prop :=
  -- Placeholder for the general theory
  True

/-
## Part VII: Summary
-/

/--
**Summary of Erdős Problem #965:**

**Question:**
For any 2-coloring of ℝ, must there exist an uncountable set with
monochromatic pairwise sums?

**Answer:** NO

**Key Results:**
1. Erdős (1975): False under CH using Erdős-Hajnal-Rado methods
2. Komjáth (2016): False without assuming CH
3. Hindman-Leader-Strauss (2017): False for k-sums under CH

**Interpretation:**
Uncountable sets in ℝ are "too large" to guarantee monochromatic
pairwise sums. The Ramsey property fails at the uncountable level.
-/
theorem erdos_965_summary :
    ¬ ErdosConjecture965 ∧
    (∃ c : TwoColoring, ∀ A : Set ℝ,
      HasCardinalityAleph1 A → ¬ IsMonochromatic c (PairwiseSums A)) ∧
    (∀ c, ∃ A : Set ℝ, A.Countable ∧ A.Infinite ∧
      IsMonochromatic c (PairwiseSums A)) := by
  constructor
  · exact erdos_965_disproved
  constructor
  · exact komjath_unconditional
  · exact countable_ramsey_possible

/--
**Final Answer:**
The answer to Erdős Problem #965 is NO.
-/
theorem erdos_965_answer_no : ¬ ErdosConjecture965 := erdos_965_disproved

end Erdos965
