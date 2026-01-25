/-
Erdős Problem #120: The Similarity Problem

Given an infinite set A ⊆ ℝ, must there exist a set E ⊆ ℝ of positive measure that
contains no translated and scaled copy of A (i.e., no set of the form aA + b
where a, b ∈ ℝ and a ≠ 0)?

A "similar copy" of A is any set {a·x + b : x ∈ A} for a ≠ 0.

Known results:
- TRUE for unbounded A or A dense in some interval
- FALSE for all finite sets (Steinhaus, 1920)
- OPEN for most countable sequences converging to 0

Special case: A = {1, 1/2, 1/4, ...} (geometric sequence) is Problem 94 on Green's list.

This is Problem #120 from erdosproblems.com.
$100 prize offered.

Reference: https://erdosproblems.com/120

Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

/-!
# Erdős Problem 120: The Similarity Problem

*Reference:* [erdosproblems.com/120](https://www.erdosproblems.com/120)
-/

open Set MeasureTheory
open Filter

namespace Erdos120

/-- A similar copy of A: the set {a·x + b : x ∈ A} for a ≠ 0 -/
def similarCopy (A : Set ℝ) (a b : ℝ) : Set ℝ :=
  (fun x => a * x + b) '' A

/-- E contains a similar copy of A if aA + b ⊆ E for some a ≠ 0 -/
def containsSimilarCopy (E A : Set ℝ) : Prop :=
  ∃ a b : ℝ, a ≠ 0 ∧ similarCopy A a b ⊆ E

/-- E avoids all similar copies of A -/
def avoidsSimilarCopies (E A : Set ℝ) : Prop :=
  ¬ containsSimilarCopy E A

/-- A set A is a "universal similarity set" if every positive measure set contains
    a similar copy of A -/
def universalSimilaritySet (A : Set ℝ) : Prop :=
  ∀ E : Set ℝ, MeasurableSet E → MeasureTheory.volume E > 0 →
    containsSimilarCopy E A

/-!
## Main Conjecture

Erdős Problem #120: For every infinite A ⊆ ℝ, A is NOT a universal similarity set.
Equivalently, there exists E of positive measure avoiding all similar copies of A.
-/

/-- The main conjecture: Every infinite set is avoidable -/
def similarityConjecture : Prop :=
  ∀ A : Set ℝ, A.Infinite →
    ∃ E : Set ℝ, MeasurableSet E ∧ MeasureTheory.volume E > 0 ∧
      avoidsSimilarCopies E A

/-- Erdős Problem #120 ($100 prize) -/
@[category research open, AMS 28]
theorem erdos_120 : answer(sorry) ↔ similarityConjecture := by
  sorry

/-!
## Known Results
-/

/-- Finite sets are universal similarity sets (Steinhaus, 1920) -/
@[category research solved, AMS 28]
theorem steinhaus_finite (A : Set ℝ) (hA : A.Finite) (hA' : A.Nonempty) :
    universalSimilaritySet A := by
  sorry

/-- Unbounded sets are avoidable -/
@[category research solved, AMS 28]
theorem unbounded_avoidable (A : Set ℝ) (hA : ¬ Bornology.IsBounded A) :
    ∃ E : Set ℝ, MeasurableSet E ∧ MeasureTheory.volume E > 0 ∧
      avoidsSimilarCopies E A := by
  sorry

/-- Sets dense in an interval are avoidable -/
@[category research solved, AMS 28]
theorem dense_in_interval_avoidable (A : Set ℝ) (I : Set ℝ)
    (hI : ∃ a b : ℝ, a < b ∧ I = Ioo a b) (hDense : Dense (A ∩ I) ∧ (A ∩ I).Nonempty) :
    ∃ E : Set ℝ, MeasurableSet E ∧ MeasureTheory.volume E > 0 ∧
      avoidsSimilarCopies E A := by
  sorry

/-!
## Special Case: Geometric Sequences

The case A = {1, 1/2, 1/4, ...} (Problem 94 on Green's list) is particularly important.
-/

/-- The geometric sequence {1, 1/2, 1/4, ...} -/
def geometricSeq : Set ℝ := {x | ∃ n : ℕ, x = (1/2 : ℝ)^n}

/-- Is the geometric sequence avoidable? -/
@[category research open, AMS 28]
theorem erdos_120_geometric : answer(sorry) ↔
    ∃ E : Set ℝ, MeasurableSet E ∧ MeasureTheory.volume E > 0 ∧
      avoidsSimilarCopies E geometricSeq := by
  sorry

/-!
## Structure of the Problem
-/

/-- Key observation: Similar copies preserve ratios -/
-- If A = {a₁, a₂, ...}, then aA + b = {a·a₁ + b, a·a₂ + b, ...}
-- The ratios (aᵢ - aⱼ)/(aₖ - aₗ) are preserved under similarity

/-- For a sequence converging to 0, similar copies cluster near b -/
lemma similar_copy_of_convergent_clusters (A : Set ℝ) (hA : ∃ f : ℕ → ℝ, Tendsto f atTop (nhds 0) ∧ Set.range f ⊆ A)
    (a b : ℝ) (ha : a ≠ 0) :
    ∃ε > 0, ∀ x ∈ similarCopy A a b, |x - b| < ε → x ∈ ball b ε := by
  sorry

/-!
## Measure-Theoretic Aspects
-/

/-- A positive measure set contains intervals of all small lengths -/
-- This is related to the Steinhaus theorem

/-- The Lebesgue density theorem helps analyze this problem -/
-- Points of density 1 in E create constraints on avoiding similar copies

/-!
## Approaches to the Problem
-/

/-- Construction approach: Build E by excluding similar copies iteratively -/
-- Start with [0,1], remove similar copies of A, argue positive measure remains

/-- Probabilistic approach: Random subsets avoid similar copies? -/
-- Consider random constructions like Cantor-type sets

/-- Fourier-analytic approach: Use spectral properties of A -/
-- The Fourier transform of indicator functions might help

/-!
## Related Problems
-/

/-- A weaker question: Must E have measure > c for some universal c > 0? -/
-- Even if E exists, how small can its measure be?

/-- A stronger question: Can E be chosen to be a (countable) union of intervals? -/
-- Can we avoid similar copies with a "nice" set?

/-- Connection to Ramsey theory: Coloring ℝ to avoid monochromatic similar copies -/

end Erdos120

-- Placeholder for main result
theorem erdos_120_placeholder : True := trivial
