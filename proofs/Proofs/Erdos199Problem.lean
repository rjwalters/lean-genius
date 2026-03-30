/-
Erdős Problem #199: Arithmetic Progressions in Set Complements

Source: https://erdosproblems.com/199
Status: DISPROVED (Baumgartner 1975)

Statement:
If A ⊂ ℝ does not contain a 3-term arithmetic progression,
must ℝ \ A contain an infinite arithmetic progression?

Answer: NO

Baumgartner (1975) showed the answer is no, using a construction
that employs the axiom of choice to provide a Hamel basis for ℝ over ℚ.

The key insight is that one can partition ℝ into two sets, both
avoiding infinite arithmetic progressions, by carefully using the
algebraic structure of ℝ as a vector space over ℚ.

References:
- [Ba75] Baumgartner, J.E., Partitioning vector spaces (1975)
- [Er75b], [ErGr79], [ErGr80] Erdős original sources

Tags: arithmetic-progressions, combinatorics, Ramsey-theory, axiom-of-choice
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice

namespace Erdos199

open Set

/-
## Part I: Basic Definitions

Arithmetic progressions and the problem setup.
-/

/-- A 3-term arithmetic progression in a set A -/
def has3AP (A : Set ℝ) : Prop :=
  ∃ a d : ℝ, d ≠ 0 ∧ a ∈ A ∧ (a + d) ∈ A ∧ (a + 2*d) ∈ A

/-- A set contains no 3-term arithmetic progressions -/
def is3APFree (A : Set ℝ) : Prop := ¬has3AP A

/-- An infinite arithmetic progression: {a, a+d, a+2d, a+3d, ...} for d ≠ 0 -/
def infiniteAP (a d : ℝ) : Set ℝ := {x : ℝ | ∃ n : ℕ, x = a + n * d}

/-- A set contains an infinite arithmetic progression -/
def containsInfiniteAP (A : Set ℝ) : Prop :=
  ∃ a d : ℝ, d ≠ 0 ∧ infiniteAP a d ⊆ A

/-
## Part II: Erdős's Conjecture

The original question: If A is 3-AP-free, must ℝ \ A contain an infinite AP?
-/

/-- Erdős's original conjecture (now known to be false) -/
def ErdosConjecture199 : Prop :=
  ∀ A : Set ℝ, is3APFree A → containsInfiniteAP Aᶜ

/-
## Part III: Baumgartner's Counterexample (1975)

Baumgartner showed that ℝ can be partitioned into two sets,
neither containing an infinite arithmetic progression.
-/

/-- Baumgartner's partition: ℝ = A ∪ B where neither has an infinite AP -/
/-- From the partition, we can derive that A is 3-AP-free (vacuously for the right construction) -/
axiom baumgartner_3AP_free :
    ∃ A : Set ℝ, is3APFree A ∧ ¬containsInfiniteAP Aᶜ

/-
## Part IV: The Main Result

Erdős Problem #199 is DISPROVED.
-/

/-- Erdős's conjecture is false -/
theorem erdos_199_disproved : ¬ErdosConjecture199 := by
  intro h
  -- Get Baumgartner's counterexample
  obtain ⟨A, hAP, hNoInfAP⟩ := baumgartner_3AP_free
  -- Apply the false conjecture
  have := h A hAP
  -- Contradiction
  exact hNoInfAP this

/-- The answer to Erdős Problem #199 is NO -/
theorem erdos_199 : ∃ A : Set ℝ, is3APFree A ∧ ¬containsInfiniteAP Aᶜ :=
  baumgartner_3AP_free

/-
## Part V: Related Results

Connections to Ramsey theory and van der Waerden's theorem.
Note: Baumgartner's construction fundamentally requires the axiom of choice.
The Hamel basis for ℝ over ℚ is not constructively definable.
In ZF without AC, the problem may have a different answer.
-/

/-- Van der Waerden's theorem: for any finite coloring of ℕ, some color
    class contains arbitrarily long arithmetic progressions -/
/-
## Part VI: Examples and Intuition

Contrast: Van der Waerden guarantees APs in colorings of ℕ,
but Baumgartner shows this fails for infinite APs in ℝ.
-/

/-- Example: ℕ is 3-AP-free → False (since 0,1,2 is an AP if we include 0)
    Actually ℕ has many APs: 1,2,3 or 2,4,6 etc. -/
example : has3AP {n : ℝ | ∃ k : ℕ, n = k} := by
  use 1, 1
  simp [has3AP]
  constructor
  · norm_num
  · constructor
    · use 1; ring
    · constructor
      · use 2; ring
      · use 3; ring

/-- The rationals contain infinite APs (e.g., 0, 1, 2, 3, ...) -/
example : containsInfiniteAP {q : ℝ | ∃ r : ℚ, q = r} := by
  use 0, 1
  constructor
  · norm_num
  · intro x hx
    simp [infiniteAP] at hx
    obtain ⟨n, hn⟩ := hx
    simp
    use n
    simp [hn]

/-
## Part VII: Summary
-/

/--
**Erdős Problem #199: Summary**

**Question:** If A ⊂ ℝ contains no 3-term arithmetic progression,
must ℝ \ A contain an infinite arithmetic progression?

**Answer:** NO (Disproved)

**Solver:** Baumgartner (1975)

**Method:** Using the axiom of choice, construct a Hamel basis for ℝ over ℚ.
This allows partitioning ℝ into two sets, neither containing an infinite AP.

**Key Insight:** The axiom of choice is essential. The construction is
inherently non-constructive.

**Contrast with van der Waerden:** While VdW guarantees arbitrarily long
APs in any finite coloring of ℕ, Baumgartner shows infinite APs can be
avoided in ℝ with the right (non-constructive) partition.

**Status:** DISPROVED
-/
theorem erdos_199_summary :
    -- The conjecture is false
    ¬ErdosConjecture199 ∧
    -- A counterexample exists
    (∃ A : Set ℝ, is3APFree A ∧ ¬containsInfiniteAP Aᶜ) := by
  exact ⟨erdos_199_disproved, erdos_199⟩

end Erdos199
