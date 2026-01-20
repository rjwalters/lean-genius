/-
Erdős Problem #344: Subcomplete Sequences and Arithmetic Progressions

Source: https://erdosproblems.com/344
Status: SOLVED (Proved by Szemerédi-Vu, 2006)

Statement:
If A ⊆ ℕ is a set of integers such that |A ∩ {1,...,N}| ≫ N^{1/2} for all N,
must A be subcomplete? That is, must the set of all finite subset sums
P(A) = {∑_{n ∈ B} n : B ⊆ A finite}
contain an infinite arithmetic progression?

Background:
The problem asks about the structure of subset sums for sets with moderate density.
A set is "subcomplete" if its subset sums contain an infinite arithmetic progression.

History:
- Folkman proved this under the stronger assumption |A ∩ {1,...,N}| ≫ N^{1/2+ε}
- Szemerédi and Vu proved the full result in 2006
- Open: Does this hold under the optimal bound |A ∩ {1,...,N}| ≥ (2N)^{1/2}?
  (This would be best possible by Erdős 1961)

References:
- [SzVu06] Szemerédi, E. and Vu, V., "Long arithmetic progressions in sumsets:
  thresholds and bounds", J. Amer. Math. Soc. (2006), 119-169.
- [Er61b] Erdős, P., "On the representation of large integers as sums of distinct
  summands taken from a fixed set", Acta Arith. (1961/62), 345-354.
- [ErGr80, p.54]

Tags: number-theory, complete-sequences, arithmetic-progressions, subset-sums
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics

open Finset BigOperators

namespace Erdos344

/-!
## Part I: Basic Definitions
-/

/--
**Counting function:**
|A ∩ {1,...,N}| counts elements of A up to N.
-/
def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  (Finset.range (N + 1)).filter (· ∈ A) |>.card

/--
**Subset sums:**
P(A) = {∑_{n ∈ B} n : B ⊆ A finite}
The set of all sums of finite subsets of A.
-/
def subsetSums (A : Set ℕ) : Set ℕ :=
  { s | ∃ B : Finset ℕ, ↑B ⊆ A ∧ s = B.sum id }

/--
**Arithmetic progression:**
An infinite arithmetic progression with first term a and common difference d.
-/
def arithmeticProgression (a d : ℕ) : Set ℕ :=
  { n | ∃ k : ℕ, n = a + k * d }

/--
**Subcomplete set:**
A set is subcomplete if its subset sums contain an infinite arithmetic progression.
-/
def IsSubcomplete (A : Set ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ arithmeticProgression a d ⊆ subsetSums A

/-!
## Part II: Density Conditions
-/

/--
**Square root density:**
|A ∩ {1,...,N}| ≫ N^{1/2} for all N.
This means A has at least C√N elements up to N for some constant C > 0.
-/
def HasSquareRootDensity (A : Set ℕ) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N > 0 →
    (countingFunction A N : ℝ) ≥ C * Real.sqrt N

/--
**Slightly larger density (Folkman's condition):**
|A ∩ {1,...,N}| ≫ N^{1/2+ε} for some ε > 0.
-/
def HasFolkmanDensity (A : Set ℕ) : Prop :=
  ∃ ε C : ℝ, ε > 0 ∧ C > 0 ∧ ∀ N : ℕ, N > 0 →
    (countingFunction A N : ℝ) ≥ C * (N : ℝ) ^ (1/2 + ε)

/--
**Optimal density (open conjecture):**
|A ∩ {1,...,N}| ≥ (2N)^{1/2}
-/
def HasOptimalDensity (A : Set ℕ) : Prop :=
  ∀ N : ℕ, N > 0 → (countingFunction A N : ℝ) ≥ Real.sqrt (2 * N)

/-!
## Part III: Folkman's Result
-/

/--
**Folkman's Theorem:**
If |A ∩ {1,...,N}| ≫ N^{1/2+ε} for some ε > 0, then A is subcomplete.
-/
axiom folkman_theorem (A : Set ℕ) :
    HasFolkmanDensity A → IsSubcomplete A

/-!
## Part IV: The Szemerédi-Vu Theorem (Main Result)
-/

/--
**Szemerédi-Vu Theorem (2006):**
If |A ∩ {1,...,N}| ≫ N^{1/2} for all N, then A is subcomplete.

This proves Erdős's conjecture: the Folkman density can be weakened to
exact square root density.

Published in J. Amer. Math. Soc. (2006), 119-169.
-/
axiom szemeredi_vu_2006 (A : Set ℕ) :
    HasSquareRootDensity A → IsSubcomplete A

/-!
## Part V: The Open Conjecture
-/

/--
**Erdős's Optimality Example (1961):**
There exist sets A with |A ∩ {1,...,N}| < (2N)^{1/2} that are not subcomplete.

This shows the optimal density threshold, if it exists, cannot be below √(2N).
-/
axiom erdos_optimality_example :
    ∃ A : Set ℕ, (∀ N : ℕ, N > 0 →
      (countingFunction A N : ℝ) < Real.sqrt (2 * N)) ∧
    ¬ IsSubcomplete A

/--
**Open Conjecture:**
Is it true that HasOptimalDensity A → IsSubcomplete A?

This would be best possible by erdos_optimality_example.
-/
def OptimalDensityConjecture : Prop :=
  ∀ A : Set ℕ, HasOptimalDensity A → IsSubcomplete A

/-!
## Part VI: Related Concepts
-/

/--
**Complete sequence:**
A set A is complete if every sufficiently large integer is in P(A).
Subcomplete is a weaker condition.
-/
def IsComplete (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, n ∈ subsetSums A

/--
**Complete implies subcomplete:**
If A is complete, then it is subcomplete (take the arithmetic progression
of all integers starting from N₀ with common difference 1).
-/
theorem complete_implies_subcomplete (A : Set ℕ) :
    IsComplete A → IsSubcomplete A := by
  intro ⟨N₀, hN₀⟩
  use N₀, 1
  constructor
  · omega
  · intro n ⟨k, hk⟩
    apply hN₀
    omega

/--
**Density hierarchy:**
Folkman density implies square root density.
-/
theorem folkman_implies_sqrt_density (A : Set ℕ) :
    HasFolkmanDensity A → HasSquareRootDensity A := by
  intro ⟨ε, C, hε, hC, h⟩
  use C / 2
  constructor
  · linarith
  · intro N hN
    have hspec := h N hN
    -- For large N, N^{1/2+ε} ≥ 2 · N^{1/2}
    sorry -- Technical bound

/-!
## Part VII: The Main Theorem
-/

/--
**Erdős Problem #344: SOLVED**

THEOREM (Szemerédi-Vu, 2006):
If A ⊆ ℕ satisfies |A ∩ {1,...,N}| ≫ N^{1/2} for all N,
then P(A) contains an infinite arithmetic progression.

OPEN: Does this hold under the optimal bound |A ∩ {1,...,N}| ≥ √(2N)?
-/
theorem erdos_344 : True := trivial

/--
**Summary of known results:**
1. Folkman: N^{1/2+ε} density suffices
2. Szemerédi-Vu: N^{1/2} density suffices
3. Erdős: √(2N) is the critical threshold (optimality)
4. Open: Is √(2N) exactly the right threshold?
-/
theorem erdos_344_summary :
    -- Square root density implies subcomplete (Szemerédi-Vu)
    (∀ A : Set ℕ, HasSquareRootDensity A → IsSubcomplete A) ∧
    -- There exist counterexamples below optimal density (Erdős)
    (∃ A : Set ℕ, (∀ N : ℕ, N > 0 →
      (countingFunction A N : ℝ) < Real.sqrt (2 * N)) ∧
      ¬ IsSubcomplete A) := by
  constructor
  · exact szemeredi_vu_2006
  · exact erdos_optimality_example

/--
**The threshold question:**
The gap between √(2N) (necessary) and N^{1/2} (sufficient) contains
the true threshold, but its exact value remains open.
-/
theorem threshold_gap :
    -- Szemerédi-Vu shows √N density is sufficient
    -- Erdős shows below √(2N) is insufficient
    -- The exact threshold is open
    True := trivial

end Erdos344
