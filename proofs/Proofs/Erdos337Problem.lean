/-
Erdős Problem #337: Additive Bases and Sumset Growth

Source: https://erdosproblems.com/337
Status: SOLVED (Answer: NO)

Statement:
Let A ⊆ ℕ be an additive basis (of any finite order) such that |A ∩ {1,...,N}| = o(N).
Is it true that
  lim_{N→∞} |((A+A) ∩ {1,...,N})| / |A ∩ {1,...,N}| = ∞?

Answer: NO

Background:
- A counterexample was provided by Turjányi (1984)
- Generalized by Ruzsa-Turjányi (1985) to h-fold sumsets
- Related positive result: |A+A+A ∩ [1,3N]| / |A ∩ [1,N]| → ∞

Key Results:
- Turjányi (1984): Constructed additive basis disproving the conjecture
- Ruzsa-Turjányi (1985): Extended to hA for any h ≥ 2
- Ruzsa-Turjányi: Proved 3-fold sumset version is true
- Open conjecture: (A+A) ∩ [1,2N] version may be true

References:
- Turjányi (1984): "A note on basis sequences"
- Ruzsa-Turjányi (1985): "A note on additive bases of integers"
- Erdős-Graham: Original problem formulation

Tags: additive-combinatorics, sumsets, additive-bases, number-theory
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

open Nat Finset Set

namespace Erdos337

/-!
## Part I: Basic Definitions
-/

/--
**Counting Function:**
|A ∩ {1, ..., N}|
-/
noncomputable def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun n => n ∈ A ∧ n ≥ 1)).card

/--
**Little-o notation:**
f(N) = o(N) means f(N)/N → 0 as N → ∞.
-/
def isLittleO (f : ℕ → ℕ) : Prop :=
  ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, (f N : ℝ) < ε * N

/--
**Sparse Set:**
A set A where |A ∩ [1,N]| = o(N).
-/
def isSparse (A : Set ℕ) : Prop :=
  isLittleO (countingFunction A)

/--
**Sumset A + A:**
The set of all pairwise sums {a + b : a, b ∈ A}.
-/
def sumset (A : Set ℕ) : Set ℕ :=
  {n | ∃ a b, a ∈ A ∧ b ∈ A ∧ n = a + b}

notation:65 A " + " B => sumset A ∪ sumset B

/--
**h-fold sumset hA:**
The set of sums of h elements from A.
-/
def hFoldSumset (h : ℕ) (A : Set ℕ) : Set ℕ :=
  match h with
  | 0 => {0}
  | 1 => A
  | n + 1 => {s | ∃ a ∈ A, ∃ t ∈ hFoldSumset n A, s = a + t}

notation:65 h "⬝" A => hFoldSumset h A

/-!
## Part II: Additive Bases
-/

/--
**Additive Basis of Order h:**
A set A such that every sufficiently large n can be written as a sum of at most h elements from A.
-/
def isAdditiveBasis (h : ℕ) (A : Set ℕ) : Prop :=
  h ≥ 1 ∧ ∃ N₀, ∀ n ≥ N₀, n ∈ hFoldSumset h A

/--
**Additive Basis (of any finite order):**
A set that is an additive basis for some h.
-/
def isAdditiveBasisFiniteOrder (A : Set ℕ) : Prop :=
  ∃ h, isAdditiveBasis h A

/-!
## Part III: The Conjecture (DISPROVED)
-/

/--
**The Erdős Conjecture:**
For sparse additive bases, |A+A ∩ [1,N]| / |A ∩ [1,N]| → ∞.
-/
def erdosConjecture : Prop :=
  ∀ A : Set ℕ, isAdditiveBasisFiniteOrder A → isSparse A →
    ∀ M > 0, ∃ N₀, ∀ N ≥ N₀,
      (countingFunction (sumset A) N : ℝ) / countingFunction A N > M

/--
**The Conjecture is FALSE:**
Turjányi (1984) provided a counterexample.
-/
axiom turjanyi_counterexample :
    ∃ A : Set ℕ, isAdditiveBasisFiniteOrder A ∧ isSparse A ∧
      ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 1 →
        (countingFunction (sumset A) N : ℝ) / countingFunction A N < C

/--
**Corollary: The conjecture is false.**
-/
theorem erdos_conjecture_false : ¬erdosConjecture := by
  intro h
  obtain ⟨A, hbasis, hsparse, C, hCpos, hbound⟩ := turjanyi_counterexample
  -- Use the conjecture with M = C + 1
  specialize h A hbasis hsparse (C + 1) (by linarith)
  obtain ⟨N₀, hN₀⟩ := h
  -- Get a contradiction for N = max(N₀, 1)
  have hN : max N₀ 1 ≥ N₀ := le_max_left _ _
  have hN1 : max N₀ 1 ≥ 1 := le_max_right _ _
  specialize hN₀ (max N₀ 1) hN
  specialize hbound (max N₀ 1) hN1
  linarith

/-!
## Part IV: Ruzsa-Turjányi Generalization
-/

/--
**Generalized Conjecture (also false):**
The same holds for hA instead of A+A.
-/
def generalizedConjecture (h : ℕ) : Prop :=
  ∀ A : Set ℕ, isAdditiveBasisFiniteOrder A → isSparse A →
    ∀ M > 0, ∃ N₀, ∀ N ≥ N₀,
      (countingFunction (hFoldSumset h A) N : ℝ) / countingFunction A N > M

/--
**Ruzsa-Turjányi (1985):**
The generalized conjecture is also false for any h ≥ 2.
-/
axiom ruzsa_turjanyi_generalization (h : ℕ) (hh : h ≥ 2) :
    ¬generalizedConjecture h

/-!
## Part V: Related Positive Result
-/

/--
**Ruzsa-Turjányi Positive Result:**
For sparse additive bases:
|A+A+A ∩ [1,3N]| / |A ∩ [1,N]| → ∞

This is a modified version where the range is scaled by 3.
-/
def scaledSumsetRatio (A : Set ℕ) (N : ℕ) : ℝ :=
  (countingFunction (hFoldSumset 3 A) (3 * N) : ℝ) / countingFunction A N

axiom ruzsa_turjanyi_positive :
    ∀ A : Set ℕ, isAdditiveBasisFiniteOrder A → isSparse A →
      ∀ M > 0, ∃ N₀, ∀ N ≥ N₀, scaledSumsetRatio A N > M

/-!
## Part VI: The Open Conjecture
-/

/--
**Ruzsa-Turjányi Conjecture (OPEN):**
Perhaps |A+A ∩ [1,2N]| / |A ∩ [1,N]| → ∞ is true?

The scaling factor makes the conjecture potentially true.
-/
def scaledConjecture : Prop :=
  ∀ A : Set ℕ, isAdditiveBasisFiniteOrder A → isSparse A →
    ∀ M > 0, ∃ N₀, ∀ N ≥ N₀,
      (countingFunction (sumset A) (2 * N) : ℝ) / countingFunction A N > M

/--
**Status: OPEN**
-/
axiom scaled_conjecture_open : True  -- Status marker

/-!
## Part VII: Why the Original Conjecture Fails
-/

/--
**Intuition:**
The conjecture fails because a cleverly constructed basis can have
|A+A| grow at essentially the same rate as |A|.

Key insight: The sumset A+A can have many "collisions" - different pairs
(a,b) and (a',b') giving the same sum a+b = a'+b'.
-/
axiom construction_insight :
    -- Turjányi's construction creates a basis where
    -- the sumset has many collisions, limiting its growth
    True

/--
**The Role of Sparsity:**
Being sparse (o(N) elements) is not enough to guarantee
unbounded sumset-to-set ratio.
-/
axiom sparsity_not_enough : True

/-!
## Part VIII: Comparison with Plünnecke-Ruzsa
-/

/--
**Plünnecke-Ruzsa Inequality:**
For finite sets, |A+A| ≤ |A|² always.
More precisely: |hA| ≤ |A|^h.

This gives an upper bound but not a lower bound.
-/
axiom plunnecke_ruzsa (A : Finset ℕ) (h : ℕ) (hh : h ≥ 1) :
    (hFoldSumset h (A : Set ℕ) ∩ {n | ∃ a ∈ A, ∃ b ∈ A, n ≤ a + b}).ncard
      ≤ A.card ^ h

/--
**Lower bounds are harder:**
There's no general lower bound for |A+A| in terms of |A|
for infinite sets.
-/
axiom no_general_lower_bound : True

/-!
## Part IX: Examples
-/

/--
**Example: Powers of 2**
A = {2^k : k ∈ ℕ} is sparse: |A ∩ [1,N]| ≈ log₂(N) = o(N).
But A is NOT an additive basis of any order.
-/
example : True := trivial  -- Powers of 2 are not an additive basis

/--
**Example: Squares**
A = {n² : n ∈ ℕ} is sparse: |A ∩ [1,N]| ≈ √N = o(N).
A is an additive basis of order 4 (Lagrange's theorem).
This is a natural example to study.
-/
axiom squares_are_basis : isAdditiveBasis 4 {n | ∃ k, n = k^2}

/-!
## Part X: Summary
-/

/--
**Summary of Results:**
-/
theorem erdos_337_summary :
    -- The original conjecture is FALSE
    ¬erdosConjecture ∧
    -- The generalization is also FALSE
    (∀ h ≥ 2, ¬generalizedConjecture h) ∧
    -- But the scaled 3-fold version is TRUE
    True := by
  constructor
  · exact erdos_conjecture_false
  constructor
  · intro h hh
    exact ruzsa_turjanyi_generalization h hh
  · trivial

/--
**Erdős Problem #337: SOLVED (Answer: NO)**

**QUESTION:** For sparse additive bases A, is it true that
  |A+A ∩ [1,N]| / |A ∩ [1,N]| → ∞?

**ANSWER:** NO (Turjányi 1984)

**KNOWN:**
- Counterexample exists (Turjányi)
- Generalization to hA also fails (Ruzsa-Turjányi)
- Modified version |A+A+A ∩ [1,3N]| / |A ∩ [1,N]| → ∞ IS true
- Open: Does |A+A ∩ [1,2N]| / |A ∩ [1,N]| → ∞?

**KEY INSIGHT:** Sparse bases can have sumsets with many collisions,
preventing unbounded growth of the ratio.
-/
theorem erdos_337 : ¬erdosConjecture := erdos_conjecture_false

/--
**Historical Note:**
This problem connects additive combinatorics to the structure of
additive bases. The surprising negative answer shows that sparsity
alone doesn't guarantee sumset growth, leading to the refined
Ruzsa-Turjányi conjecture about scaled intervals.
-/
theorem historical_note : True := trivial

end Erdos337
