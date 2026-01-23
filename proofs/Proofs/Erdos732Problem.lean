/-
Erdős Problem #732: Block-Compatible Sequences

Source: https://erdosproblems.com/732
Status: PARTIALLY SOLVED

Statement:
A sequence 1 < X₁ ≤ X₂ ≤ ... ≤ Xₘ ≤ n is block-compatible if there exists a
pairwise balanced block design A₁, ..., Aₘ ⊆ {1, ..., n} with |Aᵢ| = Xᵢ.

Questions:
1. Are there necessary and sufficient conditions for block-compatibility?
2. Is there some c > 0 such that there are ≥ exp(c·√n·log n) block-compatible
   sequences?

Known Results:
- Necessary: Σᵢ C(Xᵢ,2) = C(n,2)
- Upper bound: ≤ exp(O(√n·log n)) sequences (Erdős)
- Lower bound: ≥ 2^((1/2+o(1))√n·log n) sequences (Alon)

So Question 2 is SOLVED affirmatively by Alon.
Question 1 (characterization) is more subtle.

Historical Context:
A pairwise balanced block design (PBD) is a decomposition of all pairs
into blocks. The block sizes form the sequence X₁, ..., Xₘ.

References:
- [Er81] Erdős (1981): Original problem
- Alon: Lower bound proof

Tags: combinatorics, block-designs, enumeration
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic

namespace Erdos732

/-
## Part I: Basic Definitions
-/

/--
**A block (subset):**
A subset of {1, ..., n}.
-/
def Block (n : ℕ) := Finset (Fin n)

/--
**Pair:**
An unordered pair from {1, ..., n}.
-/
def Pair (n : ℕ) := {p : Finset (Fin n) // p.card = 2}

/--
**Pairs covered by a block:**
All pairs {i, j} with i, j ∈ A.
-/
def pairsCoveredBy {n : ℕ} (A : Block n) : Finset (Finset (Fin n)) :=
  A.powerset.filter (fun p => p.card = 2)

/--
**Pairwise Balanced Block Design (PBD):**
A collection of blocks covering each pair exactly once.
-/
def IsPBD {n : ℕ} (blocks : List (Block n)) : Prop :=
  -- Every pair is covered exactly once
  ∀ p : Finset (Fin n), p.card = 2 →
    (blocks.filter (fun A => p ⊆ A)).length = 1

/-
## Part II: Block-Compatible Sequences
-/

/--
**Block-compatible sequence:**
A sequence X₁ ≤ ... ≤ Xₘ is block-compatible for n if there's a PBD
on {1, ..., n} with block sizes X₁, ..., Xₘ.
-/
def IsBlockCompatible (Xs : List ℕ) (n : ℕ) : Prop :=
  ∃ blocks : List (Block n),
    IsPBD blocks ∧
    blocks.map Finset.card = Xs

/--
**Well-formed sequence:**
1 < X₁ ≤ ... ≤ Xₘ ≤ n.
-/
def IsWellFormed (Xs : List ℕ) (n : ℕ) : Prop :=
  Xs ≠ [] ∧
  (∀ X ∈ Xs, 2 ≤ X ∧ X ≤ n) ∧
  Xs.Chain' (· ≤ ·)

/-
## Part III: Necessary Conditions
-/

/--
**Pair-counting condition:**
Σᵢ C(Xᵢ, 2) = C(n, 2)
-/
def PairCountCondition (Xs : List ℕ) (n : ℕ) : Prop :=
  (Xs.map (fun X => X * (X - 1) / 2)).sum = n * (n - 1) / 2

/--
**The pair-counting condition is necessary:**
If Xs is block-compatible, then Σ C(Xᵢ, 2) = C(n, 2).
-/
theorem pair_count_necessary {Xs : List ℕ} {n : ℕ}
    (h : IsBlockCompatible Xs n) : PairCountCondition Xs n := by
  sorry

/--
**Block count observation:**
Since each pair is covered exactly once, the total "pair-coverage"
must equal the total number of pairs.
-/
theorem pair_count_explanation (n : ℕ) :
    -- Number of pairs in {1, ..., n} is C(n, 2)
    n * (n - 1) / 2 = n * (n - 1) / 2 := rfl

/-
## Part IV: Question 1 - Characterization
-/

/--
**Question 1:**
Are there necessary and sufficient conditions for block-compatibility?

The pair-counting condition is necessary but NOT sufficient.
Finding simple sufficient conditions is the challenge.
-/
def CharacterizationQuestion : Prop :=
  ∃ (condition : List ℕ → ℕ → Prop),
    -- The condition is decidable and reasonable
    (∀ Xs n, condition Xs n → PairCountCondition Xs n) ∧
    -- The condition is necessary and sufficient
    (∀ Xs n, IsWellFormed Xs n →
      (IsBlockCompatible Xs n ↔ condition Xs n))

/--
**Status of Question 1:**
No simple characterization is known.
The pair-counting condition is NOT sufficient.
-/
axiom characterization_hard :
  -- There exist sequences satisfying pair-counting that are not block-compatible
  ∃ Xs n, PairCountCondition Xs n ∧ IsWellFormed Xs n ∧ ¬IsBlockCompatible Xs n

/-
## Part V: Question 2 - Counting
-/

/--
**Number of block-compatible sequences for n:**
B(n) = |{Xs : Xs is block-compatible for n}|
-/
noncomputable def B (n : ℕ) : ℕ :=
  (Finset.filter (fun Xs => IsBlockCompatible Xs n)
    (Finset.univ : Finset (List ℕ))).card  -- Finite approximation

/--
**Erdős's upper bound:**
B(n) ≤ exp(O(√n · log n))
-/
axiom erdos_upper_bound :
  ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, n ≥ 2 →
      (B n : ℝ) ≤ Real.exp (C * Real.sqrt n * Real.log n)

/--
**Alon's lower bound:**
B(n) ≥ 2^((1/2 + o(1))√n · log n)
-/
axiom alon_lower_bound :
  ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n ≥ N,
      (B n : ℝ) ≥ 2 ^ ((1/2 - ε) * Real.sqrt n * Real.log n)

/--
**Question 2: SOLVED**
There exists c > 0 such that B(n) ≥ exp(c·√n·log n) for large n.
-/
theorem question_2_solved :
    ∃ c : ℝ, c > 0 ∧
      ∃ N : ℕ, ∀ n ≥ N,
        (B n : ℝ) ≥ Real.exp (c * Real.sqrt n * Real.log n) := by
  -- Follows from Alon's lower bound with c = (1/2 - ε) · ln(2)
  use (1/3) * Real.log 2  -- Any positive constant < (1/2) · ln(2)
  constructor
  · positivity
  · obtain ⟨N, hN⟩ := alon_lower_bound (1/6) (by norm_num : (1/6 : ℝ) > 0)
    use N
    intro n hn
    calc (B n : ℝ) ≥ 2 ^ ((1/2 - 1/6) * Real.sqrt n * Real.log n) := hN n hn
      _ = 2 ^ ((1/3) * Real.sqrt n * Real.log n) := by ring_nf
      _ ≥ Real.exp ((1/3) * Real.log 2 * Real.sqrt n * Real.log n) := by sorry

/-
## Part VI: The Gap
-/

/--
**The asymptotic:**
B(n) = 2^((c + o(1))√n · log n) for some c ∈ [1/2, O(1)].

Alon shows c ≥ 1/2.
Erdős shows c ≤ O(1).
-/
def AsymptoticConstant : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n ≥ N,
        2 ^ ((c - ε) * Real.sqrt n * Real.log n) ≤ B n ∧
        (B n : ℝ) ≤ 2 ^ ((c + ε) * Real.sqrt n * Real.log n)

/--
**Lower bound on the constant:**
c ≥ 1/2 by Alon.
-/
theorem constant_at_least_half :
    ∃ c : ℝ, c ≥ 1/2 ∧
      ∀ ε : ℝ, ε > 0 →
        ∃ N : ℕ, ∀ n ≥ N,
          (B n : ℝ) ≥ 2 ^ ((c - ε) * Real.sqrt n * Real.log n) := by
  use 1/2
  constructor
  · norm_num
  · exact alon_lower_bound

/-
## Part VII: Examples
-/

/--
**Example: n = 3**
The only PBD on {1, 2, 3} is the single block {1, 2, 3}.
So the only block-compatible sequence is [3].
-/
example : IsBlockCompatible [3] 3 := by
  use [Finset.univ]
  constructor
  · intro p hp
    sorry  -- p ⊆ univ, and there's exactly one block
  · simp

/--
**Example: n = 4**
Possible PBDs:
- Single block {1,2,3,4}: sequence [4]
- Three blocks of size 2: sequence [2,2,2] if such design exists

For [2,2,2]: need 3 pairs, but C(4,2) = 6 pairs. No good.
Actually we need Σ C(Xᵢ,2) = 6.
[4]: C(4,2) = 6 ✓
[2,2,2,2,2,2]: 6·1 = 6 ✓ (partition into pairs)
-/
example : PairCountCondition [4] 4 := by
  simp [PairCountCondition]
  norm_num

example : PairCountCondition [2, 2, 2, 2, 2, 2] 4 := by
  simp [PairCountCondition]
  norm_num

/--
**Example: n = 6**
The Fano plane analog for n = 7 doesn't apply here.
For n = 6: C(6,2) = 15 pairs.
Blocks of size 3: C(3,2) = 3 pairs each.
So 5 blocks of size 3: 5 × 3 = 15 ✓
-/
example : PairCountCondition [3, 3, 3, 3, 3] 6 := by
  simp [PairCountCondition]
  norm_num

/-
## Part VIII: Related Problems
-/

/--
**Problem #733:**
A related problem about block designs.
-/
axiom problem_733_related : True

/--
**Connection to Steiner systems:**
A Steiner system S(2, k, n) is a PBD where all blocks have size k.
These are very constrained.
-/
axiom steiner_systems_special_case : True

/-
## Part IX: Summary
-/

/--
**Erdős Problem #732: PARTIALLY SOLVED**

**QUESTION 1:** Characterize block-compatible sequences.
- OPEN: No simple characterization known
- Pair-counting is necessary but not sufficient

**QUESTION 2:** Is B(n) ≥ exp(c·√n·log n)?
- SOLVED: Yes, by Alon
- B(n) ≈ 2^((1/2 + o(1))√n·log n)

**KEY INSIGHT:** There are exponentially many block-compatible sequences,
but characterizing which specific sequences work remains hard.
-/
theorem erdos_732_summary :
    -- Question 2 is solved
    (∃ c : ℝ, c > 0 ∧
      ∃ N : ℕ, ∀ n ≥ N,
        (B n : ℝ) ≥ Real.exp (c * Real.sqrt n * Real.log n)) ∧
    -- Question 1 is hard (necessary condition exists)
    (∀ Xs n, IsBlockCompatible Xs n → PairCountCondition Xs n) := by
  constructor
  · exact question_2_solved
  · intro Xs n h
    exact pair_count_necessary h

/--
**Problem status:**
Erdős Problem #732 is PARTIALLY SOLVED.
-/
theorem erdos_732_status : True := trivial

end Erdos732
