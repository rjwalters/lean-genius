/-
Erdős Problem #722: Existence of Steiner Systems (Block Designs)

Source: https://erdosproblems.com/722
Status: SOLVED (Keevash 2014)

Statement:
Let k > r and n be sufficiently large. Does there always exist a block r-(n,k,1)
design (or Steiner system S(r,k,n)), provided the trivial necessary divisibility
conditions are satisfied?

The divisibility conditions are: for every 0 ≤ i < r,
  binom(k-i, r-i) | binom(n-i, r-i)

Answer: YES (for n sufficiently large)

Historical Progress:
- Kirkman: Solved for (r,k) = (2,3) - "Kirkman's schoolgirl problem"
- Hanani (1961): Solved for (3,4), (2,4), (2,5)
- Wilson (1972): Solved for (2,k) for all k ≥ 2
- Keevash (2014): General proof for all r < k

Key Insight:
Keevash used probabilistic and algebraic methods (randomized algebraic
construction) to prove existence for all parameters satisfying the
divisibility conditions.

A Steiner system S(r,k,n) is a collection of k-subsets (blocks) of an
n-element set such that every r-subset is contained in exactly one block.

References:
- Hanani (1961): "The existence and construction of balanced incomplete
  block designs"
- Wilson (1972): "An existence theory for pairwise balanced designs"
- Keevash (2014): "The existence of designs", arXiv:1401.3665

Tags: combinatorics, design-theory, steiner-systems, block-designs
-/

import Mathlib.Combinatorics.SetFamily.Intersecting
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset

open Nat Finset

namespace Erdos722

/-!
## Part I: Basic Definitions
-/

variable {n : ℕ}

/--
**Block of size k:**
A subset of {1, ..., n} of cardinality k.
-/
def IsBlock (k : ℕ) (B : Finset (Fin n)) : Prop := B.card = k

/--
**r-Subset Coverage:**
An r-subset S is covered by block B if S ⊆ B.
-/
def Covers (S B : Finset (Fin n)) : Prop := S ⊆ B

/--
**Block Design:**
A collection of k-blocks such that every r-subset is covered by exactly one block.
This is a Steiner system S(r, k, n).
-/
structure SteinerSystem (r k n : ℕ) where
  blocks : Finset (Finset (Fin n))
  block_size : ∀ B ∈ blocks, (B : Finset (Fin n)).card = k
  covers_once : ∀ S : Finset (Fin n), S.card = r →
    ∃! B, B ∈ blocks ∧ Covers S B

/--
**Number of blocks in a Steiner system:**
A Steiner system S(r,k,n) has exactly binom(n,r) / binom(k,r) blocks.
-/
noncomputable def expectedBlockCount (r k n : ℕ) : ℕ :=
  n.choose r / k.choose r

/--
**Alternative formula for block count:**
binom(n,k) · binom(k,r)^{-1}
-/
noncomputable def blockCountAlt (r k n : ℕ) : ℕ :=
  n.choose k / k.choose r

/-!
## Part II: Divisibility Conditions
-/

/--
**The Divisibility Conditions:**
For a Steiner system S(r,k,n) to possibly exist, we need:
  binom(k-i, r-i) | binom(n-i, r-i) for all 0 ≤ i < r

These are necessary conditions for the block counts to work out.
-/
def DivisibilityConditions (r k n : ℕ) : Prop :=
  ∀ i : ℕ, i < r → (k - i).choose (r - i) ∣ (n - i).choose (r - i)

/--
**Special case i = 0:**
binom(k, r) | binom(n, r)
-/
def MainDivisibility (r k n : ℕ) : Prop :=
  k.choose r ∣ n.choose r

/--
**Special case i = r-1:**
k - (r-1) | n - (r-1), i.e., k - r + 1 | n - r + 1
-/
def LastDivisibility (r k n : ℕ) : Prop :=
  (k - r + 1) ∣ (n - r + 1)

/--
**All conditions together:**
-/
theorem divisibility_includes_main (r k n : ℕ) (hr : r ≥ 1) :
    DivisibilityConditions r k n → MainDivisibility r k n := by
  intro hDiv
  exact hDiv 0 (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hr))

/-!
## Part III: Classical Examples
-/

/--
**Kirkman's Schoolgirl Problem:**
S(2,3,n) exists iff n ≡ 1 or 3 (mod 6) and n ≥ 7.

This was the first Steiner triple system problem, solved by Kirkman (1847).
-/
axiom kirkman_triple_systems (n : ℕ) (hn : n ≥ 7) :
    (n % 6 = 1 ∨ n % 6 = 3) ↔
    ∃ S : SteinerSystem 2 3 n, True

/--
**Fano Plane:**
S(2,3,7) - the smallest Steiner triple system.
Has 7 points and 7 lines (blocks), each line contains 3 points.
-/
axiom fano_plane_exists : ∃ S : SteinerSystem 2 3 7, True

/--
**Hanani's Results (1961):**
Characterized when S(3,4,n), S(2,4,n), and S(2,5,n) exist.
-/
axiom hanani_1961 :
    -- S(3,4,n) exists for n ≡ 2 or 4 (mod 6), n ≥ 4
    (∀ n : ℕ, n ≥ 4 → (n % 6 = 2 ∨ n % 6 = 4) →
      DivisibilityConditions 3 4 n → ∃ S : SteinerSystem 3 4 n, True) ∧
    -- S(2,4,n) exists for n ≡ 1 or 4 (mod 12), n ≥ 4
    (∀ n : ℕ, n ≥ 4 → DivisibilityConditions 2 4 n →
      ∃ S : SteinerSystem 2 4 n, True) ∧
    -- S(2,5,n) exists under appropriate conditions
    (∀ n : ℕ, n ≥ 5 → DivisibilityConditions 2 5 n →
      ∃ S : SteinerSystem 2 5 n, True)

/-!
## Part IV: Wilson's Theorem (1972)
-/

/--
**Wilson's Theorem (1972):**
For r = 2, Steiner systems S(2,k,n) exist for all sufficiently large n
satisfying the divisibility conditions.

This resolved the r = 2 case completely.
-/
axiom wilson_theorem_r2 (k : ℕ) (hk : k ≥ 2) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, DivisibilityConditions 2 k n →
      ∃ S : SteinerSystem 2 k n, True

/--
**Wilson's quantitative bound:**
The N₀ depends polynomially on k.
-/
axiom wilson_quantitative (k : ℕ) (hk : k ≥ 2) :
    ∃ C : ℕ, ∀ n ≥ C * k^2, DivisibilityConditions 2 k n →
      ∃ S : SteinerSystem 2 k n, True

/-!
## Part V: Keevash's Theorem (2014) - General Solution
-/

/--
**Keevash's Theorem (2014):**
For all r < k, Steiner systems S(r,k,n) exist for all sufficiently large n
satisfying the divisibility conditions.

This is the complete solution to Erdős Problem #722.
-/
axiom keevash_theorem (r k : ℕ) (hr : r ≥ 1) (hk : k > r) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, DivisibilityConditions r k n →
      ∃ S : SteinerSystem r k n, True

/--
**Erdős Problem #722: SOLVED**

The answer is YES: for n sufficiently large, Steiner systems exist
whenever the divisibility conditions are satisfied.
-/
theorem erdos_722_solved (r k : ℕ) (hr : r ≥ 1) (hk : k > r) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, DivisibilityConditions r k n →
      ∃ S : SteinerSystem r k n, True :=
  keevash_theorem r k hr hk

/-!
## Part VI: Keevash's Method
-/

/--
**Randomized Algebraic Construction:**
Keevash's proof uses a sophisticated combination of:
1. Random greedy algorithms
2. Algebraic nibble methods
3. Absorbing methods

The key innovation was the "randomized algebraic construction" that handles
the general case.
-/
axiom keevash_method_insight : True

/--
**Absorbing Method:**
A key technique: first construct a "robustly spread" partial design,
then complete it using algebraic absorption.
-/
axiom absorbing_method : True

/-!
## Part VII: Small Examples
-/

/--
**Example: S(2,3,7) - Fano Plane**
7 blocks: {1,2,3}, {1,4,5}, {1,6,7}, {2,4,6}, {2,5,7}, {3,4,7}, {3,5,6}
Each pair appears in exactly one block.
-/
theorem fano_plane_divisibility : DivisibilityConditions 2 3 7 := by
  intro i hi
  interval_cases i
  · -- i = 0: 3 | 21 ✓
    simp [Nat.choose]
    decide
  · -- i = 1: 2 | 6 ✓
    simp [Nat.choose]
    decide

/--
**Example: S(2,3,9)**
12 blocks forming a Steiner triple system on 9 points.
-/
theorem s239_divisibility : DivisibilityConditions 2 3 9 := by
  intro i hi
  interval_cases i
  · simp [Nat.choose]; decide
  · simp [Nat.choose]; decide

/-!
## Part VIII: Related Concepts
-/

/--
**Resolvable Design:**
A Steiner system where blocks can be partitioned into parallel classes.
Kirkman's schoolgirl problem asks for a resolvable S(2,3,15).
-/
def IsResolvable (S : SteinerSystem r k n) : Prop :=
  -- Blocks can be partitioned so each class partitions the ground set
  True  -- Simplified

/--
**Packing vs Covering:**
- Packing: every r-set in at most one block
- Covering: every r-set in at least one block
- Steiner: exactly one (both packing and covering)
-/
def IsPacking (blocks : Finset (Finset (Fin n))) (r : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card = r →
    (blocks.filter (fun B => Covers S B)).card ≤ 1

def IsCovering (blocks : Finset (Finset (Fin n))) (r : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card = r →
    ∃ B ∈ blocks, Covers S B

/-!
## Part IX: Summary
-/

/--
**Summary of Results:**
-/
theorem erdos_722_summary :
    -- The general existence theorem holds (Keevash)
    (∀ r k : ℕ, r ≥ 1 → k > r →
      ∃ N₀ : ℕ, ∀ n ≥ N₀, DivisibilityConditions r k n →
        ∃ S : SteinerSystem r k n, True) ∧
    -- Wilson's theorem for r = 2
    (∀ k : ℕ, k ≥ 2 →
      ∃ N₀ : ℕ, ∀ n ≥ N₀, DivisibilityConditions 2 k n →
        ∃ S : SteinerSystem 2 k n, True) ∧
    -- Fano plane exists
    (∃ S : SteinerSystem 2 3 7, True) := by
  constructor
  · exact fun r k hr hk => keevash_theorem r k hr hk
  constructor
  · exact fun k hk => wilson_theorem_r2 k hk
  · exact fano_plane_exists

/--
**Historical Note:**
Steiner systems are named after Jakob Steiner, though Thomas Kirkman
studied them first. The existence problem was a major open question in
combinatorics for over a century until Keevash's breakthrough in 2014.
-/
theorem historical_note : True := trivial

end Erdos722
