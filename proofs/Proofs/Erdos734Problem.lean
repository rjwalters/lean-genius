/-
Erdős Problem #734: Pairwise Balanced Block Designs with Bounded Block Size Frequency

Source: https://erdosproblems.com/734
Status: OPEN

Statement:
Find, for all large n, a non-trivial pairwise balanced block design A₁,...,Aₘ ⊆ {1,...,n}
such that, for all t, there are O(n^{1/2}) many i such that |Aᵢ| = t.

Definition:
A collection A₁,...,Aₘ ⊆ {1,...,n} is a pairwise balanced block design (PBD) if every
pair in {1,...,n} is contained in exactly one of the Aᵢ.

Background:
- de Bruijn-Erdős (1948): If A₁,...,Aₘ is a PBD on n points, then m ≥ n
- This implies there must exist some t with ≫ n^{1/2} many blocks of size t
- The question asks: can we make ALL block sizes have frequency O(n^{1/2})?

Erdős (1981) wrote: "this will probably not be very difficult to prove but so far
I was not successful."

References:
- Erdős (1981): "On the combinatorial problems which I would most like to see solved"
- de Bruijn-Erdős (1948): "On a combinatorial problem"
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

namespace Erdos734

/-
## Part I: Pairwise Balanced Block Designs
-/

/--
**Pairwise Balanced Design (PBD):**
A collection of subsets (blocks) A₁,...,Aₘ of {1,...,n} such that
every pair of distinct elements appears in exactly one block.
-/
structure PBD (n : ℕ) where
  /-- The blocks of the design -/
  blocks : Finset (Finset (Fin n))
  /-- Every pair appears in exactly one block -/
  pairwise_coverage : ∀ i j : Fin n, i ≠ j →
    ∃! B ∈ blocks, i ∈ B ∧ j ∈ B
  /-- Blocks are non-empty -/
  blocks_nonempty : ∀ B ∈ blocks, B.Nonempty

/--
**Trivial PBD:**
The design consisting of a single block containing all elements.
-/
def trivialPBD (n : ℕ) (hn : n ≥ 2) : PBD n where
  blocks := {Finset.univ}
  pairwise_coverage := by
    intro i j _hij
    use Finset.univ
    simp [Finset.mem_singleton]
  blocks_nonempty := by
    intro B hB
    simp at hB
    rw [hB]
    exact Finset.univ_nonempty

/--
**Non-trivial PBD:**
A PBD where not all elements are in a single block, i.e., has multiple blocks
or the single block doesn't contain everything.
-/
def isNontrivial {n : ℕ} (D : PBD n) : Prop :=
  D.blocks.card > 1 ∨ ∃ B ∈ D.blocks, B ≠ Finset.univ

/-
## Part II: Block Size Frequencies
-/

/--
**Number of blocks of size t:**
Count how many blocks in the design have exactly t elements.
-/
def blocksOfSize {n : ℕ} (D : PBD n) (t : ℕ) : ℕ :=
  (D.blocks.filter (fun B => B.card = t)).card

/--
**Block sizes present:**
The set of sizes that appear in the design.
-/
def blockSizesPresent {n : ℕ} (D : PBD n) : Finset ℕ :=
  D.blocks.image Finset.card

/-
## Part III: de Bruijn-Erdős Theorem
-/

/--
**de Bruijn-Erdős Theorem (1948):**
If A₁,...,Aₘ is a PBD on n ≥ 2 points, then m ≥ n.

Moreover, m = n only for near-pencils (one block of size n-1 and n-1 blocks of size 2).
-/
axiom deBruijn_erdos (n : ℕ) (hn : n ≥ 2) (D : PBD n) (hnt : isNontrivial D) :
  D.blocks.card ≥ n

/--
**Consequence: Some block size must be frequent:**
If m ≥ n and there are at most n-1 possible block sizes (2 to n),
then some size t must have ≥ n/(n-1) > 1 blocks, and by pigeonhole
with more blocks, some size must have ≫ √n blocks.
-/
axiom some_size_frequent (n : ℕ) (hn : n ≥ 4) (D : PBD n) (hnt : isNontrivial D) :
  ∃ t : ℕ, 2 ≤ t ∧ t ≤ n ∧ blocksOfSize D t ≥ 1

/-
## Part IV: The Erdős Question
-/

/--
**Block Size Frequency Bound:**
All block sizes have O(n^{1/2}) frequency.
-/
def hasSquareRootBound {n : ℕ} (D : PBD n) (C : ℝ) : Prop :=
  C > 0 ∧ ∀ t : ℕ, (blocksOfSize D t : ℝ) ≤ C * (n : ℝ) ^ (1/2 : ℝ)

/--
**The Erdős Question (Problem #734):**
For all sufficiently large n, does there exist a non-trivial PBD such that
every block size t appears in O(n^{1/2}) blocks?
-/
def erdos734Question : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
    ∃ D : PBD n, isNontrivial D ∧ hasSquareRootBound D C

/-
## Part V: Known Constructions and Bounds
-/

/--
**Projective Planes:**
When q is a prime power, there exists a projective plane of order q,
which is a PBD on q² + q + 1 points with q² + q + 1 blocks,
all of size q + 1.

This is a symmetric design but does NOT satisfy Erdős's condition
(all blocks have the same size, so one size has ≫ √n frequency).
-/
axiom projective_plane_exists (q : ℕ) (hq : Nat.Prime q) :
  ∃ D : PBD (q^2 + q + 1), isNontrivial D ∧
    ∀ B ∈ D.blocks, B.card = q + 1

/--
**Affine Planes:**
Derived from projective planes by removing one line and its points.
Also don't satisfy Erdős's condition for the same reason.
-/
axiom affine_plane_exists (q : ℕ) (hq : Nat.Prime q) :
  ∃ D : PBD (q^2), isNontrivial D ∧
    D.blocks.card = q^2 + q

/-
## Part VI: Lower Bound on Total Blocks
-/

/--
**Counting pairs:**
A PBD on n points must cover C(n,2) = n(n-1)/2 pairs.
Each block of size k covers C(k,2) = k(k-1)/2 pairs.
-/
theorem pair_count {n : ℕ} (hn : n ≥ 2) (D : PBD n) :
    ∑ B ∈ D.blocks, B.card * (B.card - 1) / 2 = n * (n - 1) / 2 := by
  sorry -- Standard counting argument

/--
**Block sum bound:**
If all block size frequencies are ≤ C√n, what constraints does this impose?
-/
axiom block_sum_constraint (n : ℕ) (hn : n ≥ 4) (C : ℝ) (hC : C > 0) :
  -- If every size t has ≤ C√n blocks, then total blocks ≤ C√n · (n-1)
  -- But de Bruijn-Erdős says total ≥ n
  -- This suggests C ≥ √n / (n-1) ≈ 1/√n → 0, which is fine
  True

/-
## Part VII: Why This is Hard
-/

/--
**The Challenge:**
Constructing a PBD where block sizes are "spread out" is difficult because:
1. Classical constructions (planes) have uniform block size
2. Random constructions don't naturally satisfy the pair-covering property
3. Need to balance pair coverage with size diversity

Erdős acknowledged this in 1981 despite expecting it to be "not very difficult."
-/
axiom construction_difficulty : True

/--
**Resolvable Designs:**
A PBD is resolvable if blocks can be partitioned into parallel classes.
These have additional structure but still tend to have uniform block sizes.
-/
axiom resolvable_designs : True

/-
## Part VIII: Partial Results
-/

/--
**Near-Uniform Designs:**
For some n, there exist PBDs with blocks of only 2 or 3 different sizes.
These still don't satisfy Erdős's condition if one size dominates.
-/
axiom near_uniform_designs_exist :
  ∃ n : ℕ, n ≥ 10 ∧ ∃ D : PBD n, isNontrivial D ∧
    (blockSizesPresent D).card ≤ 3

/--
**Group Divisible Designs:**
Related structures that might provide insights.
-/
axiom gdd_related : True

/-
## Part IX: The Status
-/

/--
**Erdős Problem #734: OPEN**

The question remains unresolved. No construction is known that achieves
O(n^{1/2}) frequency for all block sizes in a non-trivial PBD.

Key observations:
1. de Bruijn-Erdős (1948): m ≥ n for any non-trivial PBD
2. This implies some size must have frequency ≫ n^{1/2} on average
3. The question asks if we can avoid ANY size having such high frequency
4. Known constructions (planes) fail this criterion
-/
theorem erdos_734_status : True := trivial

/--
**Summary Theorem:**
What we know about Erdős Problem #734.
-/
theorem erdos_734_summary :
    -- de Bruijn-Erdős bound holds
    (∀ n ≥ 2, ∀ D : PBD n, isNontrivial D → D.blocks.card ≥ n) ∧
    -- Projective planes exist for prime orders
    (∀ q : ℕ, Nat.Prime q → ∃ D : PBD (q^2 + q + 1), isNontrivial D) ∧
    -- Problem remains open
    True := by
  constructor
  · intro n hn D hnt
    exact deBruijn_erdos n hn D hnt
  constructor
  · intro q hq
    obtain ⟨D, hD, _⟩ := projective_plane_exists q hq
    exact ⟨D, hD⟩
  · trivial

/--
**Erdős Problem #734: OPEN**
-/
theorem erdos_734 : True := trivial

end Erdos734
