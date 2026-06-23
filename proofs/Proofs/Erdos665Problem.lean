/-
Erdős Problem #665: Pairwise Balanced Designs with Large Blocks

Source: https://erdosproblems.com/665
Status: OPEN

Statement:
A pairwise balanced design for {1,...,n} is a collection of sets A₁,...,Aₘ
where 2 ≤ |Aᵢ| < n, and every pair of distinct elements appears in exactly
one set.

Does there exist a constant C > 0 such that for all sufficiently large n,
a pairwise balanced design exists where |Aᵢ| > √n - C for all blocks?

Known Results:
- Erdős-Larson: h(n) ≪ n^{1/2-c} for some c > 0
- Under prime gap conjectures: h(n) ≪ (log n)²
- Shrikhande-Singhi: Answer is "no" if projective planes of all orders
  are prime powers (such designs embed in projective planes)

Tags: combinatorics, design-theory, block-designs, prime-gaps, open
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Real

namespace Erdos665

/-
## Part I: Basic Definitions

Ground set, pairwise balanced design, and block size properties.
-/

/-- The ground set {1, ..., n} -/
def groundSet (n : ℕ) : Finset ℕ := (Finset.range n).map ⟨(· + 1), fun _ _ h => by omega⟩

/-- A pairwise balanced design is a collection of blocks -/
structure PairwiseBalancedDesign (n : ℕ) where
  blocks : Finset (Finset ℕ)
  blocks_subset : ∀ A ∈ blocks, A ⊆ groundSet n
  blocks_size : ∀ A ∈ blocks, 2 ≤ A.card ∧ A.card < n
  covers_pairs : ∀ x y : ℕ, x ∈ groundSet n → y ∈ groundSet n → x ≠ y →
    ∃! A : Finset ℕ, A ∈ blocks ∧ x ∈ A ∧ y ∈ A

/-- A design has blocks of size at least k -/
def HasLargeBlocks {n : ℕ} (D : PairwiseBalancedDesign n) (k : ℕ) : Prop :=
  ∀ A ∈ D.blocks, A.card ≥ k

/-
## Part II: The Main Question

The function h(n) measures how close to √n all block sizes can be.
-/

/-- The question: Does there exist constant C such that blocks have size > √n - C? -/
def ErdosQuestion : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, n ≥ 10 →
    ∃ D : PairwiseBalancedDesign n,
      ∀ A ∈ D.blocks, (A.card : ℝ) > Real.sqrt n - C

/--
**h(n)**: The minimum "deficiency" — how far below √n the smallest block
must be in the best possible design on n points.
Axiomatized because it involves an infimum over all PBDs.
-/
axiom h (n : ℕ) : ℝ

/-- h(n) correctly measures deficiency from √n -/
/-
## Part III: Known Upper Bounds on h(n)
-/

/--
**Erdős-Larson (1982):**
h(n) ≪ n^{1/2-c} for some c > 0.
The best unconditional bound.
-/
axiom erdos_larson_bound :
  ∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, n ≥ 10 → h n ≤ C * (n : ℝ)^(1/2 - c)

/-
## Part IV: Connection to Projective Planes
-/

/-- A projective plane of order q has q² + q + 1 points -/
def projectivePlanePoints (q : ℕ) : ℕ := q^2 + q + 1

/-- A projective plane of order q has lines with q + 1 points -/
def projectivePlaneLineSize (q : ℕ) : ℕ := q + 1

/--
**Shrikhande-Singhi (1985):**
Every PBD on n points with blocks ≥ √n - c can be embedded
in a projective plane of order n + i for some i ≤ c + 2.
-/
/--
**Conditional negative answer:**
If projective planes exist only for prime power orders,
then h(n) is unbounded — the answer to Erdős's question is NO.
-/
axiom prime_power_planes_implies_unbounded :
  (∀ q : ℕ, q ≥ 2 → (∃ p k : ℕ, p.Prime ∧ q = p^k)) →
    ¬ErdosQuestion

/-
## Part V: Connection to Prime Gaps
-/

/--
**Largest prime gap up to n.**
H(n) = max{p_{k+1} - p_k : p_k ≤ n}.
Axiomatized because computing this requires iterating over primes.
-/
axiom largestPrimeGap (n : ℕ) : ℕ

/-- h(n) correlates with H(n) -/
axiom h_correlates_with_prime_gap :
  ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, n ≥ 100 →
      h n ≤ C * (largestPrimeGap n : ℝ)

/--
**Cramér's conjecture:**
H(n) = O((log n)²). If true, this gives h(n) = O((log n)²).
-/
/-
## Part VI: Special Cases
-/

/--
**Perfect square prime case:**
For n = q² with q prime, the affine plane AG(2,q) gives
a PBD with all blocks of size exactly q = √n.
-/
/-- For n slightly above q², blocks of size ≥ q - 1 are achievable. -/
/-
## Part VII: Summary
-/

/--
**Erdős Problem #665: Summary**

OPEN: Is h(n) = O(1)? Can all blocks have size > √n - C?

Combines:
1. Erdős-Larson unconditional bound h(n) ≤ n^{1/2-c}
2. Prime power planes would imply h(n) unbounded
3. h(n) correlates with largest prime gap H(n)
-/
theorem erdos_665_summary :
    -- Unconditional: h(n) ≤ n^{1/2-c}
    (∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, C > 0 ∧
      ∀ n : ℕ, n ≥ 10 → h n ≤ C * (n : ℝ)^(1/2 - c)) ∧
    -- Prime power planes ⟹ negative answer
    ((∀ q : ℕ, q ≥ 2 → (∃ p k : ℕ, p.Prime ∧ q = p^k)) → ¬ErdosQuestion) ∧
    -- h correlates with prime gaps
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 100 →
      h n ≤ C * (largestPrimeGap n : ℝ)) :=
  ⟨erdos_larson_bound,
   prime_power_planes_implies_unbounded,
   h_correlates_with_prime_gap⟩

end Erdos665
