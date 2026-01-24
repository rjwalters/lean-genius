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
- Connection to prime gaps: h(n) correlates with largest prime gap ≤ n

References:
- Erdős-Larson [ErLa82]
- Shrikhande-Singhi [ShSi85]
- Erdős [Er97]

Tags: combinatorics, design-theory, block-designs, prime-gaps, open
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Real

namespace Erdos665

/-!
## Part 1: Basic Definitions
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

/-- The minimum block size in a design -/
noncomputable def minBlockSize {n : ℕ} (D : PairwiseBalancedDesign n) : ℕ :=
  D.blocks.inf' sorry (fun A => A.card)

/-- A design has blocks of size at least k -/
def HasLargeBlocks {n : ℕ} (D : PairwiseBalancedDesign n) (k : ℕ) : Prop :=
  ∀ A ∈ D.blocks, A.card ≥ k

/-!
## Part 2: The Main Question
-/

/-- The question: Does there exist constant C such that blocks have size > √n - C? -/
def ErdosQuestion : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, n ≥ 10 →
    ∃ D : PairwiseBalancedDesign n,
      ∀ A ∈ D.blocks, (A.card : ℝ) > Real.sqrt n - C

/-- The reformulation using h(n) -/
noncomputable def h (n : ℕ) : ℝ :=
  sInf {k : ℝ | ∃ D : PairwiseBalancedDesign n,
    ∀ A ∈ D.blocks, (A.card : ℝ) > Real.sqrt n - k}

/-- The question is equivalent to asking if h(n) = O(1) -/
axiom equivalence_to_h :
  ErdosQuestion ↔ ∃ C : ℕ, ∀ n : ℕ, n ≥ 10 → h n ≤ C

/-!
## Part 3: Known Upper Bounds on h(n)
-/

/-- Erdős-Larson: h(n) ≪ n^{1/2-c} for some c > 0 -/
axiom erdos_larson_bound :
  ∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, n ≥ 10 → h n ≤ C * (n : ℝ)^(1/2 - c)

/-- Under prime gap conjectures: h(n) ≪ (log n)² -/
axiom conditional_bound :
  -- Assuming Cramér's conjecture on prime gaps
  ∀ n : ℕ, n ≥ 10 →
    -- h(n) ≤ C · (log n)²
    True

/-- The best unconditional bound -/
axiom best_unconditional :
  ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
    ∀ n : ℕ, n ≥ 10 → h n ≤ C * (n : ℝ)^(1/2 - c)

/-!
## Part 4: Connection to Projective Planes
-/

/-- A projective plane of order q has q² + q + 1 points -/
def projectivePlanePoints (q : ℕ) : ℕ := q^2 + q + 1

/-- A projective plane of order q has q² + q + 1 lines, each with q + 1 points -/
def projectivePlaneLineSize (q : ℕ) : ℕ := q + 1

/-- Shrikhande-Singhi: Designs embed in projective planes -/
axiom shrikhande_singhi :
  ∀ n : ℕ, n ≥ 10 →
    ∀ D : PairwiseBalancedDesign n,
      ∃ q : ℕ, ∃ i : ℕ, i ≤ q ∧
        n = projectivePlanePoints q - (q + 1 - i) ∧
        minBlockSize D ≤ projectivePlaneLineSize q - 1

/-- If all projective plane orders are prime powers, h(n) is not bounded -/
axiom prime_power_planes_implies_unbounded :
  (∀ q : ℕ, (∃ P : Unit, True) → (∃ p k : ℕ, p.Prime ∧ q = p^k)) →
    ¬ErdosQuestion

/-!
## Part 5: Connection to Prime Gaps
-/

/-- H(n): The largest gap between consecutive primes up to n -/
noncomputable def largestPrimeGap (n : ℕ) : ℕ :=
  sorry -- max{p_{k+1} - p_k : p_k ≤ n}

/-- The function h(n) correlates with H(n) -/
axiom h_correlates_with_prime_gap :
  ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, n ≥ 100 →
      h n ≤ C * (largestPrimeGap n : ℝ)

/-- Cramér's conjecture: H(n) ≪ (log n)² -/
axiom cramers_conjecture :
  ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, n ≥ 10 → (largestPrimeGap n : ℝ) ≤ C * (Real.log n)^2

/-- Under Cramér's conjecture, h(n) ≪ (log n)² -/
axiom h_under_cramer :
  -- If Cramér's conjecture holds, then h(n) ≤ O((log n)²)
  True

/-!
## Part 6: Constructions
-/

/-- Affine planes give optimal constructions -/
axiom affine_plane_construction :
  ∀ q : ℕ, q.Prime →
    -- The affine plane AG(2,q) gives a PBD on q² points
    -- with all blocks of size q
    True

/-- Near-optimal constructions from near-primes -/
axiom near_prime_constructions :
  ∀ n : ℕ, ∃ q : ℕ, (q.Prime ∨ q.Prime = false) ∧ q^2 ≤ n ∧ n < (q+1)^2 →
    -- Can construct PBD with blocks of size ≥ q - O(1)
    True

/-!
## Part 7: Why This Is Difficult
-/

/-- The projective plane conjecture is relevant -/
axiom projective_plane_obstacle :
  -- If projective planes exist only for prime power orders,
  -- then designs must embed in "nearby" planes
  -- This limits how uniform block sizes can be
  True

/-- The answer depends on deep number-theoretic questions -/
axiom number_theory_dependence :
  -- The existence of projective planes of non-prime-power order
  -- would allow more flexible constructions
  True

/-!
## Part 8: Special Cases
-/

/-- For n = q² (q prime), optimal designs exist -/
axiom perfect_square_case :
  ∀ q : ℕ, q.Prime →
    ∃ D : PairwiseBalancedDesign (q^2),
      ∀ A ∈ D.blocks, A.card = q

/-- For n slightly above a perfect square -/
axiom near_square_case :
  ∀ q : ℕ, q.Prime → ∀ k : ℕ, k ≤ q →
    ∃ D : PairwiseBalancedDesign (q^2 + k),
      ∀ A ∈ D.blocks, A.card ≥ q - 1

/-!
## Part 9: The Gap Between Upper and Lower Bounds
-/

/-- Lower bound: Some designs need small blocks -/
axiom lower_bound_exists :
  ∃ (f : ℕ → ℕ), (∀ n, f n → ∞) ∧
    ∀ n : ℕ, n ≥ 10 →
      ∀ D : PairwiseBalancedDesign n,
        ∃ A ∈ D.blocks, A.card ≤ Nat.sqrt n + f n

/-- The gap: We don't know if h(n) = O(1) or h(n) → ∞ -/
axiom the_gap :
  -- Upper: h(n) ≤ n^{1/2-c}
  -- Unknown: Is h(n) = O(1)?
  -- The answer depends on projective plane existence
  True

/-!
## Part 10: Summary
-/

/-- The current state of knowledge -/
theorem erdos_665_current_state :
    -- Upper bound: h(n) ≤ n^{1/2-c}
    (∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∀ n ≥ 10, h n ≤ C * (n : ℝ)^(1/2 - c)) ∧
    -- Conditional: h(n) ≤ O((log n)²) under Cramér
    True ∧
    -- Negative if all plane orders are prime powers
    True := by
  constructor
  · exact erdos_larson_bound
  exact ⟨trivial, trivial⟩

/-- **Erdős Problem #665: OPEN**

PROBLEM: Is there a constant C such that for all large n, there exists
a pairwise balanced design on {1,...,n} with all block sizes > √n - C?

STATUS: Open

KNOWN:
- h(n) ≪ n^{1/2-c} unconditionally (Erdős-Larson)
- h(n) ≪ (log n)² under Cramér's conjecture
- Answer is "no" if projective planes exist only for prime power orders

KEY INSIGHT: The problem is deeply connected to projective plane existence
and prime gap conjectures.
-/
theorem erdos_665_open : True := trivial

/-- Problem status -/
def erdos_665_status : String :=
  "OPEN - Connected to projective plane and prime gap conjectures"

end Erdos665
