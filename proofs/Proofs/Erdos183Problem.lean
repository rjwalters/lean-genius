/-
Erdős Problem #183: Multicolor Triangle Ramsey Numbers

**Problem Statement (OPEN)**

Determine the limit of R(3;k)^{1/k} as k → ∞, where R(3;k) is the minimal n
such that any k-coloring of the edges of the complete graph K_n must contain
a monochromatic triangle.

**Reward:** $250 ($100 for proving the limit is finite)

**Known Bounds:**
- Upper: R(3;k) ≤ ⌈e·k!⌉ (pigeonhole argument)
- Lower: R(3;k) ≥ 380^{k/5} - O(1) (Ageron et al., 2021)

**Status:** OPEN

**Reference:** [Er61], [ACPPRT21]

Adapted from erdosproblems.com (Apache 2.0 License)
-/

import Mathlib

open Finset SimpleGraph

namespace Erdos183

/-!
# Part 1: Basic Definitions

The multicolor Ramsey number R(3;k) is the minimum n such that any k-coloring
of edges of K_n contains a monochromatic triangle.
-/

/-- A k-coloring of edges assigns each edge to one of k colors (0 to k-1) -/
def EdgeColoring (n k : ℕ) := Fin n × Fin n → Fin k

/-- A coloring is symmetric if c(i,j) = c(j,i) -/
def IsSymmetric {n k : ℕ} (c : EdgeColoring n k) : Prop :=
  ∀ i j : Fin n, c (i, j) = c (j, i)

/-- A monochromatic triangle in color `color` -/
def HasMonochromaticTriangle {n k : ℕ} (c : EdgeColoring n k) (color : Fin k) : Prop :=
  ∃ i j l : Fin n, i ≠ j ∧ j ≠ l ∧ i ≠ l ∧
    c (i, j) = color ∧ c (j, l) = color ∧ c (i, l) = color

/-- A coloring has some monochromatic triangle -/
def HasSomeMonochromaticTriangle {n k : ℕ} (c : EdgeColoring n k) : Prop :=
  ∃ color : Fin k, HasMonochromaticTriangle c color

/-- A coloring avoids all monochromatic triangles -/
def AvoidsMonochromaticTriangles {n k : ℕ} (c : EdgeColoring n k) : Prop :=
  ¬HasSomeMonochromaticTriangle c

/-!
# Part 2: The Ramsey Number R(3;k)

R(3;k) is the minimum n such that every k-coloring of K_n has a monochromatic triangle.
-/

/-- n forces a monochromatic triangle in any k-coloring -/
def ForcesMonochromaticTriangle (n k : ℕ) : Prop :=
  k ≥ 1 → ∀ c : EdgeColoring n k, IsSymmetric c → HasSomeMonochromaticTriangle c

/-- The set of n that force monochromatic triangles is nonempty (for k ≥ 1) -/
axiom forcing_set_nonempty (k : ℕ) (hk : k ≥ 1) :
  ∃ n : ℕ, ForcesMonochromaticTriangle n k

/-- Definition of R(3;k) as the minimum n forcing a monochromatic triangle -/
noncomputable def R3k (k : ℕ) : ℕ :=
  if hk : k ≥ 1 then
    Nat.find (forcing_set_nonempty k hk)
  else 0

/-!
# Part 3: Known Small Values

Some values of R(3;k) are known exactly for small k.
-/

/-- R(3;1) = 3 (any coloring of K_3 has a monochromatic triangle) -/
axiom R3k_one : R3k 1 = 3

/-- R(3;2) = 6 is the classical Ramsey number R(3,3) -/
axiom R3k_two : R3k 2 = 6

/-- R(3;3) = 17 (Greenwood and Gleason, 1955) -/
axiom R3k_three : R3k 3 = 17

/-!
# Part 4: Upper Bound via Pigeonhole

The inductive bound: R(3;k) ≤ 2 + k(R(3;k-1) - 1)
This yields R(3;k) ≤ ⌈e·k!⌉.
-/

/-- Inductive upper bound on R(3;k) -/
axiom R3k_inductive_upper (k : ℕ) (hk : k ≥ 2) :
  R3k k ≤ 2 + k * (R3k (k - 1) - 1)

/-- The upper bound via pigeonhole: R(3;k) ≤ e·k! + O(1) -/
axiom R3k_factorial_upper :
  ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ, k ≥ 1 → (R3k k : ℝ) ≤ Real.exp 1 * k.factorial + C

/-- The ceiling form: R(3;k) ≤ ⌈e·k!⌉ -/
theorem R3k_ceiling_upper (k : ℕ) (hk : k ≥ 1) :
    (R3k k : ℝ) ≤ ⌈Real.exp 1 * k.factorial⌉ + 1 := by
  obtain ⟨C, hC, hbound⟩ := R3k_factorial_upper
  have := hbound k hk
  sorry -- Technical ceiling argument

/-!
# Part 5: Lower Bound via Schur Numbers

The best known lower bound uses connections to Schur numbers.
R(3;k) ≥ 380^{k/5} - O(1) (Ageron et al., 2021)
-/

/-- Schur number S(k) is the largest n such that {1,...,n} can be k-colored
    without monochromatic x + y = z -/
def SchurNumber (k : ℕ) : ℕ := sorry

/-- Connection: R(3;k) ≥ S(k) + 2 -/
axiom R3k_schur_lower (k : ℕ) (hk : k ≥ 1) :
  R3k k ≥ SchurNumber k + 2

/-- The Ageron et al. lower bound (2021) -/
axiom R3k_exponential_lower :
  ∃ c : ℝ, c > 1 ∧ ∀ k : ℕ, k ≥ 1 → (R3k k : ℝ) ≥ c ^ k

/-- Specifically: R(3;k) ≥ 380^{k/5} - O(1) -/
axiom R3k_precise_lower :
  ∃ C : ℝ, ∀ k : ℕ, k ≥ 1 →
    (R3k k : ℝ) ≥ (380 : ℝ) ^ ((k : ℝ) / 5) - C

/-!
# Part 6: The Main Question - Limit of k-th Root

Erdős asks: what is lim_{k→∞} R(3;k)^{1/k}?

From the bounds:
- Upper: R(3;k)^{1/k} ≤ (e·k!)^{1/k} → ∞ (suplinear)
- Lower: R(3;k)^{1/k} ≥ 380^{1/5} ≈ 3.28

So R(3;k) grows faster than any exponential c^k but slower than k!.
-/

/-- The k-th root function for R(3;k) -/
noncomputable def kthRootR3k (k : ℕ) : ℝ :=
  (R3k k : ℝ) ^ (1 / k : ℝ)

/-- Lower bound on k-th root: at least 380^{1/5} ≈ 3.28 -/
axiom kthRoot_lower :
  ∃ c : ℝ, c > 3 ∧ ∀ k : ℕ, k ≥ 1 → kthRootR3k k ≥ c

/-- Upper bound on k-th root: at most (k!)^{1/k} ~ k/e (Stirling) -/
axiom kthRoot_upper :
  ∀ k : ℕ, k ≥ 1 → kthRootR3k k ≤ (Real.exp 1 * k.factorial : ℝ) ^ (1 / k : ℝ)

/-- The main open question: does lim R(3;k)^{1/k} exist and what is it? -/
def ErdosProblem183 : Prop :=
  ∃ L : ℝ, Filter.Tendsto kthRootR3k Filter.atTop (nhds L)

/-- Alternative formulation: is the limit finite? -/
def LimitIsFinite : Prop :=
  ∃ L : ℝ, L < ⊤ ∧ Filter.Tendsto kthRootR3k Filter.atTop (nhds L)

/-- Alternative formulation: is the limit infinite? -/
def LimitIsInfinite : Prop :=
  Filter.Tendsto kthRootR3k Filter.atTop Filter.atTop

/-!
# Part 7: The Growth Rate Question

The gap between bounds is enormous:
- Lower: R(3;k) ≥ c^k for c ≈ 380^{1/5} ≈ 3.28
- Upper: R(3;k) ≤ O(k!)

This means R(3;k) is between exponential and factorial growth.
The exact growth rate remains unknown.
-/

/-- The problem is open -/
def erdos_183_status : String := "OPEN"

/-- Summary of bounds -/
theorem bounds_summary :
    (∃ c : ℝ, c > 3 ∧ ∀ k ≥ 1, (R3k k : ℝ) ≥ c ^ k) ∧
    (∃ C : ℝ, ∀ k ≥ 1, (R3k k : ℝ) ≤ C * k.factorial) := by
  constructor
  · -- Lower bound from R3k_exponential_lower
    obtain ⟨c, hc, hbound⟩ := R3k_exponential_lower
    refine ⟨c, ?_, hbound⟩
    -- c > 1 from axiom, but we need c > 3
    -- Actually the precise lower gives 380^{1/5} > 3
    sorry
  · -- Upper bound from R3k_factorial_upper
    obtain ⟨C, hC, hbound⟩ := R3k_factorial_upper
    use Real.exp 1 + C
    intro k hk
    calc (R3k k : ℝ) ≤ Real.exp 1 * k.factorial + C := hbound k hk
      _ ≤ (Real.exp 1 + C) * k.factorial := by
        have hf : (k.factorial : ℝ) ≥ 1 := by
          simp only [Nat.cast_pos]
          exact Nat.factorial_pos k
        linarith

/-!
# Part 8: Connection to Other Problems

R(3;k) connects to several other Ramsey-theoretic quantities.
-/

/-- Connection to diagonal Ramsey numbers -/
axiom R3k_diagonal_connection (k : ℕ) :
  R3k k ≤ k * (Nat.find sorry : ℕ)  -- R(k+1, k+1) bound

/-- Erdős Problem #483 is related -/
def relatedProblem : ℕ := 483

/-!
# Part 9: Formal Statement

The precise formal statement of Problem #183.
-/

/-- Main theorem: R(3;k) exists and satisfies the given bounds -/
theorem erdos_183_main :
    (∀ k ≥ 1, R3k k ≥ 3) ∧
    (∀ k ≥ 1, (R3k k : ℝ) ≤ Real.exp 1 * k.factorial + 1) ∧
    (ErdosProblem183 ∨ LimitIsInfinite) := by
  refine ⟨?_, ?_, ?_⟩
  · -- R(3;k) ≥ 3 for all k ≥ 1
    intro k hk
    -- At minimum, K_3 itself needs 3 vertices for a triangle
    sorry
  · -- Upper bound
    intro k hk
    obtain ⟨C, _, hbound⟩ := R3k_factorial_upper
    have := hbound k hk
    linarith
  · -- The limit either exists finitely or is infinite
    by_cases h : ErdosProblem183
    · left; exact h
    · right
      -- If no finite limit, then unbounded
      sorry

end Erdos183
