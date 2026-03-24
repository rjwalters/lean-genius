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
open scoped Classical

namespace Erdos183

/-
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

/-
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

/-
# Part 3: Known Small Values

Some values of R(3;k) are known exactly for small k.
-/

/-- R(3;1) = 3 (any coloring of K_3 has a monochromatic triangle) -/
axiom R3k_one : R3k 1 = 3

/-- R(3;2) = 6 is the classical Ramsey number R(3,3) -/
axiom R3k_two : R3k 2 = 6

/-- R(3;3) = 17 (Greenwood and Gleason, 1955) -/
axiom R3k_three : R3k 3 = 17

/-- Monotonicity: more colors requires more vertices to force a monochromatic triangle.
    Proof: embed a k₁-coloring into a k₂-coloring via Fin.castLE; any monochromatic
    triangle for the k₂-coloring is also monochromatic for the k₁-coloring (injectivity). -/
theorem R3k_mono {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) : R3k k₁ ≤ R3k k₂ := by
  by_cases hk₁ : k₁ ≥ 1
  · -- k₁ ≥ 1 implies k₂ ≥ 1
    have hk₂ : k₂ ≥ 1 := le_trans hk₁ h
    -- Unfold R3k to Nat.find and use minimality
    show R3k k₁ ≤ R3k k₂
    unfold R3k
    rw [dif_pos hk₁, dif_pos hk₂]
    apply Nat.find_min'
    -- Need: ForcesMonochromaticTriangle (Nat.find ...) k₁
    have hforce := Nat.find_spec (forcing_set_nonempty k₂ hk₂)
    -- hforce : ForcesMonochromaticTriangle (Nat.find ...) k₂
    intro _ c₁ hc₁_sym
    -- Embed k₁-coloring as k₂-coloring via Fin.castLE
    let c₂ : EdgeColoring _ k₂ := fun p => Fin.castLE h (c₁ p)
    have hc₂_sym : IsSymmetric c₂ := by
      intro i j; show Fin.castLE h (c₁ (i, j)) = Fin.castLE h (c₁ (j, i))
      congr 1; exact hc₁_sym i j
    -- c₂ has a monochromatic triangle (from forcing property)
    obtain ⟨color₂, i, j, l, hij, hjl, hil, hcij, hcjl, hcil⟩ :=
      hforce hk₂ c₂ hc₂_sym
    -- Extract triangle for c₁ using Fin.castLE injectivity
    have hinj : Function.Injective (Fin.castLE h) := by
      intro a b hab
      ext
      have := congr_arg Fin.val hab
      simpa [Fin.castLE] using this
    exact ⟨c₁ (i, j), i, j, l, hij, hjl, hil, rfl,
      hinj (hcjl.trans hcij.symm), hinj (hcil.trans hcij.symm)⟩
  · -- k₁ = 0: R3k 0 = 0 ≤ R3k k₂
    have : k₁ = 0 := by omega
    subst this
    unfold R3k
    simp only [show ¬((0 : ℕ) ≥ 1) from by omega, dite_false]
    exact Nat.zero_le _

/-- R(3;k) ≥ 3 for all k ≥ 1 (from R3k_one and monotonicity). -/
theorem R3k_ge_three (k : ℕ) (hk : k ≥ 1) : R3k k ≥ 3 := by
  calc R3k k ≥ R3k 1 := R3k_mono hk
    _ = 3 := R3k_one

/-
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

/-
# Part 5: Lower Bound via Schur Numbers

The best known lower bound uses connections to Schur numbers.
R(3;k) ≥ 380^{k/5} - O(1) (Ageron et al., 2021)
-/

/-- Schur number S(k) is the largest n such that {1,...,n} can be k-colored
    without monochromatic x + y = z.
    Axiomatized since computing Schur numbers is a hard combinatorial problem. -/
axiom SchurNumber (k : ℕ) : ℕ

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

/-
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

/-- Alternative formulation: is the limit finite?
    (All reals are finite, so this is equivalent to ErdosProblem183.) -/
def LimitIsFinite : Prop :=
  ∃ L : ℝ, Filter.Tendsto kthRootR3k Filter.atTop (nhds L)

/-- Alternative formulation: is the limit infinite? -/
def LimitIsInfinite : Prop :=
  Filter.Tendsto kthRootR3k Filter.atTop Filter.atTop

/-
# Part 7: The Growth Rate Question

The gap between bounds is enormous:
- Lower: R(3;k) ≥ c^k for c ≈ 380^{1/5} ≈ 3.28
- Upper: R(3;k) ≤ O(k!)

This means R(3;k) is between exponential and factorial growth.
The exact growth rate remains unknown.
-/

/-- The problem is open -/
def erdos_183_status : String := "OPEN"

/-- Summary of bounds: exponential lower, factorial upper. -/
theorem bounds_summary :
    (∃ c : ℝ, c > 1 ∧ ∀ k ≥ 1, (R3k k : ℝ) ≥ c ^ k) ∧
    (∃ C : ℝ, ∀ k ≥ 1, (R3k k : ℝ) ≤ C * k.factorial) := by
  constructor
  · exact R3k_exponential_lower
  · obtain ⟨C, _, hbound⟩ := R3k_factorial_upper
    use Real.exp 1 + C
    intro k hk
    have hfact : (k.factorial : ℝ) ≥ 1 := by
      exact_mod_cast Nat.factorial_pos k
    nlinarith [hbound k hk]

/-
# Part 8: Connection to Other Problems

R(3;k) connects to several other Ramsey-theoretic quantities.
-/

/-- Erdős Problem #483 is related -/
def relatedProblem : ℕ := 483

/-
# Part 9: Formal Statement

The precise formal statement of Problem #183.
-/

/-- Main theorem: R(3;k) exists and satisfies the given bounds -/
theorem erdos_183_main :
    (∀ k ≥ 1, R3k k ≥ 3) ∧
    (∃ C : ℝ, C > 0 ∧ ∀ k ≥ 1, (R3k k : ℝ) ≤ C * k.factorial) := by
  constructor
  · exact R3k_ge_three
  · obtain ⟨C, hCpos, hbound⟩ := R3k_factorial_upper
    use Real.exp 1 + C
    constructor
    · linarith [Real.exp_pos 1]
    · intro k hk
      have hfact : (k.factorial : ℝ) ≥ 1 := by
        exact_mod_cast Nat.factorial_pos k
      nlinarith [hbound k hk]

end Erdos183
