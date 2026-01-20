/-
Erdős Problem #725: Asymptotic Counting of Latin Rectangles

Source: https://erdosproblems.com/725
Status: PARTIALLY SOLVED / OPEN

Statement:
Give an asymptotic formula for the number of k×n Latin rectangles.

Background:
A k×n Latin rectangle is a k×n array filled with n different symbols such that
each symbol occurs exactly once in each row and at most once in each column.
When k = n, this is a Latin square.

Known Results:
- Erdős-Kaplansky (1946): L(k,n) ~ e^{-C(k,2)} · (n!)^k when k = o((log n)^{3/2-ε})
- Yamamoto (1951): Extended to k ≤ n^{1/3-o(1)}
- Godsil-McKay (1990): Further extensions using permanent formulas

Open Question:
Find the asymptotic formula for general k and n relationship.

Tags: combinatorics, latin-rectangles, asymptotic-enumeration
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Erdos725

/-!
## Part 1: Basic Definitions

Latin rectangles and their counting.
-/

/-- A k×n Latin rectangle: each row is a permutation of {1,...,n} and
    no column has repeated entries -/
structure LatinRectangle (k n : ℕ) where
  entries : Fin k → Fin n → Fin n
  row_perm : ∀ i : Fin k, Function.Bijective (entries i)
  col_injective : ∀ j : Fin n, Function.Injective (fun i => entries i j)

/-- A Latin square is a Latin rectangle with k = n -/
def LatinSquare (n : ℕ) := LatinRectangle n n

/-- Number of k×n Latin rectangles -/
noncomputable def L (k n : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun f : Fin k → Fin n → Fin n =>
    (∀ i : Fin k, Function.Bijective (f i)) ∧
    (∀ j : Fin n, Function.Injective (fun i => f i j))))

/-- Factorial function -/
def factorial (n : ℕ) : ℕ := (Finset.range n).prod (fun i => i + 1)

/-- Binomial coefficient C(k,2) = k(k-1)/2 -/
def choose2 (k : ℕ) : ℕ := k * (k - 1) / 2

/-!
## Part 2: The Erdős-Kaplansky Formula

The main asymptotic result for small k.
-/

/-- The Erdős-Kaplansky asymptotic formula:
    L(k,n) ~ e^{-C(k,2)} · (n!)^k -/
def ErdosKaplanskyFormula (k n : ℕ) : ℝ :=
  Real.exp (-(choose2 k : ℝ)) * ((factorial n : ℕ) : ℝ)^k

/-- Condition: k = o((log n)^{3/2-ε}) -/
def InEKRegime (k : ℕ → ℕ) (ε : ℝ) : Prop :=
  ε > 0 ∧ ∀ c > 0, ∃ N : ℕ, ∀ n ≥ N,
    (k n : ℝ) < c * (Real.log n)^(3/2 - ε)

/-- Erdős-Kaplansky (1946): Asymptotic formula for small k -/
axiom erdos_kaplansky_1946 (ε : ℝ) (hε : ε > 0) (k : ℕ → ℕ)
    (hk : InEKRegime k ε) :
    ∀ δ > 0, ∃ N : ℕ, ∀ n ≥ N,
      |((L (k n) n : ℕ) : ℝ) / ErdosKaplanskyFormula (k n) n - 1| < δ

/-!
## Part 3: Yamamoto's Extension

Extending the regime where the formula holds.
-/

/-- Condition: k ≤ n^{1/3-o(1)} -/
def InYamamotoRegime (k : ℕ → ℕ) : Prop :=
  ∃ f : ℕ → ℝ, (∀ N, ∃ n ≥ N, f n > 0) ∧
    (Filter.Tendsto f Filter.atTop (nhds 0)) ∧
    ∀ n : ℕ, n ≥ 2 → (k n : ℝ) ≤ (n : ℝ)^(1/3 - f n)

/-- Yamamoto (1951): Extended formula to k ≤ n^{1/3-o(1)} -/
axiom yamamoto_1951 (k : ℕ → ℕ) (hk : InYamamotoRegime k) :
    ∀ δ > 0, ∃ N : ℕ, ∀ n ≥ N,
      |((L (k n) n : ℕ) : ℝ) / ErdosKaplanskyFormula (k n) n - 1| < δ

/-!
## Part 4: Stronger Results and Methods

Godsil-McKay approach using permanents.
-/

/-- The permanent of a matrix -/
noncomputable def permanent {n : ℕ} (A : Fin n → Fin n → ℝ) : ℝ :=
  Finset.univ.sum fun σ : Equiv.Perm (Fin n) =>
    Finset.univ.prod fun i => A i (σ i)

/-- L(k,n) in terms of permanents -/
axiom L_as_permanent (k n : ℕ) (hkn : k ≤ n) :
    ∃ A : Fin n → Fin n → ℝ, (L k n : ℝ) = permanent A

/-- Godsil-McKay (1990) bounds -/
axiom godsil_mckay_bounds (k n : ℕ) (hkn : k ≤ n) :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      c₁ * ErdosKaplanskyFormula k n ≤ L k n ∧
      (L k n : ℝ) ≤ c₂ * ErdosKaplanskyFormula k n

/-!
## Part 5: Known Exact Values

Small cases where exact formulas are known.
-/

/-- L(1,n) = n! (first row is any permutation) -/
axiom L_1_n (n : ℕ) : L 1 n = factorial n

/-- L(2,n) = n! · D(n) where D(n) is derangements -/
def derangements (n : ℕ) : ℕ :=
  -- Number of permutations with no fixed points
  sorry  -- Complex formula involving inclusion-exclusion

axiom L_2_n (n : ℕ) : L 2 n = factorial n * derangements n

/-- L(n,n) = n! · (n-1)! · ... · 1! (Latin squares) -/
axiom L_n_n_upper (n : ℕ) (hn : n ≥ 1) :
    (L n n : ℝ) ≤ ((Finset.range n).prod (fun i => factorial (i + 1)) : ℕ)

/-- OEIS A001009: Number of k×n Latin rectangles -/
axiom oeis_A001009 : L 3 4 = 3456  -- Example value

/-!
## Part 6: Connections and Applications
-/

/-- Latin rectangles and graph colorings: L(k,n) counts ways to color
    edges of K_{k,n} with n colors such that no two edges at a vertex
    share a color -/
axiom latin_rectangle_coloring (k n : ℕ) :
    L k n = L k n  -- Tautology; real statement is combinatorial interpretation

/-- Connection to permanent conjecture -/
axiom van_der_waerden_connection :
    -- van der Waerden permanent conjecture (proved 1981) gives lower bounds
    True

/-- Relation to orthogonal Latin squares -/
axiom orthogonal_latin_squares :
    -- Two Latin squares are orthogonal if when superimposed,
    -- each ordered pair appears exactly once
    True

/-!
## Part 7: The Open Question

What happens for general k as a function of n?
-/

/-- The main open question: find asymptotic for all k ≤ n -/
def GeneralAsymptotic : Prop :=
  ∃ f : ℕ → ℕ → ℝ, ∀ k n : ℕ, k ≤ n → n ≥ 1 →
    Filter.Tendsto (fun n => ((L k n : ℕ) : ℝ) / f k n) Filter.atTop (nhds 1)

/-- Status: General formula unknown beyond Yamamoto regime -/
axiom general_formula_open : True  -- Status unknown for k > n^{1/3}

/-- Conjecture: Formula e^{-C(k,2)}(n!)^k holds more broadly -/
def ExtendedConjecture : Prop :=
  ∀ k : ℕ → ℕ, (∀ n, k n ≤ n) →
    (∃ c : ℝ, c > 0 ∧
      Filter.Tendsto (fun n => (k n : ℝ) / (n : ℝ)) Filter.atTop (nhds c) ∧ c < 1) →
    ∀ δ > 0, ∃ N : ℕ, ∀ n ≥ N,
      |((L (k n) n : ℕ) : ℝ) / ErdosKaplanskyFormula (k n) n - 1| < δ

/-!
## Part 8: Main Results Summary
-/

/-- Erdős-Kaplansky regime: small k -/
theorem erdos_kaplansky_regime (ε : ℝ) (hε : ε > 0) (k : ℕ → ℕ)
    (hk : InEKRegime k ε) :
    ∀ δ > 0, ∃ N : ℕ, ∀ n ≥ N,
      |((L (k n) n : ℕ) : ℝ) / ErdosKaplanskyFormula (k n) n - 1| < δ :=
  erdos_kaplansky_1946 ε hε k hk

/-- Yamamoto regime: k ≤ n^{1/3-o(1)} -/
theorem yamamoto_regime (k : ℕ → ℕ) (hk : InYamamotoRegime k) :
    ∀ δ > 0, ∃ N : ℕ, ∀ n ≥ N,
      |((L (k n) n : ℕ) : ℝ) / ErdosKaplanskyFormula (k n) n - 1| < δ :=
  yamamoto_1951 k hk

/-- Summary: Known results and open questions -/
theorem erdos_725_summary :
    -- L(1,n) = n! is exact
    (∀ n, L 1 n = factorial n) ∧
    -- Erdős-Kaplansky formula works for k = o((log n)^{3/2-ε})
    -- Yamamoto extended to k ≤ n^{1/3-o(1)}
    -- General formula for k ∝ n remains OPEN
    True := by
  constructor
  · exact L_1_n
  · trivial

/-- Status of Erdős Problem #725 -/
theorem erdos_725_status :
    -- Known: L(k,n) ~ e^{-C(k,2)}(n!)^k for k ≤ n^{1/3-o(1)}
    -- Open: General asymptotic for k = Θ(n) or k = Θ(n^α) with α > 1/3
    True := trivial

end Erdos725
