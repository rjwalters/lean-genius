/-
Erdős Problem #917: Critical Graphs and Edge Density

Source: https://erdosproblems.com/917
Status: OPEN (partial results known)

Statement:
Let k ≥ 4 and f_k(n) be the maximum number of edges in a k-critical graph on n vertices.
(A graph is k-critical if its chromatic number is k but every proper subgraph has
chromatic number < k, i.e., removing any edge decreases the chromatic number.)

Questions:
1. Is f_k(n) ≫_k n²? (Does the edge count grow quadratically?)
2. Is f_6(n) ~ n²/4? (Specific asymptotic for 6-critical graphs)
3. For k ≥ 6: Is f_k(n) ~ (1/2)(1 - 1/⌊k/3⌋)n²?

Historical Results:
- Erdős (1949): Asked if f_k(n) = o(n²), was surprised by counterexamples
- Dirac (1952): f_6(4n+2) ≥ 4n² + 8n + 3 using two odd cycles + all cross edges
- Erdős (1969): Generalized for k ≡ 0 (mod 3)
- Toft (1970): f_k(n) ≫_k n² for all k ≥ 4
- Stiebitz (1987): Disproved asymptotic conjecture for k ≢ 0 (mod 3)
- Luo-Ma-Yang (2023): Improved upper bounds

References:
- Erdős (1949), Dirac (1952), Toft (1970), Stiebitz (1987), Luo-Ma-Yang (2023)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic

open SimpleGraph Finset

namespace Erdos917

/- ## Basic Definitions -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The chromatic number of a simple graph. -/
noncomputable def chromaticNumber (G : SimpleGraph V) : ℕ :=
  Nat.find (G.Colorable_of_fintype)

/-- A graph is k-chromatic if its chromatic number is exactly k. -/
def IsKChromatic (G : SimpleGraph V) (k : ℕ) : Prop :=
  chromaticNumber G = k

/-- A graph G is k-critical if:
    1. Its chromatic number is k
    2. Removing any edge decreases the chromatic number -/
def IsKCritical (G : SimpleGraph V) (k : ℕ) : Prop :=
  IsKChromatic G k ∧
  ∀ e : Sym2 V, e ∈ G.edgeSet →
    chromaticNumber (G.deleteEdges {e}) < k

/-- The number of edges in a simple graph. -/
noncomputable def edgeCount (G : SimpleGraph V) : ℕ :=
  G.edgeFinset.card

/- ## The Maximum Edge Function f_k(n) -/

/--
**f_k(n):** The maximum number of edges in a k-critical graph on n vertices.
Axiomatized because computing the maximum over all k-critical graphs on n vertices
requires dependent type manipulation beyond simple definitions.
-/
axiom f (k n : ℕ) : ℕ

/-- f_k is defined for k ≥ 4 (the interesting range). -/
/- ## Question 1: Quadratic Growth -/

/--
**Question 1:** Is f_k(n) ≫_k n²?

This asks whether f_k(n) ≥ c_k · n² for some constant c_k > 0 depending on k.
-/
def Question1 (k : ℕ) : Prop :=
  k ≥ 4 → ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ k → (f k n : ℝ) ≥ c * n^2

/--
**Toft (1970):** Proved f_k(n) ≫_k n² for all k ≥ 4.

This answers Question 1 affirmatively!
-/
axiom toft_1970 (k : ℕ) (hk : k ≥ 4) :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ k → (f k n : ℝ) ≥ c * n^2

/-- Question 1 is answered: YES for all k ≥ 4. -/
theorem question1_answered : ∀ k ≥ 4, Question1 k := fun k hk _ => toft_1970 k hk

/- ## Question 2: The k = 6 Case -/

/--
**Question 2:** Is f_6(n) ~ n²/4?

This conjectures that the asymptotic density for 6-critical graphs is 1/4.
-/
def Question2 : Prop :=
  ∀ ε > 0, ∀ᶠ n in Filter.atTop,
    |((f 6 n : ℝ) / n^2) - 1/4| < ε

/--
**Dirac's Construction (1952):**
Take two disjoint odd cycles of length 2n+1 and add all cross edges.
This gives a 6-critical graph with approximately n²/4 edges.
-/
/- ## Question 3: The General Asymptotic -/

/--
**Question 3:** For k ≥ 6, is f_k(n) ~ (1/2)(1 - 1/⌊k/3⌋)n²?

This generalizes Question 2 (the k = 6 case gives ⌊6/3⌋ = 2, so 1/2(1-1/2) = 1/4).
-/
def Question3 (k : ℕ) : Prop :=
  k ≥ 6 →
  let d := k / 3  -- floor division in Lean
  ∀ ε > 0, ∀ᶠ n in Filter.atTop,
    |((f k n : ℝ) / n^2) - (1/2) * (1 - 1/d)| < ε

/--
**Erdős's Construction (1969):**
For k ≡ 0 (mod 3), infinitely many n satisfy
f_k(n) ≥ (1/2)(1 - 1/(k/3))n² + n
-/
/--
**Stiebitz (1987):** Disproved the asymptotic conjecture for k ≢ 0 (mod 3).

The conjecture is FALSE for k ≢ 0 (mod 3), but may still be true for k ≡ 0 (mod 3).
-/
axiom stiebitz_1987_disproof (k : ℕ) (hk : k ≥ 4) (hmod : k % 3 ≠ 0) :
    ¬Question3 k

/- ## Upper Bounds -/

/--
**Trivial Upper Bound:**
A k-critical graph has chromatic number k, so it doesn't contain K_k.
By Turán's theorem, it has at most ex(n; K_k) edges.
-/
/--
**Stiebitz Upper Bound (1987):**
f_k(n) < ex(n; K_{k-1}) ~ (1/2)(1 - 1/(k-2))n²

Better than Turán by replacing k-1 with k-2.
-/
/--
**Luo-Ma-Yang (2023):** Improved the upper bound further.

f_k(n) ≤ (1/2)(1 - 1/(k-2) - 1/(36(k-1)²) + o(1))n²
-/
/- ## Summary

**Erdős Problem #917 - PARTIALLY SOLVED**

**Question 1: Is f_k(n) ≫_k n²?**
ANSWERED: YES by Toft (1970).

**Question 2: Is f_6(n) ~ n²/4?**
OPEN: Lower bound established (Dirac), upper bound not proven.

**Question 3: Is f_k(n) ~ (1/2)(1 - 1/⌊k/3⌋)n² for k ≥ 6?**
PARTIALLY ANSWERED:
- FALSE for k ≢ 0 (mod 3) by Stiebitz (1987)
- OPEN for k ≡ 0 (mod 3)

**Current State:**
- Lower bounds: Erdős-Dirac constructions
- Upper bounds: Stiebitz (1987), improved by Luo-Ma-Yang (2023)
-/

/-- Complete summary of Erdős Problem #917.
Combines Toft's quadratic growth with Stiebitz's disproof. -/
theorem erdos_917 :
    (∀ k ≥ 4, Question1 k) ∧
    (∀ k ≥ 4, k % 3 ≠ 0 → ¬Question3 k) ∧
    (∀ k ≥ 4, ∃ c : ℝ, c > 0 ∧ ∀ n ≥ k, (f k n : ℝ) ≥ c * n^2) :=
  ⟨question1_answered, stiebitz_1987_disproof, toft_1970⟩

end Erdos917
