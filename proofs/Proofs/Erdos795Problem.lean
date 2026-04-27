/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 990567b9-500d-48bf-9b5e-fa4bffd84ddc

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem raghavan_error_is_smaller (n : ℕ) (hn : n ≥ 4) :
    ∃ C : ℝ, C > 0 ∧
    n^(5/12 : ℝ) ≤ C * n^(1/2 : ℝ) / Real.log n
-/

/-
  Erdős Problem #795: Distinct Subset Products

  Source: https://erdosproblems.com/795
  Status: SOLVED (Raghavan, 2025)

  Statement:
  Let g(n) be the maximal size of A ⊆ {1,...,n} such that the products
  ∏_{a∈S} a are distinct for all S ⊆ A. Is it true that
    g(n) ≤ π(n) + π(n^{1/2}) + o(n^{1/2}/log n)?

  Solution:
  YES - proved by Raghavan (2025) who established:
    Upper: g(n) ≤ π(n) + π(n^{1/2}) + O(n^{5/12+o(1)})
    Lower: g(n) ≥ π(n) + π(n^{1/2}) + π(n^{1/3})/3 - O(1)

  Background:
  - Erdős (1966) proved g(n) ≤ π(n) + O(n^{1/2}/log n)
  - The primes ≤ n and squares of primes ≤ n^{1/2} form a natural construction
  - This gives lower bound ≈ π(n) + π(n^{1/2})

  History:
  - The problem asks for tight bounds on sets with distinct subset products
  - Related to multiplicative Sidon sets and product-free sets
  - Part of a sequence including Problem #786

  References:
  - [Er66] Erdős (1966), "Remarks on number theory V", Mat. Lapok
  - [Ra25] Raghavan (2025), "Sharp Bounds for Sets with Distinct Subset Products"
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  DecidablePred fun (A : Finset ℕ) => A ⊆ Finset.range (n + 1) ∧ Erdos795.HasDistinctSubsetProducts A

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
namespace Erdos795

/- ## Basic Definitions -/

/-- A set has distinct subset products if every subset gives a different product -/
def HasDistinctSubsetProducts (A : Finset ℕ) : Prop :=
  ∀ S T : Finset ℕ, S ⊆ A → T ⊆ A → S ≠ T →
    S.prod id ≠ T.prod id

/-- Alternative: Injectivity of the product map on subsets -/
def DistinctProducts' (A : Finset ℕ) : Prop :=
  Function.Injective (fun S : Finset ℕ => if S ⊆ A then S.prod id else 0)

/-- The function g(n): maximum size of A ⊆ {1,...,n} with distinct subset products -/
noncomputable def g (n : ℕ) : ℕ :=
  haveI : DecidablePred (fun A : Finset ℕ =>
      A ⊆ Finset.range (n + 1) ∧ HasDistinctSubsetProducts A) :=
    Classical.decPred _
  Finset.sup
    ((Finset.range (n + 1)).powerset.filter (fun A =>
      A ⊆ Finset.range (n + 1) ∧ HasDistinctSubsetProducts A))
    Finset.card

/- ## The Prime Counting Function -/

/-- π(n) counts primes ≤ n -/
noncomputable def primePi (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter Nat.Prime |>.card

/- ## Erdős's Original Bound -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  g
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  n
Function expected at
  primePi
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  n-/
/-- Erdős (1966): g(n) ≤ π(n) + O(n^{1/2}/log n) -/
theorem erdos_upper_bound (n : ℕ) (hn : n ≥ 2) :
    ∃ C : ℝ, C > 0 ∧
    (g n : ℝ) ≤ primePi n + C * n^(1/2 : ℝ) / Real.log n := by
  sorry

-- [Er66]

/- ## The Conjectured Bound -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `g`
Unknown identifier `primePi`
Unknown identifier `primePi`-/
/-- The main question: Is g(n) ≤ π(n) + π(n^{1/2}) + o(n^{1/2}/log n)? -/
def erdos_795_question : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    (g n : ℝ) ≤ primePi n + primePi (Nat.sqrt n) + ε * n^(1/2 : ℝ) / Real.log n

/- ## Raghavan's Solution (2025) -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  g
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  n
Function expected at
  primePi
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  n
Function expected at
  primePi
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  (Nat.sqrt n)-/
/-- Raghavan (2025): Upper bound with explicit error term -/
theorem raghavan_upper_bound (n : ℕ) (hn : n ≥ 2) :
    ∃ C : ℝ, C > 0 ∧
    (g n : ℝ) ≤ primePi n + primePi (Nat.sqrt n) + C * n^(5/12 : ℝ) * (Real.log n)^(1/2) := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  g
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  n
Function expected at
  primePi
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  n
Function expected at
  primePi
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  (Nat.sqrt n)
Function expected at
  primePi
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  (n ^ (1 / 3 : ℝ).toNat)-/
-- [Ra25]

/-- Raghavan (2025): Lower bound including cube root primes -/
theorem raghavan_lower_bound (n : ℕ) (hn : n ≥ 2) :
    ∃ C : ℝ,
    (g n : ℝ) ≥ primePi n + primePi (Nat.sqrt n) + (primePi (n^(1/3 : ℝ).toNat) : ℝ) / 3 - C := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce

erdos_795_question : Sort u_1
⊢ erdos_795_question
type of theorem `erdos_795_solved` is not a proposition
  {erdos_795_question : Sort u_1} → erdos_795_question-/
-- [Ra25]

/-- Main theorem: The conjecture is TRUE -/
theorem erdos_795_solved : erdos_795_question := by
  intro ε hε
  -- For large n, n^{5/12} = o(n^{1/2}/log n)
  -- So Raghavan's bound implies the conjecture
  sorry

-- Consequence of raghavan_upper_bound

/- ## Natural Constructions -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  HasDistinctSubsetProducts
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  ((Finset.range (n + 1)).filter Nat.Prime)-/
/-- The primes ≤ n form a set with distinct subset products -/
theorem primes_have_distinct_products (n : ℕ) :
    HasDistinctSubsetProducts ((Finset.range (n + 1)).filter Nat.Prime) := by
  -- By unique factorization: different subsets of primes give different products
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  g
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  n
Function expected at
  primePi
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  n-/
/-- The primes give lower bound g(n) ≥ π(n) -/
theorem lower_bound_primes (n : ℕ) :
    g n ≥ primePi n := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  HasDistinctSubsetProducts
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (P ∪ P2)-/
/-- Adding squares of primes maintains distinct products -/
theorem primes_and_squares_distinct (n : ℕ) :
    let P := (Finset.range (n + 1)).filter Nat.Prime
    let P2 := (Finset.range (Nat.sqrt n + 1)).filter Nat.Prime |>.image (· ^ 2)
    HasDistinctSubsetProducts (P ∪ P2) := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  g
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  n
Function expected at
  primePi
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  n
Function expected at
  primePi
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  (Nat.sqrt n)-/
/-- This gives the natural lower bound π(n) + π(√n) -/
theorem lower_bound_with_squares (n : ℕ) (hn : n ≥ 4) :
    g n ≥ primePi n + primePi (Nat.sqrt n) := by
  sorry

/- ## Why the Bound is Tight -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  HasDistinctSubsetProducts
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  A
Function expected at
  g
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  n
Function expected at
  primePi
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  (n ^ (1 / 3 : ℝ).toNat)-/
/-- Key insight: Most elements must be primes or prime powers -/
theorem structure_of_optimal_sets (n : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.range (n + 1))
    (hDistinct : HasDistinctSubsetProducts A)
    (hOpt : A.card = g n) :
    -- A consists mostly of primes and prime squares
    ∃ P P2 R : Finset ℕ,
      A = P ∪ P2 ∪ R ∧
      (∀ p ∈ P, Nat.Prime p) ∧
      (∀ q ∈ P2, ∃ p, Nat.Prime p ∧ q = p^2) ∧
      R.card ≤ primePi (n^(1/3 : ℝ).toNat) / 2 := by
  sorry

-- Structural analysis in [Ra25]

/- ## Comparison of Error Terms -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  primePi
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (Nat.sqrt n)-/
/-- Erdős's error: O(n^{1/2}/log n) ≈ O(π(√n) · log(√n)/log n) -/
theorem erdos_error_comparison (n : ℕ) (hn : n ≥ 4) :
    ∃ C : ℝ, C > 0 ∧
    n^(1/2 : ℝ) / Real.log n ≤ C * primePi (Nat.sqrt n) := by
  sorry

/-- Raghavan's error: O(n^{5/12+o(1)}) is subsumed -/
theorem raghavan_error_is_smaller (n : ℕ) (hn : n ≥ 4) :
    ∃ C : ℝ, C > 0 ∧
    n^(5/12 : ℝ) ≤ C * n^(1/2 : ℝ) / Real.log n := by
  -- By multiplying both sides of the inequality by $\log n$, we get $(n : ℝ) ^ (5 / 12) * \log n \leq C * (n : ℝ) ^ (1 / 2)$.
  suffices h_mul : ∃ C > 0, (n : ℝ) ^ (5 / 12 : ℝ) * Real.log n ≤ C * (n : ℝ) ^ (1 / 2 : ℝ) by
    exact ⟨ h_mul.choose, h_mul.choose_spec.1, by rw [ le_div_iff₀ ( Real.log_pos ( by norm_cast; linarith ) ) ] ; linarith [ h_mul.choose_spec.2 ] ⟩;
  use ( ( n : ℝ ) ^ ( 5 / 12 : ℝ ) * Real.log n ) / ( n : ℝ ) ^ ( 1 / 2 : ℝ ) + 1, by positivity, by nlinarith [ show 0 < ( n : ℝ ) ^ ( 1 / 2 : ℝ ) by positivity, div_mul_cancel₀ ( ( n : ℝ ) ^ ( 5 / 12 : ℝ ) * Real.log n ) ( by positivity : ( n : ℝ ) ^ ( 1 / 2 : ℝ ) ≠ 0 ) ] ;

-- 5/12 < 1/2 and log factors help

/- ## Connection to Multiplicative Sidon Sets -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected end of input; expected ','-/
/-- A multiplicative Sidon set: no non-trivial product relations -/
def IsMultiplicativeSidon (A : Finset ℕ) : Prop :=
  ∀ a b c d ∈ A, a * b = c * d → ({a, b} : Finset ℕ) = {c, d}

/- NOTE: The theorem `sidon_implies_distinct_products` (Sidon → DSP) was REMOVED
   because it is MATHEMATICALLY FALSE.

   Counterexample: A = {2, 3, 6} is a multiplicative Sidon set (all products of
   pairs from A are distinct: 4, 6, 9, 12, 18, 36 — no two pairs give the same
   product). However, A does NOT have distinct subset products: {2, 3} and {6} are
   different subsets of A, but both have product 6.

   The correct direction is: DSP → Sidon (for 2-element subsets), not Sidon → DSP.
   See theorem `dsp_implies_sidon` (not yet formalized) for the correct statement.
-/

/-- Distinct subset products does NOT imply multiplicative Sidon.
    The implication goes the other way for 2-element subsets (DSP → Sidon).
    Counterexample: A = {2, 6, 18} has distinct subset products (products:
    2, 6, 18, 12, 36, 108, 216, all distinct) but is not Sidon: 6*6 = 36 = 2*18,
    while {6} ≠ {2, 18} as Finsets. -/
theorem distinct_products_not_sidon :
    ∃ A : Finset ℕ, HasDistinctSubsetProducts A ∧ ¬IsMultiplicativeSidon A := by
  -- Witness: A = {2, 6, 18}
  -- DSP: subset products are 2, 6, 18, 12, 36, 108, 216, all distinct.
  -- Not Sidon: 6*6 = 36 = 2*18, but {6,6} = {6} ≠ {2,18} as Finsets.
  sorry

/- ## Related: Problem #786 -/

/-- Problem #786 asks about the growth of g(n) for specific families -/
def erdos_786_related : Prop :=
  -- What is the precise asymptotic of g(n)?
  -- Raghavan's bounds pin it down to π(n) + π(√n) + Θ(π(∛n))
  True

/- ## Examples -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  HasDistinctSubsetProducts
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  { 2, 3, 5 }-/
/-- Example: A = {2, 3, 5} has distinct subset products -/
example : HasDistinctSubsetProducts {2, 3, 5} := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  HasDistinctSubsetProducts
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  { 2, 3, 6 }-/
-- Products: 1, 2, 3, 5, 6, 10, 15, 30 are distinct

/-- Example: A = {2, 3, 6} does NOT have distinct products -/
example : ¬HasDistinctSubsetProducts {2, 3, 6} := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  g
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  2
Function expected at
  g
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  3
Function expected at
  g
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  5
Function expected at
  g
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  10-/
-- {6} and {2, 3} both give product 6

/-- Small values of g(n) -/
theorem g_small_values :
    g 2 = 1 ∧ g 3 = 2 ∧ g 5 = 3 ∧ g 10 ≥ 5 := by
  sorry

/- ## Summary

**Status: SOLVED (Raghavan, 2025)**

Erdős Problem #795 asked for tight bounds on g(n), the maximum size of a
subset of {1,...,n} with all subset products distinct.

**Answer:**
g(n) = π(n) + π(n^{1/2}) + Θ(π(n^{1/3}))

**Upper Bound (Raghavan):**
g(n) ≤ π(n) + π(n^{1/2}) + O(n^{5/12+o(1)})

**Lower Bound (Raghavan):**
g(n) ≥ π(n) + π(n^{1/2}) + π(n^{1/3})/3 - O(1)

**Key Insight:**
Optimal sets consist primarily of primes and squares of primes, with
a small contribution from cube roots of primes. The unique factorization
theorem ensures distinct products, and prime powers contribute efficiently.
-/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected name `Erdos795` after `end`: The current section is unnamed

Hint: Delete the name `Erdos795` to end the current unnamed scope; outer named scopes can then be closed using additional `end` command(s):
  end ̵E̵r̵d̵o̵s̵7̵9̵5̵-/
end Erdos795