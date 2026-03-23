/-
  Erdős Problem #793: Primitive Sets Avoiding Product Divisibility

  Source: https://erdosproblems.com/793
  Status: OPEN

  Statement:
  Let F(n) be the maximum size of a subset A ⊆ {1,...,n} such that
  a ∤ bc whenever a, b, c ∈ A with a ≠ b and a ≠ c.

  Is there a constant C such that F(n) = π(n) + (C + o(1))·n^{2/3}·(log n)^{-2}?

  Background:
  This is a variant of primitive set problems. A set is "primitive" if no
  element divides another. Here we strengthen the condition: no element
  divides the product of any two other distinct elements.

  The primes in (n^{2/3}, n] trivially satisfy this condition (they can't
  divide any product of smaller numbers), contributing π(n) - π(n^{2/3}) ≈ π(n)
  elements. The question is: how many additional elements can we add?

  Known Bounds (Erdős 1938):
  π(n) + c₁·n^{2/3}·(log n)^{-2} ≤ F(n) ≤ π(n) + c₂·n^{2/3}·(log n)^{-2}

  Graph-Theoretic Proof (Erdős 1969):
  Upper bound F(n) ≤ π(n) + n^{2/3} via a bipartite graph argument:
  Vertices: [1, n^{2/3}] ∪ {primes in (n^{2/3}, n]}
  Edges: u ~ v if uv ∈ A
  This graph is P₃-free (no path of length 3), hence a forest, giving the bound.

  Generalization:
  For sets where no a divides products of r distinct others, the exponent
  2/3 becomes 2/(r+1).

  References:
  [Er38] Erdős, P. "On sequences of integers no one of which divides
         the product of two others" (1938)
  [Er69] Erdős, P. "Some applications of graph theory to number theory" (1969)

  Tags: number-theory, divisibility, primitive-sets, primes, open-problem
-/

import Mathlib

open Finset Nat

/-
## The Divisibility Condition

A set A satisfies the condition if no element divides the product of
two other distinct elements.
-/

/-- The key divisibility condition: a ∤ bc for distinct a, b, c ∈ A -/
def satisfiesCondition (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
    a ≠ b → a ≠ c → ¬(a ∣ b * c)

/-- Alternative: a doesn't divide any product of two other elements -/
def noDividesProduct (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
    a ≠ b → a ≠ c → b ≠ c → ¬(a ∣ b * c)

/-
## The Function F(n)

F(n) = maximum size of A ⊆ {1,...,n} satisfying the condition.
-/

/-- The set {1, ..., n} -/
def Icc_nat (n : ℕ) : Finset ℕ := Finset.Icc 1 n

/-- F(n): maximum size of a valid subset of {1,...,n} -/
noncomputable def F (n : ℕ) : ℕ :=
  sSup { A.card | A : Finset ℕ // A ⊆ Icc_nat n ∧ satisfiesCondition A }

/-
## Prime Counting Function

π(n) counts primes up to n. Large primes form the "core" of optimal sets.
-/

/-- Prime counting function π(n) -/
noncomputable def primePi (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).filter Nat.Prime |>.card

/-- Primes in (n^{2/3}, n] can all be included -/
theorem large_primes_satisfy_condition (n : ℕ) (hn : n ≥ 8) :
    let A := (Finset.Icc 1 n).filter (fun p => Nat.Prime p ∧ p > n^(2/3 : ℝ))
    satisfiesCondition A := by
  intro A
  intro a ha b hb c hc hab hac
  simp only [mem_filter, mem_Icc] at ha hb hc
  -- a is prime and > n^{2/3}, so a > b and a > c
  -- Thus a ∤ bc since a is prime and neither b nor c equals a
  sorry

/-
## Known Bounds

Erdős established tight bounds up to constants.
-/

/-- Lower bound: F(n) ≥ π(n) + c₁·n^{2/3}·(log n)^{-2} -/
axiom F_lower_bound :
  ∃ c₁ : ℝ, c₁ > 0 ∧ ∀ n ≥ 2,
    (F n : ℝ) ≥ primePi n + c₁ * n^(2/3 : ℝ) * (Real.log n)^(-2 : ℝ)

/-- Upper bound: F(n) ≤ π(n) + c₂·n^{2/3}·(log n)^{-2} -/
axiom F_upper_bound :
  ∃ c₂ : ℝ, c₂ > 0 ∧ ∀ n ≥ 2,
    (F n : ℝ) ≤ primePi n + c₂ * n^(2/3 : ℝ) * (Real.log n)^(-2 : ℝ)

/-- Simpler upper bound: F(n) ≤ π(n) + n^{2/3} -/
axiom F_simple_upper_bound (n : ℕ) (hn : n ≥ 2) :
    (F n : ℝ) ≤ primePi n + n^(2/3 : ℝ)

/-
## The Main Conjecture (OPEN)

Does F(n) - π(n) have a precise asymptotic with a specific constant C?
-/

/-- The secondary term: F(n) - π(n) -/
noncomputable def secondaryTerm (n : ℕ) : ℝ :=
  (F n : ℝ) - primePi n

/-- The normalized secondary term -/
noncomputable def normalizedSecondary (n : ℕ) : ℝ :=
  secondaryTerm n / (n^(2/3 : ℝ) * (Real.log n)^(-2 : ℝ))

/-- Erdős's conjecture: the normalized secondary term converges to some C -/
def erdos793Conjecture : Prop :=
  ∃ C : ℝ, Filter.Tendsto normalizedSecondary Filter.atTop (nhds C)

/-- Equivalent: F(n) = π(n) + (C + o(1))·n^{2/3}·(log n)^{-2} -/
def erdos793ConjectureAlt : Prop :=
  ∃ C : ℝ, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    |secondaryTerm n - C * n^(2/3 : ℝ) * (Real.log n)^(-2 : ℝ)| <
      ε * n^(2/3 : ℝ) * (Real.log n)^(-2 : ℝ)

/-
## Graph-Theoretic Approach

Erdős's elegant proof uses a bipartite graph construction.
-/

/-- The bipartite graph construction for the upper bound proof -/
structure ErdosGraph (n : ℕ) where
  /-- Small integers: [1, n^{2/3}] -/
  smallInts : Finset ℕ
  /-- Large primes: primes in (n^{2/3}, n] -/
  largePrimes : Finset ℕ
  /-- Vertices are the union -/
  vertices : Finset ℕ := smallInts ∪ largePrimes
  /-- Edges: uv ∈ A for some valid set A -/
  edges : Finset (ℕ × ℕ)

/-- The graph has no P₃ (path of length 3) -/
def ErdosGraph.isP3Free (G : ErdosGraph n) : Prop :=
  ∀ a b c d : ℕ, ¬((a, b) ∈ G.edges ∧ (b, c) ∈ G.edges ∧ (c, d) ∈ G.edges)

/-- P₃-free graphs are forests, hence have at most |V| - 1 edges -/
axiom P3_free_is_forest (G : ErdosGraph n) (hP3 : G.isP3Free) :
    G.edges.card < G.vertices.card

/-
## Generalization to r-Products

For r ≥ 2, consider sets where no element divides products of r others.
-/

/-- Generalized condition: a ∤ b₁·b₂·...·bᵣ for r distinct bᵢ ≠ a -/
def satisfiesConditionR (A : Finset ℕ) (r : ℕ) : Prop :=
  ∀ a ∈ A, ∀ B : Finset ℕ, B ⊆ A → B.card = r → a ∉ B →
    ¬(a ∣ B.prod id)

/-- F_r(n): maximum size for r-product condition -/
noncomputable def F_r (n r : ℕ) : ℕ :=
  sSup { A.card | A : Finset ℕ // A ⊆ Icc_nat n ∧ satisfiesConditionR A r }

/-- Generalized conjecture: exponent becomes 2/(r+1) -/
axiom generalized_bounds (r : ℕ) (hr : r ≥ 2) :
  ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ ∀ n ≥ 2,
    (primePi n : ℝ) + c₁ * n^((2 : ℝ)/(r+1)) ≤ F_r n r ∧
    (F_r n r : ℝ) ≤ primePi n + c₂ * n^((2 : ℝ)/(r+1))

#check erdos793Conjecture
#check F_lower_bound
#check F_upper_bound
#check @satisfiesCondition
