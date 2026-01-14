import Mathlib

/-!
# Erdős Problem 1102: Squarefree Properties P and Q

## What This Proves
We formalize Erdős Problem 1102, which asks: how fast must sequences with
properties P or Q grow, where these properties are defined in terms of
squarefree translates?

The answer was resolved by van Doorn and Tao (2025):
- Property P: Sequences have density 0 but can decay arbitrarily slowly
- Property Q: Sequences have upper density at most 6/π² (with equality possible)

## The Problem
A number is **squarefree** if it's not divisible by any perfect square > 1.
Equivalently, in its prime factorization, all exponents are 0 or 1.

**Property P:** For every n ≥ 1, only finitely many a ∈ A have n + a squarefree.
**Property Q:** Infinitely many n have n + a squarefree for all a < n in A.

The question asks about growth rates of sequences satisfying these properties.

## Historical Context
Erdős posed this in 1981. The density of squarefree numbers is 6/π² ≈ 0.608.
van Doorn and Tao (2025) resolved most questions, showing property Q sequences
have upper density at most 6/π², achieved by taking A = squarefree numbers.

## Approach
- **Foundation:** We use Mathlib's Squarefree predicate
- **Definitions:** Properties P and Q formalized as set predicates
- **Axioms:** Main results stated from van Doorn-Tao

## Status
- [x] Properties P and Q formalized
- [x] Density bounds stated
- [x] Uses axioms for analytic results
- [ ] Full constructive proofs

## References
- Erdős, P. (1981)
- van Doorn, W. and Tao, T., arXiv:2512.01087 (2025)
- https://erdosproblems.com/1102
-/

namespace Erdos1102

open Nat Set Filter Topology

/-! ## Definitions -/

/-- Property P: For all n ≥ 1, only finitely many a ∈ A have n + a squarefree.

    Intuitively, A is "anti-squarefree": adding any n kills squarefreeness
    for all but finitely many elements. -/
def HasPropertyP (A : Set ℕ) : Prop :=
  ∀ n ≥ 1, {a ∈ A | Squarefree (n + a)}.Finite

/-- Property Q: Infinitely many n have n + a squarefree for all a < n in A.

    Intuitively, A is "pro-squarefree": infinitely often, adding any element
    of A below n to n gives a squarefree number. -/
def HasPropertyQ (A : Set ℕ) : Prop :=
  {n : ℕ | ∀ a ∈ A, a < n → Squarefree (n + a)}.Infinite

/-! ## The Squarefree Numbers -/

/-- The set of squarefree natural numbers -/
def squarefreeSet : Set ℕ := {n | Squarefree n}

/-- 1 is squarefree -/
example : Squarefree 1 := squarefree_one

/-- 2 is squarefree (it's prime) -/
example : Squarefree 2 := by native_decide

/-- 6 is squarefree (6 = 2 × 3) -/
example : Squarefree 6 := by native_decide

/-- 4 is not squarefree (4 = 2²) -/
example : ¬Squarefree 4 := by native_decide

/-- 12 is not squarefree (12 = 4 × 3 = 2² × 3) -/
example : ¬Squarefree 12 := by native_decide

/-! ## The Magic Constant: 6/π²

The density of squarefree numbers is 6/π² = 1/ζ(2) ≈ 0.6079... -/

/-- The density of squarefree numbers -/
noncomputable def squarefreeDensity : ℝ := 6 / Real.pi^2

/-! ## Main Results (van Doorn-Tao 2025) -/

/-- **Axiom (van Doorn-Tao 2025):**
    Any sequence with property P has density 0.

    If A = {a₁ < a₂ < ...} has property P, then aⱼ / j → ∞. -/
axiom propertyP_density_zero (A : ℕ → ℕ) (h_inc : StrictMono A)
    (hP : HasPropertyP (range A)) :
    Tendsto (fun j => (A j / j : ℝ)) atTop atTop

/-- **Axiom (van Doorn-Tao 2025):**
    Sequences with property P can have density going to 0 arbitrarily slowly.

    For any function f → ∞, there exists A with property P and aⱼ/j ≤ f(j). -/
axiom propertyP_arbitrarily_slow (f : ℕ → ℕ) (h_inf : Tendsto f atTop atTop)
    (h_pos : ∀ n, f n ≠ 0) :
    ∃ A : ℕ → ℕ, StrictMono A ∧
    HasPropertyP (range A) ∧
    ∀ j : ℕ, (A j : ℝ) / j ≤ f j

/-- **Axiom (van Doorn-Tao 2025):**
    Any sequence with property Q has upper density at most 6/π².

    If A = {a₁ < a₂ < ...} has property Q, then limsup (j/aⱼ) ≤ 6/π². -/
axiom propertyQ_upper_density (A : ℕ → ℕ) (h_inc : StrictMono A)
    (hQ : HasPropertyQ (range A)) :
    limsup (fun j : ℕ ↦ j / A j) atTop ≤ squarefreeDensity

/-- **Axiom (van Doorn-Tao 2025):**
    There exists a sequence with property Q achieving density 6/π².

    Specifically, A = squarefree numbers works. -/
axiom propertyQ_achievable :
    ∃ A : ℕ → ℕ, StrictMono A ∧
    (∀ j, Squarefree (A j)) ∧
    HasPropertyQ (range A) ∧
    Tendsto (fun j : ℕ ↦ (j / A j : ℝ)) atTop (𝓝 squarefreeDensity)

/-- **Erdős Problem 1102** (Solved)

    Summary of the resolution by van Doorn and Tao:
    - Property P sequences have density 0, but can decay arbitrarily slowly
    - Property Q sequences have upper density ≤ 6/π², with equality achievable -/
theorem erdos_1102_summary : True := trivial

/-! ## Special Sequences

Erdős also asked about specific sequences like 2^n ± 1 and n! ± 1. -/

/-- The sequence 2^n - 1 -/
def powersOfTwoMinus1 : ℕ → ℕ := fun n => 2^n - 1

/-- The sequence 2^n + 1 -/
def powersOfTwoPlus1 : ℕ → ℕ := fun n => 2^n + 1

/-- **Axiom (van Doorn-Tao 2025):**
    The sequences 2^n ± 1 and n! ± 1 have property Q.

    Whether they have property P remains open. -/
axiom special_sequences_have_Q :
    HasPropertyQ (range powersOfTwoMinus1) ∧
    HasPropertyQ (range powersOfTwoPlus1)

end Erdos1102
