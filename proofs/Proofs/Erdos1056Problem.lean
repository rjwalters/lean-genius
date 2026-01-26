/-!
# Erdős Problem #1056: Consecutive Interval Products ≡ 1 (mod p)

For k ≥ 2, does there exist a prime p and k consecutive intervals
I₁, ..., Iₖ (partitioning a range of integers) such that the product
of all integers in each interval is ≡ 1 (mod p)?

## Known Examples
- k=2, p=11: 3·4 ≡ 5·6·7 ≡ 1 (mod 11) — Erdős (1979)
- k=3, p=17: 2·3·4·5 ≡ 6·7·8·9·10·11 ≡ 12·13·14·15 ≡ 1 (mod 17) — Makowski (1983)

## Generalization (Noll–Simmons)
Do there exist arbitrarily many q₁ < ... < qₖ < p such that
q₁! ≡ q₂! ≡ ... ≡ qₖ! (mod p)?

## Status: OPEN
Guy's collection, Problem A15.

Reference: https://erdosproblems.com/1056
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- The product of integers in an interval [a, b). -/
def intervalProd (a b : ℕ) : ℕ :=
  (Finset.Ico a b).prod id

/-- A sequence of k+1 boundary points defining k consecutive intervals.
    Boundaries must be strictly increasing. -/
def IsValidBoundary (boundaries : List ℕ) (k : ℕ) : Prop :=
  boundaries.length = k + 1 ∧ boundaries.Chain' (· < ·)

/-- All k interval products are ≡ 1 (mod p). -/
def AllProductsCongruentOne (p : ℕ) (boundaries : List ℕ) (k : ℕ) : Prop :=
  IsValidBoundary boundaries k ∧
  ∀ i : Fin k, intervalProd (boundaries.get ⟨i.val, by omega⟩)
    (boundaries.get ⟨i.val + 1, by omega⟩) % p = 1

/-- A solution for a given k: a prime p and valid boundaries with all
    interval products ≡ 1 (mod p). -/
def HasSolution (k : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ ∃ boundaries : List ℕ,
    AllProductsCongruentOne p boundaries k

/-! ## Erdős's Observation: k = 2 -/

/-- Erdős (1979): k=2 has a solution with p=11.
    3·4 = 12 ≡ 1 (mod 11), 5·6·7 = 210 ≡ 1 (mod 11).
    Boundaries: [3, 5, 8], intervals: [3,5), [5,8). -/
axiom erdos_k2 : HasSolution 2

/-- Verification: 3·4 = 12 = 11 + 1 ≡ 1 (mod 11). -/
example : 3 * 4 % 11 = 1 := by native_decide

/-- Verification: 5·6·7 = 210 = 19·11 + 1 ≡ 1 (mod 11). -/
example : 5 * 6 * 7 % 11 = 1 := by native_decide

/-! ## Makowski's Extension: k = 3 -/

/-- Makowski (1983): k=3 has a solution with p=17.
    2·3·4·5 = 120 ≡ 1 (mod 17)
    6·7·8·9·10·11 = 332640 ≡ 1 (mod 17)
    12·13·14·15 = 32760 ≡ 1 (mod 17)
    Boundaries: [2, 6, 12, 16]. -/
axiom makowski_k3 : HasSolution 3

/-- Verification: 2·3·4·5 = 120, 120 mod 17 = 1. -/
example : 2 * 3 * 4 * 5 % 17 = 1 := by native_decide

/-- Verification: 12·13·14·15 = 32760, 32760 mod 17 = 1. -/
example : 12 * 13 * 14 * 15 % 17 = 1 := by native_decide

/-! ## The Main Conjecture -/

/-- Erdős Problem #1056: For every k ≥ 2, there exists a solution.
    That is, for every k there is a prime p and k consecutive intervals
    whose products are all ≡ 1 (mod p). -/
axiom erdos_1056_conjecture : ∀ k : ℕ, k ≥ 2 → HasSolution k

/-! ## Wilson's Theorem Connection -/

/-- Wilson's theorem: (p-1)! ≡ -1 (mod p) for prime p.
    If we partition {1, ..., p-1} into intervals with product ≡ 1 (mod p),
    then the product of all intervals is (p-1)! ≡ -1 (mod p).
    So the number of intervals must account for this sign. -/
axiom wilson_constraint (p : ℕ) (hp : p.Prime) :
    (Finset.Ico 1 p).prod id % p = p - 1

/-! ## Noll–Simmons Generalization -/

/-- The Noll–Simmons question: For arbitrarily large k, do there exist
    q₁ < q₂ < ... < qₖ < p (all less than prime p) such that
    q₁! ≡ q₂! ≡ ... ≡ qₖ! (mod p)?

    This generalizes the interval product question via the observation
    that consecutive interval products correspond to ratios of factorials. -/
axiom noll_simmons_conjecture :
    ∀ k : ℕ, ∃ p : ℕ, p.Prime ∧
      ∃ Q : Fin k → ℕ, (∀ i : Fin k, Q i < p) ∧
        (∀ i j : Fin k, Nat.factorial (Q i) % p = Nat.factorial (Q j) % p)

/-! ## Computational Aspects -/

/-- The solutions grow quickly: for k=2, p=11 suffices; for k=3, p=17.
    Finding solutions for larger k likely requires larger primes. -/
axiom known_small_solutions :
    HasSolution 2 ∧ HasSolution 3
