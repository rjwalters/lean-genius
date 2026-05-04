/-
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
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

namespace Erdos1056

open Finset

/- ## Part I: Core Definitions -/

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

/- ## Part II: Proved Infrastructure Lemmas -/

/-- The interval product of an empty range is 1. -/
theorem intervalProd_empty {a b : ℕ} (h : b ≤ a) :
    intervalProd a b = 1 := by
  unfold intervalProd
  rw [Finset.Ico_eq_empty (by omega)]
  simp

/-- A valid boundary list has at least one element. -/
theorem IsValidBoundary.length_pos {boundaries : List ℕ} {k : ℕ}
    (h : IsValidBoundary boundaries k) :
    0 < boundaries.length := by
  have := h.1; omega

/-- In a valid boundary list, boundaries are strictly increasing. -/
theorem IsValidBoundary.chain {boundaries : List ℕ} {k : ℕ}
    (h : IsValidBoundary boundaries k) :
    boundaries.Chain' (· < ·) := h.2

/-- The number of boundary points is k + 1. -/
theorem IsValidBoundary.intervals_count {boundaries : List ℕ} {k : ℕ}
    (h : IsValidBoundary boundaries k) :
    boundaries.length = k + 1 := h.1

/-- Interval products are positive when the interval starts at ≥ 1. -/
theorem intervalProd_pos {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    0 < intervalProd a b := by
  unfold intervalProd
  apply Finset.prod_pos
  intro i hi
  rw [Finset.mem_Ico] at hi
  simp [id]
  omega

/-- Multiplying two numbers both ≡ 1 mod p gives a product ≡ 1 mod p. -/
theorem mod_mul_of_mod_eq_one {a b p : ℕ} (ha : a % p = 1) (hb : b % p = 1) :
    (a * b) % p = 1 := by
  rw [Nat.mul_mod, ha, hb]
  simp

/- ## Part III: Verified Solutions (Proved) -/

/-- Verification: 3·4 = 12 ≡ 1 (mod 11). -/
example : 3 * 4 % 11 = 1 := by native_decide

/-- Verification: 5·6·7 = 210 ≡ 1 (mod 11). -/
example : 5 * 6 * 7 % 11 = 1 := by native_decide

/-- Verification: 2·3·4·5 = 120 ≡ 1 (mod 17). -/
example : 2 * 3 * 4 * 5 % 17 = 1 := by native_decide

/-- Verification: 6·7·8·9·10·11 = 332640 ≡ 1 (mod 17). -/
example : 6 * 7 * 8 * 9 * 10 * 11 % 17 = 1 := by native_decide

/-- Verification: 12·13·14·15 = 32760 ≡ 1 (mod 17). -/
example : 12 * 13 * 14 * 15 % 17 = 1 := by native_decide

/-- **Erdős (1979): k=2 has a solution with p=11.**
    3·4 = 12 ≡ 1 (mod 11), 5·6·7 = 210 ≡ 1 (mod 11).
    Boundaries: [3, 5, 8], intervals: [3,5), [5,8). -/
theorem erdos_k2 : HasSolution 2 := by
  unfold HasSolution AllProductsCongruentOne IsValidBoundary intervalProd
  exact ⟨11, by decide, [3, 5, 8],
    ⟨⟨by decide, by decide⟩,
     fun i => by fin_cases i <;> native_decide⟩⟩

/-- **Makowski (1983): k=3 has a solution with p=17.**
    2·3·4·5 = 120 ≡ 1 (mod 17)
    6·7·8·9·10·11 = 332640 ≡ 1 (mod 17)
    12·13·14·15 = 32760 ≡ 1 (mod 17)
    Boundaries: [2, 6, 12, 16]. -/
theorem makowski_k3 : HasSolution 3 := by
  unfold HasSolution AllProductsCongruentOne IsValidBoundary intervalProd
  exact ⟨17, by decide, [2, 6, 12, 16],
    ⟨⟨by decide, by decide⟩,
     fun i => by fin_cases i <;> native_decide⟩⟩

/-- Solutions for k=2 and k=3 are both verified. -/
theorem known_small_solutions : HasSolution 2 ∧ HasSolution 3 :=
  ⟨erdos_k2, makowski_k3⟩

/-- The existence of a k=2 solution shows the problem is non-trivial. -/
theorem problem_nontrivial : ∃ k : ℕ, k ≥ 2 ∧ HasSolution k :=
  ⟨2, le_refl _, erdos_k2⟩

/-- Both known solutions use odd primes. -/
theorem known_solutions_use_odd_primes :
    (∃ p : ℕ, p.Prime ∧ 2 < p ∧ ∃ b, AllProductsCongruentOne p b 2) ∧
    (∃ p : ℕ, p.Prime ∧ 2 < p ∧ ∃ b, AllProductsCongruentOne p b 3) := by
  constructor
  · exact ⟨11, by decide, by omega, [3, 5, 8], by
      unfold AllProductsCongruentOne IsValidBoundary intervalProd
      exact ⟨⟨by decide, by decide⟩, fun i => by fin_cases i <;> native_decide⟩⟩
  · exact ⟨17, by decide, by omega, [2, 6, 12, 16], by
      unfold AllProductsCongruentOne IsValidBoundary intervalProd
      exact ⟨⟨by decide, by decide⟩, fun i => by fin_cases i <;> native_decide⟩⟩

/- ## Part IV: Wilson's Theorem Connection -/

/-- Wilson's theorem constraint for p=11:
    (11-1)! ≡ -1 (mod 11), i.e., product of [1,11) ≡ 10 (mod 11). -/
theorem wilson_constraint_11 : (Finset.Ico 1 11).prod id % 11 = 11 - 1 := by
  native_decide

/-- Wilson's theorem constraint for p=17:
    (17-1)! ≡ -1 (mod 17), i.e., product of [1,17) ≡ 16 (mod 17). -/
theorem wilson_constraint_17 : (Finset.Ico 1 17).prod id % 17 = 17 - 1 := by
  native_decide

/-- General Wilson's theorem constraint: for any prime p,
    (p-1)! ≡ -1 (mod p), i.e., the product of [1,p) ≡ p-1 (mod p).
    This constrains interval product decompositions: if all intervals
    covering [1,p) have product ≡ 1 (mod p), the total is 1^k = 1,
    but Wilson says total = p-1 ≡ -1. So non-trivial solutions must
    avoid partitioning all of {1, ..., p-1}. -/
theorem wilson_constraint (p : ℕ) (hp : p.Prime) :
    (Finset.Ico 1 p).prod id % p = p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- Step 1: Relate Finset.Ico 1 p product to (p-1)!
  -- ∏ i in Ico 1 p, i = ∏ i in range (p-1), (i+1) = (p-1)!
  have h_eq : (Finset.Ico 1 p).prod id = (p - 1).factorial := by
    rw [Finset.prod_Ico_eq_prod_range]
    simp only [id]
    symm
    induction p - 1 with
    | zero => simp
    | succ n ih => rw [Finset.prod_range_succ, Nat.factorial_succ, ih, add_comm]
  rw [h_eq]
  -- Step 2: (p-1)! % p = p - 1 by Wilson's theorem
  have h := ZMod.wilsons_lemma p
  have hval := congr_arg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_neg_one'] at hval
  exact hval

/- ## Part V: The Main Conjecture -/

/-- **Erdős Problem #1056:** For every k ≥ 2, there exists a solution.
    That is, for every k there is a prime p and k consecutive intervals
    whose products are all ≡ 1 (mod p). [OPEN] -/
axiom erdos_1056_conjecture : ∀ k : ℕ, k ≥ 2 → HasSolution k

/- ## Part VI: Noll–Simmons Generalization -/

/-- The Noll–Simmons question: For arbitrarily large k, do there exist
    q₁ < q₂ < ... < qₖ < p (all less than prime p) such that
    q₁! ≡ q₂! ≡ ... ≡ qₖ! (mod p)?

    This generalizes the interval product question: if the product of
    [aᵢ, aᵢ₊₁) ≡ 1 (mod p), then aᵢ₊₁!/aᵢ! ≡ 1 (mod p),
    so aᵢ! ≡ aᵢ₊₁! (mod p). -/
/- ## Part VII: Summary -/

/-- Comprehensive summary: k=2 and k=3 are verified, with Wilson
    constraints proved for the relevant primes. -/
theorem erdos_1056_summary :
    HasSolution 2 ∧ HasSolution 3 ∧
    ((Finset.Ico 1 11).prod id % 11 = 11 - 1) ∧
    ((Finset.Ico 1 17).prod id % 17 = 17 - 1) :=
  ⟨erdos_k2, makowski_k3, wilson_constraint_11, wilson_constraint_17⟩

end Erdos1056
