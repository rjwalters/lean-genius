/-
# Erdős Problem #1056 OQ-01: New Solutions and Wilson's Theorem Connection

## Research Problem: erdos-1056
Extending known solutions for consecutive interval products ≡ 1 (mod p).

## What This Proves
1. **Wilson's constraint** for specific primes: (p-1)! ≡ -1 (mod p) for p=11,17,23,71.
2. **k=4 solution with p=23**: New verified solution.
3. **k=5 solution with p=71**: New verified solution.
4. **k=6 solution with p=71**: New verified solution.
5. **Solutions for all 2 ≤ k ≤ 6**: Comprehensive verification.

## New Results
Previously only k=2 (Erdős 1979, p=11) and k=3 (Makowski 1983, p=17) were verified.
We add k=4 (p=23), k=5 (p=71), and k=6 (p=71).

## Approach
Computational verification via native_decide. The key insight is that solutions
correspond to sequences of boundary points where consecutive factorials are
congruent modulo a prime.

Reference: https://erdosproblems.com/1056
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Erdos1056OQ01

open Finset

/- ## Part I: Core Definitions -/

/-- The product of integers in an interval [a, b). -/
def intervalProd (a b : ℕ) : ℕ :=
  (Finset.Ico a b).prod id

/-- A solution for k=2: prime p and 3 boundaries with both products ≡ 1 (mod p). -/
def HasSolution2 (p b₀ b₁ b₂ : ℕ) : Prop :=
  p.Prime ∧ b₀ < b₁ ∧ b₁ < b₂ ∧
  intervalProd b₀ b₁ % p = 1 ∧ intervalProd b₁ b₂ % p = 1

/-- A solution for k=3: prime p and 4 boundaries. -/
def HasSolution3 (p b₀ b₁ b₂ b₃ : ℕ) : Prop :=
  p.Prime ∧ b₀ < b₁ ∧ b₁ < b₂ ∧ b₂ < b₃ ∧
  intervalProd b₀ b₁ % p = 1 ∧ intervalProd b₁ b₂ % p = 1 ∧ intervalProd b₂ b₃ % p = 1

/-- A solution for k=4: prime p and 5 boundaries. -/
def HasSolution4 (p b₀ b₁ b₂ b₃ b₄ : ℕ) : Prop :=
  p.Prime ∧ b₀ < b₁ ∧ b₁ < b₂ ∧ b₂ < b₃ ∧ b₃ < b₄ ∧
  intervalProd b₀ b₁ % p = 1 ∧ intervalProd b₁ b₂ % p = 1 ∧
  intervalProd b₂ b₃ % p = 1 ∧ intervalProd b₃ b₄ % p = 1

/-- A solution for k=5: prime p and 6 boundaries. -/
def HasSolution5 (p b₀ b₁ b₂ b₃ b₄ b₅ : ℕ) : Prop :=
  p.Prime ∧ b₀ < b₁ ∧ b₁ < b₂ ∧ b₂ < b₃ ∧ b₃ < b₄ ∧ b₄ < b₅ ∧
  intervalProd b₀ b₁ % p = 1 ∧ intervalProd b₁ b₂ % p = 1 ∧
  intervalProd b₂ b₃ % p = 1 ∧ intervalProd b₃ b₄ % p = 1 ∧ intervalProd b₄ b₅ % p = 1

/-- A solution for k=6: prime p and 7 boundaries. -/
def HasSolution6 (p b₀ b₁ b₂ b₃ b₄ b₅ b₆ : ℕ) : Prop :=
  p.Prime ∧ b₀ < b₁ ∧ b₁ < b₂ ∧ b₂ < b₃ ∧ b₃ < b₄ ∧ b₄ < b₅ ∧ b₅ < b₆ ∧
  intervalProd b₀ b₁ % p = 1 ∧ intervalProd b₁ b₂ % p = 1 ∧
  intervalProd b₂ b₃ % p = 1 ∧ intervalProd b₃ b₄ % p = 1 ∧
  intervalProd b₄ b₅ % p = 1 ∧ intervalProd b₅ b₆ % p = 1

/-- Existence of a k-interval solution. -/
def ExistsSolution (k : ℕ) : Prop :=
  match k with
  | 2 => ∃ p b₀ b₁ b₂, HasSolution2 p b₀ b₁ b₂
  | 3 => ∃ p b₀ b₁ b₂ b₃, HasSolution3 p b₀ b₁ b₂ b₃
  | 4 => ∃ p b₀ b₁ b₂ b₃ b₄, HasSolution4 p b₀ b₁ b₂ b₃ b₄
  | 5 => ∃ p b₀ b₁ b₂ b₃ b₄ b₅, HasSolution5 p b₀ b₁ b₂ b₃ b₄ b₅
  | 6 => ∃ p b₀ b₁ b₂ b₃ b₄ b₅ b₆, HasSolution6 p b₀ b₁ b₂ b₃ b₄ b₅ b₆
  | _ => True  -- placeholder for other k

/- ## Part II: Wilson's Constraint for Key Primes -/

/-- Wilson's constraint for p=11: (11-1)! ≡ 10 (mod 11). -/
theorem wilson_11 : (Finset.Ico 1 11).prod id % 11 = 10 := by native_decide

/-- Wilson's constraint for p=17: (17-1)! ≡ 16 (mod 17). -/
theorem wilson_17 : (Finset.Ico 1 17).prod id % 17 = 16 := by native_decide

/-- Wilson's constraint for p=23: (23-1)! ≡ 22 (mod 23). -/
theorem wilson_23 : (Finset.Ico 1 23).prod id % 23 = 22 := by native_decide

/-- Wilson's constraint for p=71: (71-1)! ≡ 70 (mod 71). -/
theorem wilson_71 : (Finset.Ico 1 71).prod id % 71 = 70 := by native_decide

/- ## Part III: Individual Interval Verifications -/

-- k=2 intervals (Erdős 1979, p=11)
example : intervalProd 3 5 % 11 = 1 := by unfold intervalProd; native_decide
example : intervalProd 5 8 % 11 = 1 := by unfold intervalProd; native_decide

-- k=3 intervals (Makowski 1983, p=17)
example : intervalProd 2 6 % 17 = 1 := by unfold intervalProd; native_decide
example : intervalProd 6 12 % 17 = 1 := by unfold intervalProd; native_decide
example : intervalProd 12 16 % 17 = 1 := by unfold intervalProd; native_decide

-- k=4 intervals (NEW, p=23)
/-- 2·3·4 = 24 ≡ 1 (mod 23). -/
theorem k4_interval_1 : intervalProd 2 5 % 23 = 1 := by unfold intervalProd; native_decide

/-- 5·6·7·8 = 1680 ≡ 1 (mod 23). -/
theorem k4_interval_2 : intervalProd 5 9 % 23 = 1 := by unfold intervalProd; native_decide

/-- 9·10·11 = 990 ≡ 1 (mod 23). -/
theorem k4_interval_3 : intervalProd 9 12 % 23 = 1 := by unfold intervalProd; native_decide

/-- 12·13·...·21 ≡ 1 (mod 23). -/
theorem k4_interval_4 : intervalProd 12 22 % 23 = 1 := by unfold intervalProd; native_decide

-- k=5 intervals (NEW, p=71)
/-- 8·9 = 72 ≡ 1 (mod 71). -/
theorem k5_interval_1 : intervalProd 8 10 % 71 = 1 := by unfold intervalProd; native_decide

/-- 10·11·...·19 ≡ 1 (mod 71). -/
theorem k5_interval_2 : intervalProd 10 20 % 71 = 1 := by unfold intervalProd; native_decide

/-- 20·21·...·51 ≡ 1 (mod 71). -/
theorem k5_interval_3 : intervalProd 20 52 % 71 = 1 := by unfold intervalProd; native_decide

/-- 52·53·...·61 ≡ 1 (mod 71). -/
theorem k5_interval_4 : intervalProd 52 62 % 71 = 1 := by unfold intervalProd; native_decide

/-- 62·63 = 3906 ≡ 1 (mod 71). -/
theorem k5_interval_5 : intervalProd 62 64 % 71 = 1 := by unfold intervalProd; native_decide

-- k=6 intervals (NEW, p=71) - extends k=5 by splitting last interval
/-- 64·65·66·67·68·69·70 ≡ 1 (mod 71). -/
theorem k6_interval_6 : intervalProd 64 71 % 71 = 1 := by unfold intervalProd; native_decide

/- ## Part IV: Combined Solution Theorems -/

/-- **Erdős (1979): k=2 has a solution with p=11.** -/
theorem erdos_k2 : HasSolution2 11 3 5 8 := by
  unfold HasSolution2 intervalProd; decide

/-- **Makowski (1983): k=3 has a solution with p=17.** -/
theorem makowski_k3 : HasSolution3 17 2 6 12 16 := by
  unfold HasSolution3 intervalProd; decide

/-- **NEW: k=4 has a solution with p=23.**
    Boundaries: [2, 5, 9, 12, 22]
      [2,5): 2·3·4 = 24 ≡ 1 (mod 23)
      [5,9): 5·6·7·8 = 1680 ≡ 1 (mod 23)
      [9,12): 9·10·11 = 990 ≡ 1 (mod 23)
      [12,22): 12·13·...·21 ≡ 1 (mod 23) -/
theorem erdos_k4 : HasSolution4 23 2 5 9 12 22 := by
  unfold HasSolution4 intervalProd; native_decide

/-- **NEW: k=5 has a solution with p=71.**
    Boundaries: [8, 10, 20, 52, 62, 64]
      [8,10): 8·9 = 72 ≡ 1 (mod 71)
      [10,20): 10·11·...·19 ≡ 1 (mod 71)
      [20,52): 20·21·...·51 ≡ 1 (mod 71)
      [52,62): 52·53·...·61 ≡ 1 (mod 71)
      [62,64): 62·63 = 3906 ≡ 1 (mod 71) -/
theorem erdos_k5 : HasSolution5 71 8 10 20 52 62 64 := by
  unfold HasSolution5 intervalProd; native_decide

/-- **NEW: k=6 has a solution with p=71.**
    Boundaries: [8, 10, 20, 52, 62, 64, 71]
      Same as k=5 plus [64,71): 64·65·66·67·68·69·70 ≡ 1 (mod 71) -/
theorem erdos_k6 : HasSolution6 71 8 10 20 52 62 64 71 := by
  unfold HasSolution6 intervalProd; native_decide

/- ## Part V: Existence Proofs -/

/-- All solutions from k=2 to k=6 exist. -/
theorem exists_k2 : ExistsSolution 2 := ⟨11, 3, 5, 8, erdos_k2⟩
theorem exists_k3 : ExistsSolution 3 := ⟨17, 2, 6, 12, 16, makowski_k3⟩
theorem exists_k4 : ExistsSolution 4 := ⟨23, 2, 5, 9, 12, 22, erdos_k4⟩
theorem exists_k5 : ExistsSolution 5 := ⟨71, 8, 10, 20, 52, 62, 64, erdos_k5⟩
theorem exists_k6 : ExistsSolution 6 := ⟨71, 8, 10, 20, 52, 62, 64, 71, erdos_k6⟩

/-- Comprehensive summary: solutions verified for all 2 ≤ k ≤ 6. -/
theorem all_solutions_2_to_6 :
    ExistsSolution 2 ∧ ExistsSolution 3 ∧ ExistsSolution 4 ∧
    ExistsSolution 5 ∧ ExistsSolution 6 :=
  ⟨exists_k2, exists_k3, exists_k4, exists_k5, exists_k6⟩

/- ## Part VI: Factorial Pattern -/

/-- The factorial pattern: solutions correspond to sequences where
    (bᵢ-1)! are all congruent mod p. Here we verify for p=23:
    1! ≡ 4! ≡ 8! ≡ 11! ≡ 21! (mod 23). -/
theorem factorial_pattern_23 :
    Nat.factorial 1 % 23 = Nat.factorial 4 % 23 ∧
    Nat.factorial 4 % 23 = Nat.factorial 8 % 23 ∧
    Nat.factorial 8 % 23 = Nat.factorial 11 % 23 ∧
    Nat.factorial 11 % 23 = Nat.factorial 21 % 23 := by
  native_decide

/-- The factorial pattern for p=71:
    7! ≡ 9! ≡ 19! ≡ 51! ≡ 61! ≡ 63! ≡ 70! (mod 71). -/
theorem factorial_pattern_71 :
    Nat.factorial 7 % 71 = Nat.factorial 9 % 71 ∧
    Nat.factorial 9 % 71 = Nat.factorial 19 % 71 ∧
    Nat.factorial 19 % 71 = Nat.factorial 51 % 71 ∧
    Nat.factorial 51 % 71 = Nat.factorial 61 % 71 ∧
    Nat.factorial 61 % 71 = Nat.factorial 63 % 71 ∧
    Nat.factorial 63 % 71 = Nat.factorial 70 % 71 := by
  native_decide

/- ## Part VII: Summary of New Results -/

/-- The main theorem: solutions exist for k=4, k=5, and k=6.
    This extends the previously known k=2 (Erdős 1979) and k=3 (Makowski 1983). -/
theorem erdos_1056_new_solutions :
    ExistsSolution 4 ∧ ExistsSolution 5 ∧ ExistsSolution 6 :=
  ⟨exists_k4, exists_k5, exists_k6⟩

/-- Wilson's constraint verified for all primes used in solutions. -/
theorem wilson_constraints_verified :
    (Finset.Ico 1 11).prod id % 11 = 10 ∧
    (Finset.Ico 1 17).prod id % 17 = 16 ∧
    (Finset.Ico 1 23).prod id % 23 = 22 ∧
    (Finset.Ico 1 71).prod id % 71 = 70 :=
  ⟨wilson_11, wilson_17, wilson_23, wilson_71⟩

end Erdos1056OQ01
