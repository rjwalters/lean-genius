/-
  Erdős Problem #438: Square-Free Sumsets

  Source: https://erdosproblems.com/438
  Status: SOLVED (Khalfalah-Lodha-Szemerédi 2002)

  Statement:
  How large can A ⊆ {1,...,N} be if A+A contains no square numbers?

  Answer: |A| ≤ (11/32 + o(1))N

  Key Results:
  - Lower bound: Taking integers ≡ 1,5,9,13,14,17,21,25,26,29,30 (mod 32)
    gives |A| = (11/32)N
  - Lagarias-Odlyzko-Shearer (1983): |A| ≤ 0.475N for general sets
  - Khalfalah-Lodha-Szemerédi (2002): |A| ≤ (11/32 + o(1))N (tight bound)

  References:
  - [KLS02] Khalfalah-Lodha-Szemerédi (2002)
  - [LOS83] Lagarias-Odlyzko-Shearer (1983)

  Tags: number-theory, sumsets, squares, density, solved
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Algebra.Order.Field.Basic

open Finset Nat

namespace Erdos438

/- ## Part 1: Basic Definitions -/

/-- A number is a perfect square -/
def IsSquare (n : ℕ) : Prop := ∃ m : ℕ, n = m * m

/-- The sumset A+A of a set A -/
def sumset (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A).image (fun p => p.1 + p.2)

/-- A set is square-free sumset if A+A contains no squares -/
def IsSquareFreeSumset (A : Finset ℕ) : Prop :=
  ∀ n ∈ sumset A, ¬IsSquare n

/-- The maximum size of a square-free sumset in {1,...,N} -/
noncomputable def maxSquareFreeDensity (N : ℕ) : ℕ :=
  Finset.sup (Finset.filter
    (fun A => A ⊆ Finset.range (N + 1) ∧ IsSquareFreeSumset A)
    (Finset.powerset (Finset.range (N + 1))))
    Finset.card

/- ## Part 2: The Simple mod 3 Construction -/

/- ## Part 3: The Improved mod 32 Construction (Massias) -/

/-- The 11 residue classes mod 32 that give square-free sumsets -/
def massias_residues : Finset ℕ := {1, 5, 9, 13, 14, 17, 21, 25, 26, 29, 30}

/-- The Massias construction: integers in these residue classes mod 32 -/
def massias_construction (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n => n % 32 ∈ massias_residues)

/-- The Massias construction has square-free sumset -/
axiom massias_construction_works (N : ℕ) :
  IsSquareFreeSumset (massias_construction N)

/- ## Part 4: The Upper Bounds -/

/-- Khalfalah-Lodha-Szemerédi (2002): 11/32 is sharp in general -/
axiom kls_theorem :
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℕ,
    A ⊆ Finset.range (N + 1) → IsSquareFreeSumset A →
    (A.card : ℝ) ≤ ((11 : ℝ) / 32 + ε) * N

/- ## Part 5: Why 11/32? -/

/-- Squares mod 32 are: 0, 1, 4, 9, 16, 17, 25 -/
def squares_mod_32 : Finset ℕ := {0, 1, 4, 9, 16, 17, 25}

/-- There are 7 squares mod 32 -/
theorem squares_mod_32_count : squares_mod_32.card = 7 := by native_decide

/-- 11 is maximal: no 12 residues mod 32 can avoid all square sums -/
axiom massias_is_maximal :
  ∀ R : Finset ℕ, R ⊆ Finset.range 32 →
    (∀ a b : ℕ, a ∈ R → b ∈ R → (a + b) % 32 ∉ squares_mod_32) →
    R.card ≤ 11

/- ## Part 6: Summary -/

/-- Erdős Problem #438: SOLVED

    The maximum density of A ⊆ {1,...,N} with A+A square-free is 11/32.
    Combines: (1) Massias construction achieves 11/32,
    (2) KLS theorem proves 11/32 is tight,
    (3) 11 is the maximum number of residues mod 32 avoiding square sums. -/
theorem erdos_438_summary :
    (∀ N : ℕ, IsSquareFreeSumset (massias_construction N)) ∧
    (∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℕ,
      A ⊆ Finset.range (N + 1) → IsSquareFreeSumset A →
      (A.card : ℝ) ≤ ((11 : ℝ) / 32 + ε) * N) ∧
    (∀ R : Finset ℕ, R ⊆ Finset.range 32 →
      (∀ a b : ℕ, a ∈ R → b ∈ R → (a + b) % 32 ∉ squares_mod_32) →
      R.card ≤ 11) :=
  ⟨massias_construction_works, kls_theorem, massias_is_maximal⟩

end Erdos438
