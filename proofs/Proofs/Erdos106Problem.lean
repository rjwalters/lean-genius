/-
  Erdős Problem #106: Square Packing in the Unit Square

  Source: https://erdosproblems.com/106
  Status: OPEN

  Statement:
  Draw n squares inside the unit square with no common interior point.
  Let f(n) be the maximum possible sum of the side-lengths. Is f(k²+1) = k?

  Background:
  This problem dates back over 60 years. Erdős proved f(2) = 1 in an early
  paper for Hungarian high school students. The question asks whether adding
  one more square beyond a perfect k×k grid doesn't increase the sum.

  Known results:
  • f(2) = 1 (Erdős)
  • f(5) = 2 (Newman)
  • f(k²) = k (trivial from Cauchy-Schwarz: sum ≤ √(n·area) = √n)
  • f(k²+1) ≥ k (via k×k grid construction)
  • Halász bounds: f(k²+2c+1) ≥ k + c/k for c ≥ 1

  Erdős-Soifer conjecture: f(k²+2c+1) = k + c/k for |c| < k

  References:
  [Er94b] Erdős, "Some old and new problems in combinatorial geometry" (1994)
  [ErSo95] Erdős-Soifer, "Squares packing" (1995)
  [Ha84] Halász (1984) - improved lower bounds
  [BKU24] Baek-Koizumi-Ueoro (2024) - axis-parallel case

  Tags: discrete-geometry, packing, squares, optimization, open-problem
-/

import Mathlib

open Set Real

/-
## Squares in the Plane

A square is defined by its center and side length.
-/

/-- A square in the plane with sides parallel to axes -/
structure Square where
  center : ℝ × ℝ
  side : ℝ
  side_pos : side > 0

/-- The interior of a square -/
def Square.interior (s : Square) : Set (ℝ × ℝ) :=
  {p | |p.1 - s.center.1| < s.side / 2 ∧ |p.2 - s.center.2| < s.side / 2}

/-- The closure of a square (including boundary) -/
def Square.closure (s : Square) : Set (ℝ × ℝ) :=
  {p | |p.1 - s.center.1| ≤ s.side / 2 ∧ |p.2 - s.center.2| ≤ s.side / 2}

/-- Two squares have disjoint interiors -/
def DisjointInteriors (s₁ s₂ : Square) : Prop :=
  Disjoint s₁.interior s₂.interior

/-
## The Unit Square

The unit square [0,1] × [0,1].
-/

/-- The unit square -/
def unitSquare : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}

/-- A square is contained in the unit square -/
def ContainedInUnit (s : Square) : Prop :=
  s.closure ⊆ unitSquare

/-
## Valid Packings

A packing is a collection of squares with disjoint interiors inside the unit square.
-/

/-- A valid packing of n squares -/
structure Packing (n : ℕ) where
  squares : Fin n → Square
  contained : ∀ i, ContainedInUnit (squares i)
  disjoint : ∀ i j, i ≠ j → DisjointInteriors (squares i) (squares j)

/-- Sum of side lengths in a packing -/
noncomputable def Packing.sumSides {n : ℕ} (P : Packing n) : ℝ :=
  ∑ i : Fin n, (P.squares i).side

/-
## The Function f(n)

f(n) is the maximum sum of side lengths over all packings of n squares.
-/

/-- f(n): maximum sum of side lengths for n squares -/
noncomputable def f (n : ℕ) : ℝ :=
  sSup {s : ℝ | ∃ P : Packing n, P.sumSides = s}

/-- f is well-defined: bounded above by √n (Cauchy-Schwarz) -/
axiom f_bounded : ∀ n : ℕ, f n ≤ Real.sqrt n

/-- f is monotone increasing -/
axiom f_mono : ∀ n m : ℕ, n ≤ m → f n ≤ f m

/-
## Known Exact Values
-/

/-- f(1) = 1: one square fills the unit square -/
axiom f_1 : f 1 = 1

/-- f(2) = 1 (Erdős) -/
axiom f_2 : f 2 = 1

/-- f(4) = 2: four squares of side 1/2 -/
axiom f_4 : f 4 = 2

/-- f(5) = 2 (Newman) -/
axiom f_5 : f 5 = 2

/-- f(9) = 3: nine squares of side 1/3 -/
axiom f_9 : f 9 = 3

/-
## Perfect Squares: f(k²) = k
-/

/-- For perfect squares, f(k²) = k -/
axiom f_perfect_square : ∀ k : ℕ, k ≥ 1 → f (k^2) = k

/-- Cauchy-Schwarz upper bound: f(n) ≤ √n -/
theorem f_upper_bound (n : ℕ) : f n ≤ Real.sqrt n := f_bounded n

/-- The k×k grid achieves f(k²) = k -/
theorem perfect_square_achieved (k : ℕ) (hk : k ≥ 1) :
    ∃ P : Packing (k^2), P.sumSides = k := by
  sorry

/-
## The Main Conjecture: f(k²+1) = k
-/

/-- Lower bound: f(k²+1) ≥ k from the k×k grid -/
axiom f_k2_plus_1_lower : ∀ k : ℕ, k ≥ 1 → f (k^2 + 1) ≥ k

/-- The main conjecture: f(k²+1) = k -/
def erdos106Conjecture : Prop :=
  ∀ k : ℕ, k ≥ 1 → f (k^2 + 1) = k

/-- Equivalently: one extra square doesn't help -/
theorem conjecture_equiv :
    erdos106Conjecture ↔ ∀ k ≥ 1, f (k^2 + 1) = f (k^2) := by
  constructor
  · intro h k hk
    rw [h k hk, f_perfect_square k hk]
  · intro h k hk
    rw [h k hk, f_perfect_square k hk]

/-
## Halász Lower Bounds

f(k²+2c+1) ≥ k + c/k for c ≥ 1
-/

/-- Halász bound for odd increments -/
axiom halasz_odd : ∀ k c : ℕ, k ≥ 1 → c ≥ 1 →
  f (k^2 + 2*c + 1) ≥ k + (c : ℝ) / k

/-- Halász bound for even increments -/
axiom halasz_even : ∀ k c : ℕ, k ≥ 1 → c ≥ 1 →
  f (k^2 + 2*c) ≥ k + (c : ℝ) / (k + 1)

/-
## The Erdős-Soifer Conjecture

f(k²+2c+1) = k + c/k for |c| < k
-/

/-- The stronger Erdős-Soifer conjecture -/
def erdosSoiferConjecture : Prop :=
  ∀ k : ℕ, k ≥ 1 → ∀ c : ℤ, |c| < k →
    f (k^2 + (2*c + 1).toNat) = k + (c : ℝ) / k

/-- Praton's equivalence: main conjecture ↔ Erdős-Soifer conjecture -/
axiom praton_equivalence :
  erdos106Conjecture ↔ erdosSoiferConjecture

/-
## Axis-Parallel Case

When all squares have sides parallel to the unit square.
-/

/-- g(n): max sum with axis-parallel constraint (always satisfied in our def) -/
noncomputable def g (n : ℕ) : ℝ := f n

/-- Baek-Koizumi-Ueoro (2024): g(k²+1) = k for axis-parallel squares -/
axiom bku_theorem : ∀ k : ℕ, k ≥ 1 → g (k^2 + 1) = k

/-
## When Does f(n+1) = f(n)?
-/

/-- Set of n where adding one square doesn't help -/
def plateauSet : Set ℕ := {n | f (n + 1) = f n}

/-- 1 ∈ plateauSet since f(2) = f(1) = 1 -/
theorem one_in_plateau : 1 ∈ plateauSet := by
  unfold plateauSet
  simp only [Set.mem_setOf_eq]
  rw [f_2, f_1]

/-- k² ∈ plateauSet ↔ main conjecture for that k -/
theorem perfect_square_plateau (k : ℕ) (hk : k ≥ 1) :
    k^2 ∈ plateauSet ↔ f (k^2 + 1) = k := by
  unfold plateauSet
  simp only [Set.mem_setOf_eq]
  rw [f_perfect_square k hk]

/-
## The Open Problem
-/

/-- The main open question -/
def erdos106OpenProblem : Prop := erdos106Conjecture

#check f
#check erdos106Conjecture
#check erdosSoiferConjecture
#check halasz_odd
#check bku_theorem
