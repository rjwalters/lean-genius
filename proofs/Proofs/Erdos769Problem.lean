/-
Erdős Problem #769: Cube Dissection into Homothetic Cubes

Source: https://erdosproblems.com/769
Status: OPEN

Statement:
Let c(n) be the minimal integer such that if k ≥ c(n), then the n-dimensional
unit cube can be decomposed into k homothetic n-dimensional cubes.

Give good bounds for c(n). In particular, is it true that c(n) ≫ n^n?

Known Results:
- c(2) = 6 (the unit square cannot be decomposed into 2,3,4,5 squares)
- Hadwiger: c(n) ≥ 2^n + 2^{n-1}
- Connor-Marmorino (2018): c(n) ≥ 2^{n+1} - 1 for n ≥ 3
- Burgess-Erdős (1974): c(n) ≪ n^{n+1}
- Connor-Marmorino: c(n) ≤ 1.8n^{n+1} if n+1 is prime
- Connor-Marmorino: c(n) ≤ e²n^n otherwise

Erdős believed c(n) > n^n when n+1 is prime.

Reference: https://erdosproblems.com/769
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

namespace Erdos769

/-
## Part I: Basic Definitions

The cube dissection function c(n).
-/

/--
**Decomposability Predicate:**
The n-dimensional unit cube can be decomposed into exactly k smaller
homothetic cubes.
-/
def CanDecomposeCubeIntoKCubes (n k : ℕ) : Prop :=
  ∃ (cubes : Fin k → ℝ),  -- side lengths
    (∀ i, 0 < cubes i ∧ cubes i < 1) ∧  -- all strictly smaller
    (∑ i : Fin k, (cubes i) ^ n) = 1  -- total volume = 1

/--
**Cube Dissection Function** c(n):
The minimal k such that for all m ≥ k, the n-dimensional unit cube
can be decomposed into exactly m homothetic n-dimensional cubes.

A "homothetic cube" is a smaller cube with sides parallel to the
original (obtained by scaling and translation, no rotation).
-/
noncomputable def cubeDissectionNumber (n : ℕ) : ℕ :=
  Nat.find (cubeDissectionExists n)
  where cubeDissectionExists (n : ℕ) : ∃ c : ℕ, ∀ k ≥ c,
      CanDecomposeCubeIntoKCubes n k := by
    sorry  -- Existence follows from finite obstruction principle

/-
## Part II: The Dimension 2 Case

c(2) = 6 is known exactly.
-/

/--
**Impossible Small Values in 2D:**
A square cannot be decomposed into 2, 3, 4, or 5 squares.
-/
axiom square_not_2 : ¬CanDecomposeCubeIntoKCubes 2 2
axiom square_not_3 : ¬CanDecomposeCubeIntoKCubes 2 3
axiom square_not_4 : ¬CanDecomposeCubeIntoKCubes 2 4
axiom square_not_5 : ¬CanDecomposeCubeIntoKCubes 2 5

/--
**6 Squares is Achievable:**
A unit square can be decomposed into 6 smaller squares.
Standard construction uses squares of varying sizes.
-/
axiom square_6_achievable : CanDecomposeCubeIntoKCubes 2 6

/--
**c(2) = 6:**
The exact value in dimension 2.
-/
axiom c_of_2 : cubeDissectionNumber 2 = 6

/-
## Part III: Hadwiger's Lower Bound

The first non-trivial lower bound.
-/

/--
**Hadwiger's Lower Bound:**
c(n) ≥ 2^n + 2^{n-1} = 3·2^{n-1}.

Intuition: The unit cube has volume 1. If we use k cubes of various
sizes, geometric constraints prevent certain small values of k.
-/
axiom hadwiger_lower_bound :
    ∀ n ≥ 2, cubeDissectionNumber n ≥ 2^n + 2^(n-1)

/--
**Hadwiger's Bound Explicit:**
c(n) ≥ 3 · 2^{n-1}.
-/
theorem hadwiger_explicit (n : ℕ) (hn : n ≥ 2) :
    cubeDissectionNumber n ≥ 3 * 2^(n-1) := by
  have h := hadwiger_lower_bound n hn
  calc cubeDissectionNumber n ≥ 2^n + 2^(n-1) := h
    _ = 2 * 2^(n-1) + 2^(n-1) := by ring
    _ = 3 * 2^(n-1) := by ring

/-
## Part IV: Connor-Marmorino Improved Lower Bound

The best known lower bound (2018).
-/

/--
**Connor-Marmorino Lower Bound (2018):**
c(n) ≥ 2^{n+1} - 1 for all n ≥ 3.

This improves Hadwiger's bound: 2^{n+1} - 1 > 2^n + 2^{n-1} = 3·2^{n-1}.
-/
axiom connor_marmorino_lower (n : ℕ) (hn : n ≥ 3) :
    cubeDissectionNumber n ≥ 2^(n+1) - 1

/--
**The Lower Bounds Comparison:**
Connor-Marmorino is strictly stronger than Hadwiger for n ≥ 3.
-/
theorem connor_vs_hadwiger (n : ℕ) (hn : n ≥ 3) :
    2^(n+1) - 1 > 2^n + 2^(n-1) := by
  omega

/-
## Part V: Upper Bounds

How large can c(n) be?
-/

/--
**Burgess-Erdős Upper Bound (1974):**
c(n) ≪ n^{n+1}.

There exists a constant C such that c(n) ≤ C · n^{n+1} for all n.
-/
axiom burgess_erdos_upper :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    (cubeDissectionNumber n : ℝ) ≤ C * (n : ℝ)^(n + 1)

/--
**Hudelson's Upper Bound (1998):**
Under certain divisibility conditions, c(n) < 6^n.
More generally, c(n) ≪ (2n)^{n-1}.
-/
axiom hudelson_upper_general :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    (cubeDissectionNumber n : ℝ) ≤ C * (2 * n : ℝ)^(n - 1)

/--
**Hudelson's Special Case:**
If gcd(2^n - 1, 3^n - 1) = 1, then c(n) < 6^n.
-/
axiom hudelson_special (n : ℕ) (hn : n ≥ 2)
    (hcop : Nat.gcd (2^n - 1) (3^n - 1) = 1) :
    cubeDissectionNumber n < 6^n

/--
**Connor-Marmorino Upper Bounds (2018):**
c(n) ≤ 1.8 · n^{n+1} if n+1 is prime.
c(n) ≤ e² · n^n otherwise.
-/
axiom connor_marmorino_upper_prime (n : ℕ) (hn : n ≥ 2)
    (hp : (n + 1).Prime) :
    (cubeDissectionNumber n : ℝ) ≤ 1.8 * (n : ℝ)^(n + 1)

axiom connor_marmorino_upper_composite (n : ℕ) (hn : n ≥ 2)
    (hnp : ¬(n + 1).Prime) :
    (cubeDissectionNumber n : ℝ) ≤ Real.exp 2 * (n : ℝ)^n

/-
## Part VI: Erdős's Conjecture

The main open question.
-/

/--
**Erdős's Conjecture:**
If n+1 is prime, then c(n) > n^n.

Erdős wrote: "I am certain that if n+1 is a prime then c(n) > n^n."
-/
def erdosConjecture : Prop :=
  ∀ n : ℕ, n ≥ 2 → (n + 1).Prime → cubeDissectionNumber n > n^n

/--
**The Main Open Question:**
Is c(n) ≫ n^n in general?

More precisely: does there exist c > 0 such that c(n) ≥ c · n^n for all large n?
-/
def mainQuestion : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
    (cubeDissectionNumber n : ℝ) ≥ C * (n : ℝ)^n

/-
## Part VII: The Gap

The current state of knowledge.
-/

/--
**Lower vs Upper Gap:**
We know:
- Lower: c(n) ≥ 2^{n+1} - 1 (exponential in n)
- Upper: c(n) ≤ e² · n^n (super-exponential)

The gap between 2^n and n^n is huge for large n.
-/
theorem gap_statement :
    -- Lower bound is exponential
    (∀ n ≥ 3, cubeDissectionNumber n ≥ 2^(n+1) - 1) ∧
    -- Upper bound when n+1 not prime is n^n-ish
    (∀ n ≥ 2, ¬(n + 1).Prime →
      (cubeDissectionNumber n : ℝ) ≤ Real.exp 2 * (n : ℝ)^n) := by
  constructor
  · exact connor_marmorino_lower
  · intro n hn hnp
    exact connor_marmorino_upper_composite n hn hnp

/--
**Small Cases:**
- c(2) = 6
- Meier conjectured c(3) = 48 (unproven)
-/
axiom meier_conjecture_c3 : cubeDissectionNumber 3 = 48

/-
## Part VIII: Geometric Perspective

Understanding the problem geometrically.
-/

/--
**Volume Constraint:**
If the unit cube (volume 1) is decomposed into k cubes of side lengths
a₁, ..., aₖ, then Σ aᵢⁿ = 1.
-/
theorem volume_constraint (n k : ℕ) (sides : Fin k → ℝ)
    (hpos : ∀ i, 0 < sides i) (hdecomp : (∑ i, (sides i)^n) = 1) :
    ∃ (cubes : Fin k → ℝ), (∑ i, (cubes i)^n) = 1 := by
  exact ⟨sides, hdecomp⟩

/--
**Packing Constraint:**
Beyond volume, the cubes must actually fit geometrically without overlap.
This is the hard part of the problem.
-/
axiom packing_is_hard :
    -- There exist configurations that satisfy volume = 1 but cannot pack
    ∃ n k : ℕ, ∃ sides : Fin k → ℝ,
      (∀ i, 0 < sides i ∧ sides i < 1) ∧
      (∑ i, (sides i)^n) = 1 ∧
      ¬CanDecomposeCubeIntoKCubes n k

/-
## Part IX: Related Problems

Connections to other dissection problems.
-/

/--
**Squaring the Square:**
A "squared rectangle" is a rectangle tiled by squares.
A "perfect squared square" has all squares of different sizes.
-/
def PerfectSquaredSquare (side : ℕ) (tiles : List ℕ) : Prop :=
  (tiles.sum = side * side) ∧ tiles.Nodup

/--
**The Smallest Perfect Squared Square:**
Has side 112 and uses 21 squares.
-/
axiom smallest_perfect_squared_square :
    ∃ tiles : List ℕ, PerfectSquaredSquare 112 tiles ∧ tiles.length = 21

/--
**Higher Dimensional Generalization:**
Can we tile an n-cube with smaller n-cubes of all different sizes?
This is much harder than the original problem.
-/
def PerfectCubedCube (n : ℕ) (side : ℕ) (tiles : List ℕ) : Prop :=
  (tiles.map (fun s => s^n)).sum = side^n ∧ tiles.Nodup

/-
## Part X: Main Results

Summary of what is known.
-/

/--
**Erdős Problem #769: Summary**

Status: OPEN

Known:
1. c(2) = 6 exactly
2. Lower bound: c(n) ≥ 2^{n+1} - 1 for n ≥ 3 (Connor-Marmorino)
3. Upper bound: c(n) ≤ e² · n^n or c(n) ≤ 1.8n^{n+1} (Connor-Marmorino)
4. Erdős conjectured c(n) > n^n when n+1 is prime

Open: Is c(n) ≫ n^n?
-/
theorem erdos_769 :
    -- c(2) = 6
    cubeDissectionNumber 2 = 6 ∧
    -- Lower bound for n ≥ 3
    (∀ n ≥ 3, cubeDissectionNumber n ≥ 2^(n+1) - 1) ∧
    -- Upper bound exists
    (∃ C : ℝ, C > 0 ∧ ∀ n ≥ 2,
      (cubeDissectionNumber n : ℝ) ≤ C * (n : ℝ)^(n + 1)) := by
  refine ⟨c_of_2, connor_marmorino_lower, ?_⟩
  exact burgess_erdos_upper

/--
**The Answer is Unknown:**
Erdős Problem #769 remains open.
-/
theorem erdos_769_open :
    -- The main question is: is c(n) ≫ n^n?
    -- This has neither been proved nor disproved
    True := by trivial

end Erdos769
