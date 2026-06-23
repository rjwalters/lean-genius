/-
Erdős Problem #769: Cube Dissection into Homothetic Cubes

Let c(n) be the minimal integer such that if k ≥ c(n), then the n-dimensional
unit cube can be decomposed into k homothetic n-dimensional cubes.

Give good bounds for c(n). In particular, is it true that c(n) ≫ n^n?

**Status**: OPEN

**Known Results**:
- c(2) = 6 (the unit square cannot be decomposed into 2,3,4,5 squares)
- Hadwiger: c(n) ≥ 2^n + 2^{n-1}
- Connor-Marmorino (2018): c(n) ≥ 2^{n+1} - 1 for n ≥ 3
- Burgess-Erdős (1974): c(n) ≪ n^{n+1}
- Connor-Marmorino: c(n) ≤ 1.8n^{n+1} if n+1 is prime
- Connor-Marmorino: c(n) ≤ e²n^n otherwise

References:
- https://erdosproblems.com/769
- Connor-Marmorino (2018)
- Hudelson (1998)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

namespace Erdos769

/- ## Decomposability Predicate -/

/-- The n-dimensional unit cube can be decomposed into exactly k smaller
homothetic cubes. Cubes have side lengths in (0,1) and total volume 1. -/
def CanDecomposeCubeIntoKCubes (n k : ℕ) : Prop :=
  ∃ (cubes : Fin k → ℝ),
    (∀ i, 0 < cubes i ∧ cubes i < 1) ∧
    (∑ i : Fin k, (cubes i) ^ n) = 1

/- ## Cube Dissection Function -/

/-- c(n): the minimal k such that for all m ≥ k, the n-dimensional unit cube
can be decomposed into exactly m homothetic n-dimensional cubes.
Axiomatized since the existence proof requires the finite obstruction principle. -/
axiom cubeDissectionNumber (n : ℕ) : ℕ

/- ## The Dimension 2 Case -/

/-- c(2) = 6: the exact value in dimension 2. -/
axiom c_of_2 : cubeDissectionNumber 2 = 6

/- ## Hadwiger's Lower Bound -/

/-- c(n) ≥ 2^n + 2^{n-1} = 3·2^{n-1} (Hadwiger).
The first non-trivial lower bound, using geometric packing constraints. -/
axiom hadwiger_lower_bound :
    ∀ n ≥ 2, cubeDissectionNumber n ≥ 2^n + 2^(n-1)

/-- Hadwiger's bound restated: c(n) ≥ 3 · 2^{n-1}. -/
theorem hadwiger_explicit (n : ℕ) (hn : n ≥ 2) :
    cubeDissectionNumber n ≥ 3 * 2^(n-1) := by
  have h := hadwiger_lower_bound n hn
  omega

/- ## Connor-Marmorino Improved Lower Bound (2018) -/

/-- c(n) ≥ 2^{n+1} - 1 for n ≥ 3 (Connor-Marmorino 2018).
Improves Hadwiger since 2^{n+1} - 1 > 2^n + 2^{n-1}. -/
axiom connor_marmorino_lower (n : ℕ) (hn : n ≥ 3) :
    cubeDissectionNumber n ≥ 2^(n+1) - 1

/-- Connor-Marmorino is strictly stronger than Hadwiger for n ≥ 3. -/
theorem connor_vs_hadwiger (n : ℕ) (hn : n ≥ 3) :
    2^(n+1) - 1 > 2^n + 2^(n-1) := by
  omega

/- ## Upper Bounds -/

/-- Burgess-Erdős (1974): c(n) ≪ n^{n+1}. -/
axiom burgess_erdos_upper :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    (cubeDissectionNumber n : ℝ) ≤ C * (n : ℝ)^(n + 1)

/- ## Erdős's Conjecture -/

/-- Erdős's Conjecture: if n+1 is prime, then c(n) > n^n.
Erdős wrote: "I am certain that if n+1 is a prime then c(n) > n^n." -/
def erdosConjecture : Prop :=
  ∀ n : ℕ, n ≥ 2 → (n + 1).Prime → cubeDissectionNumber n > n^n

/-- The main open question: is c(n) ≫ n^n in general? -/
def mainQuestion : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
    (cubeDissectionNumber n : ℝ) ≥ C * (n : ℝ)^n

/- ## Packing vs Volume -/

/-- Beyond volume (Σ sideᵢⁿ = 1), cubes must pack geometrically.
There exist volume-valid configurations that cannot actually be packed. -/

/- ## Summary -/

/-- **Erdős Problem #769 Summary.**
Combines the key results: c(2) = 6 exactly, Connor-Marmorino lower bound,
and Burgess-Erdős upper bound. The main question c(n) ≫ n^n remains OPEN. -/
theorem erdos_769_summary :
    cubeDissectionNumber 2 = 6 ∧
    (∀ n ≥ 3, cubeDissectionNumber n ≥ 2^(n+1) - 1) ∧
    (∃ C : ℝ, C > 0 ∧ ∀ n ≥ 2,
      (cubeDissectionNumber n : ℝ) ≤ C * (n : ℝ)^(n + 1)) :=
  ⟨c_of_2, connor_marmorino_lower, burgess_erdos_upper⟩

end Erdos769
