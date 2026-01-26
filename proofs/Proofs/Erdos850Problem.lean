/-!
# Erdős Problem #850: Same Prime Factors for Three Consecutive Shifts

Can there exist distinct positive integers x and y such that x,y have the
same prime factors, x+1,y+1 have the same prime factors, and x+2,y+2 also
have the same prime factors?

This is known as the Erdős-Woods conjecture. The answer is conjectured to
be no. Shorey and Tijdeman showed that under a strong form of the ABC
conjecture (due to Baker), the answer is indeed no.

For the weaker version requiring only two conditions (x,y and x+1,y+1),
solutions exist: x = 2(2^r - 1), y = x(x+2). The pair (75, 1215) also
satisfies both conditions (Makowski).

Reference: https://erdosproblems.com/850
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-! ## Same Prime Factors -/

/-- Two positive integers share the same set of prime divisors. -/
def SamePrimeFactors (x y : ℕ) : Prop :=
  x.primeFactors = y.primeFactors

/-! ## Main Conjecture -/

/-- Erdős Problem 850: Do there exist distinct x, y with the same prime
    factors for x,y and x+1,y+1 and x+2,y+2?
    Conjectured answer: no. -/
def ErdosProblem850 : Prop :=
  ¬∃ x y : ℕ, x ≠ y ∧
    SamePrimeFactors x y ∧
    SamePrimeFactors (x + 1) (y + 1) ∧
    SamePrimeFactors (x + 2) (y + 2)

/-! ## Weaker Variant: Two Consecutive Shifts -/

/-- The two-shift version: do there exist distinct x, y with same prime
    factors for both x,y and x+1,y+1? This IS solvable. -/
def TwoShiftSolvable : Prop :=
  ∃ x y : ℕ, x ≠ y ∧
    SamePrimeFactors x y ∧
    SamePrimeFactors (x + 1) (y + 1)

/-- The parametric family: x = 2(2^r - 1), y = x(x + 2) gives solutions
    to the two-shift version for r ≥ 2. -/
def ParametricFamily (r : ℕ) : ℕ × ℕ :=
  let x := 2 * (2 ^ r - 1)
  (x, x * (x + 2))

/-- The Makowski example: (75, 1215) solves the two-shift version. -/
def MakowskiExample : ℕ × ℕ := (75, 1215)

/-- 75 and 1215 are distinct. -/
theorem makowski_distinct : MakowskiExample.1 ≠ MakowskiExample.2 := by
  simp [MakowskiExample]

/-! ## Connection to ABC Conjecture -/

/-- The radical of a positive integer: the product of its distinct prime factors. -/
noncomputable def radical (n : ℕ) : ℕ :=
  n.primeFactors.prod id

/-- A strong form of the ABC conjecture (Baker's version). -/
def StrongABCConjecture : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ a b c : ℕ,
    0 < a → 0 < b → a + b = c → Nat.Coprime a b →
      (c : ℝ) ≤ C * ((radical (a * b * c) : ℝ)) ^ (1 + 1 / 6)

/-- Shorey-Tijdeman: under the strong ABC conjecture, Problem 850 holds. -/
axiom shorey_tijdeman :
    StrongABCConjecture → ErdosProblem850

/-! ## General k-Shift Version -/

/-- The generalized k-shift version: do there exist distinct x, y with
    same prime factors for all x+i, y+i where 0 ≤ i ≤ k? -/
def KShiftProblem (k : ℕ) : Prop :=
  ¬∃ x y : ℕ, x ≠ y ∧
    ∀ i : ℕ, i ≤ k → SamePrimeFactors (x + i) (y + i)

/-- Problem 850 is the k=2 case. -/
theorem problem850_is_2shift : ErdosProblem850 ↔ KShiftProblem 2 := by
  unfold ErdosProblem850 KShiftProblem
  constructor
  · intro h ⟨x, y, hne, hshift⟩
    apply h
    exact ⟨x, y, hne, hshift 0 (by omega), hshift 1 (by omega), hshift 2 (by omega)⟩
  · intro h ⟨x, y, hne, h0, h1, h2⟩
    apply h
    refine ⟨x, y, hne, fun i hi => ?_⟩
    interval_cases i <;> assumption

/-- Larger k makes the problem strictly harder: if k-shift has no solution,
    then (k-1)-shift also has no solution. -/
theorem kshift_monotone (k : ℕ) (h : KShiftProblem k) : KShiftProblem (k - 1) := by
  intro ⟨x, y, hne, hshift⟩
  apply h
  exact ⟨x, y, hne, fun i hi => hshift i (by omega)⟩

/-! ## Structural Observations -/

/-- SamePrimeFactors is reflexive. -/
theorem samePrimeFactors_refl (n : ℕ) : SamePrimeFactors n n :=
  rfl

/-- SamePrimeFactors is symmetric. -/
theorem samePrimeFactors_symm {x y : ℕ} (h : SamePrimeFactors x y) :
    SamePrimeFactors y x :=
  h.symm

/-- SamePrimeFactors is transitive. -/
theorem samePrimeFactors_trans {x y z : ℕ}
    (h1 : SamePrimeFactors x y) (h2 : SamePrimeFactors y z) :
    SamePrimeFactors x z :=
  h1.trans h2
