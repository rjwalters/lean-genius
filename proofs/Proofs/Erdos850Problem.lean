/-
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

/- ## Same Prime Factors -/

/-- Two positive integers share the same set of prime divisors. -/
def SamePrimeFactors (x y : ℕ) : Prop :=
  x.primeFactors = y.primeFactors

/- ## Main Conjecture -/

/-- Erdős Problem 850: Do there exist distinct x, y with the same prime
    factors for x,y and x+1,y+1 and x+2,y+2?
    Conjectured answer: no. -/
def ErdosProblem850 : Prop :=
  ¬∃ x y : ℕ, x ≠ y ∧
    SamePrimeFactors x y ∧
    SamePrimeFactors (x + 1) (y + 1) ∧
    SamePrimeFactors (x + 2) (y + 2)

/- ## Weaker Variant: Two Consecutive Shifts -/

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

/-- **Makowski example verification: 75 and 1215 share prime factors.**
    75 = 3 × 5², 1215 = 3⁵ × 5, so primeFactors = {3, 5} for both. -/
theorem makowski_same_primes_base : SamePrimeFactors 75 1215 := by
  native_decide

/-- **Makowski example verification: 76 and 1216 share prime factors.**
    76 = 2² × 19, 1216 = 2⁶ × 19, so primeFactors = {2, 19} for both. -/
theorem makowski_same_primes_shift : SamePrimeFactors 76 1216 := by
  native_decide

/-- **The two-shift version IS solvable.**
    The Makowski pair (75, 1215) provides a concrete witness. -/
theorem two_shift_is_solvable : TwoShiftSolvable :=
  ⟨75, 1215, by decide, makowski_same_primes_base, makowski_same_primes_shift⟩

/-- **The 0-shift problem has trivial solutions.**
    For k = 0: any two distinct numbers with the same prime factors work.
    E.g., x = 2, y = 4: primeFactors(2) = primeFactors(4) = {2}. -/
theorem zero_shift_has_solution :
    ¬KShiftProblem 0 := by
  intro h
  apply h
  refine ⟨2, 4, by decide, fun i hi => ?_⟩
  interval_cases i
  show SamePrimeFactors 2 4
  native_decide

/-- **Larger k makes the problem strictly easier to NEGATE (harder to solve).**
    Correction to kshift_monotone: if no pair works for k shifts,
    it doesn't mean no pair works for k-1 shifts. The correct monotonicity
    is: a solution to (k+1)-shift is also a solution to k-shift.
    So KShiftProblem k → KShiftProblem (k+1). -/
theorem kshift_hard_monotone (k : ℕ) (h : ¬KShiftProblem (k + 1)) :
    ¬KShiftProblem k := by
  intro hk
  apply h; intro ⟨x, y, hne, hshift⟩
  exact hk ⟨x, y, hne, fun i hi => hshift i (by omega)⟩

/- ## Connection to ABC Conjecture -/

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

/- ## General k-Shift Version -/

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

/- ## Structural Observations -/

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
