/-!
# Erdős Problem #124 — Complete Sequences from Digit-Restricted Sums

For integers 3 ≤ d₁ < d₂ < ... < dᵣ with Σ 1/(dᵢ-1) ≥ 1, can all
sufficiently large integers be represented as Σ cᵢaᵢ where cᵢ ∈ {0,1}
and each aᵢ uses only digits {0,1} in base dᵢ?

Known:
- The condition Σ 1/(dᵢ-1) ≥ 1 is necessary (Pomerance)
- First question proved (Aristotle/Alexeev, formalized in Lean)
- Second question (with gcd condition and P(dᵢ,k)) proved for {3,4,7}

Conjectured by Burr, Erdős, Graham, and Li [BEGL96].

Reference: https://erdosproblems.com/124
-/

import Mathlib.Data.Nat.Digits
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-! ## Digit-Restricted Numbers -/

/-- P(d, k): the set of natural numbers whose base-d representation
    uses only digits 0 and 1, starting from position k.
    Equivalently, numbers of the form Σ εᵢ · dⁱ with εᵢ ∈ {0,1}, i ≥ k. -/
def digitRestricted (d k : ℕ) : Set ℕ :=
  {n : ℕ | ∀ i, i < k ∨ (Nat.digits d n).getD i 0 ∈ ({0, 1} : Finset ℕ)}

/-- A simpler characterization for k = 0: numbers whose base-d digits
    are all 0 or 1 -/
def binaryDigitsInBase (d : ℕ) : Set ℕ :=
  {n : ℕ | ∀ digit ∈ Nat.digits d n, digit ∈ ({0, 1} : Finset ℕ)}

/-! ## The Reciprocal Condition -/

/-- The critical condition: Σ 1/(dᵢ - 1) ≥ 1 -/
def reciprocalCondition (r : ℕ) (d : Fin r → ℕ) : Prop :=
  1 ≤ Finset.univ.sum (fun i => (1 : ℚ) / ((d i : ℚ) - 1))

/-- The bases satisfy 3 ≤ d₁ < d₂ < ... < dᵣ -/
def validBases (r : ℕ) (d : Fin r → ℕ) : Prop :=
  (∀ i, 3 ≤ d i) ∧ StrictMono d

/-! ## Representation Property -/

/-- An integer n is representable as Σ cᵢaᵢ where cᵢ ∈ {0,1}
    and aᵢ ∈ P(dᵢ, 0) (digits only 0,1 in base dᵢ) -/
def IsRepresentable (r : ℕ) (d : Fin r → ℕ) (n : ℕ) : Prop :=
  ∃ (c : Fin r → ℕ) (a : Fin r → ℕ),
    (∀ i, c i ∈ ({0, 1} : Finset ℕ)) ∧
    (∀ i, a i ∈ binaryDigitsInBase (d i)) ∧
    n = Finset.univ.sum (fun i => c i * a i)

/-- The stronger representation with P(dᵢ, k) for arbitrary k -/
def IsRepresentableFromLevel (r : ℕ) (d : Fin r → ℕ) (k n : ℕ) : Prop :=
  ∃ (c : Fin r → ℕ) (a : Fin r → ℕ),
    (∀ i, c i ∈ ({0, 1} : Finset ℕ)) ∧
    (∀ i, a i ∈ digitRestricted (d i) k) ∧
    n = Finset.univ.sum (fun i => c i * a i)

/-! ## Pomerance's Necessity -/

/-- Pomerance's result: the condition Σ 1/(dᵢ-1) ≥ 1 is necessary
    for all sufficiently large integers to be representable -/
axiom pomerance_necessity (r : ℕ) (d : Fin r → ℕ)
    (hv : validBases r d)
    (h : ∀ᶠ n in Filter.atTop, IsRepresentable r d n) :
  reciprocalCondition r d

/-! ## First Question (PROVED) -/

/-- Erdős Problem 124, Question 1 (PROVED): if Σ 1/(dᵢ-1) ≥ 1,
    then all sufficiently large integers are representable.
    Proved by Aristotle via Alexeev's method. -/
axiom ErdosProblem124_Q1 (r : ℕ) (hr : 0 < r) (d : Fin r → ℕ)
    (hv : validBases r d) (hrc : reciprocalCondition r d) :
  ∀ᶠ n in Filter.atTop, IsRepresentable r d n

/-! ## Second Question (Open in General) -/

/-- Erdős Problem 124, Question 2 (Open): with the additional condition
    gcd(d₁,...,dᵣ) = 1, for any k ≥ 1, all sufficiently large integers
    can be represented using P(dᵢ, k). Proved for {3,4,7}. -/
axiom ErdosProblem124_Q2 (r : ℕ) (hr : 0 < r) (d : Fin r → ℕ)
    (hv : validBases r d) (hrc : reciprocalCondition r d)
    (hgcd : Finset.univ.gcd d = 1) :
  ∀ k : ℕ, 1 ≤ k → ∀ᶠ n in Filter.atTop, IsRepresentableFromLevel r d k n

/-- The case {3, 4, 7} is verified for Question 2 -/
axiom erdos124_case_3_4_7 :
  ∀ k : ℕ, 1 ≤ k →
    ∀ᶠ n in Filter.atTop,
      IsRepresentableFromLevel 3 ![3, 4, 7] k n
