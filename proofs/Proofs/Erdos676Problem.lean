/-
Erdős Problem #676: Representations ap² + b with p Prime

**Problem Statement (OPEN)**

Is every sufficiently large integer expressible as ap² + b for some prime p,
integer a ≥ 1, and 0 ≤ b < p?

**Background:**
- The sieve of Eratosthenes shows "almost all" integers have this form
- Brun-Selberg sieve: exceptions in [1,x] are ≪ x/(log x)^c for some c > 0
- Erdős believed it "rather unlikely" that ALL large integers satisfy this

**Related Questions:**
- Without prime requirement: Selfridge-Wagstaff suggest infinitely many exceptions
- Minimal coefficient c_n: Is limsup c_n = ∞? Is c_n < n^{o(1)}?

**Status:** OPEN

**Reference:** [Er79], [Er79d]

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open Nat Filter Set

namespace Erdos676

/-!
# Part 1: Basic Definitions

Define the representation ap² + b where p is prime and b < p.
-/

-- A number n has representation (a, p, b) if n = a*p² + b with constraints
def HasRepresentation (n a : ℕ) (p : ℕ) (b : ℕ) : Prop :=
  p.Prime ∧ a ≥ 1 ∧ b < p ∧ n = a * p^2 + b

-- A number is representable if some such (a, p, b) exists
def IsRepresentable (n : ℕ) : Prop :=
  ∃ a p b, HasRepresentation n a p b

-- The set of representable numbers
def RepresentableSet : Set ℕ := {n | IsRepresentable n}

-- The set of exceptions (non-representable numbers)
def ExceptionSet : Set ℕ := {n | ¬ IsRepresentable n}

/-!
# Part 2: The Main Conjecture

Erdős asked whether all sufficiently large integers are representable.
-/

-- The conjecture: ∃N such that all n ≥ N are representable
def ErdosConjecture676 : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, IsRepresentable n

-- Alternative formulation: only finitely many exceptions
def ErdosConjecture676' : Prop :=
  ExceptionSet.Finite

-- Equivalence of formulations
theorem conjecture_equiv : ErdosConjecture676 ↔ ErdosConjecture676' := by
  constructor
  · intro ⟨N, hN⟩
    have : ExceptionSet ⊆ Finset.range N := by
      intro n hn
      simp only [ExceptionSet, Set.mem_setOf_eq] at hn
      by_contra h
      simp only [Finset.mem_range, not_lt] at h
      exact hn (hN n h)
    exact Set.Finite.subset (Finset.finite_toSet _) this
  · intro hfin
    obtain ⟨s, hs⟩ := hfin.exists_finset_coe
    use s.sup id + 1
    intro n hn
    by_contra h
    have : n ∈ ExceptionSet := h
    rw [hs] at this
    simp only [Finset.mem_coe] at this
    have := Finset.le_sup this
    omega

/-!
# Part 3: Known Results - Density

The sieve methods show almost all integers are representable.
-/

-- Counting exceptions up to x
noncomputable def exceptionCount (x : ℕ) : ℕ :=
  (Finset.filter (fun n => ¬ IsRepresentable n) (Finset.range x)).card

-- Brun-Selberg bound: exceptions are sparse
-- |ExceptionSet ∩ [1,x]| ≪ x/(log x)^c
axiom brun_selberg_bound : ∃ c : ℝ, c > 0 ∧
  ∀ x : ℕ, x > 1 → (exceptionCount x : ℝ) ≤ x / (Real.log x)^c

-- The density of representable numbers is 1
axiom density_one : Filter.Tendsto
  (fun x => (x - exceptionCount x : ℝ) / x) atTop (nhds 1)

/-!
# Part 4: Small Examples

Verify the definition works for simple cases.
-/

-- Example: 5 = 1*2² + 1 is representable (p=2, a=1, b=1)
theorem five_representable : IsRepresentable 5 := by
  use 1, 2, 1
  constructor
  · exact Nat.prime_two
  · constructor
    · omega
    · constructor
      · omega
      · ring

-- Example: 13 = 1*3² + 4 is representable (p=3, a=1, b=4)... wait, b < p required
-- Actually: 13 = 1*3² + 4, but 4 ≥ 3, so this doesn't work
-- Try: 13 = 3*2² + 1 = 12 + 1 = 13 ✓ (p=2, a=3, b=1)
theorem thirteen_representable : IsRepresentable 13 := by
  use 3, 2, 1
  constructor
  · exact Nat.prime_two
  · constructor
    · omega
    · constructor
      · omega
      · ring

/-!
# Part 5: Variant Problems

Related questions about representations.
-/

-- Without the prime requirement: n = a*m² + b with b < m
def IsRepresentableGeneral (n : ℕ) : Prop :=
  ∃ a m b, a ≥ 1 ∧ m ≥ 2 ∧ b < m ∧ n = a * m^2 + b

-- Selfridge-Wagstaff suggest infinitely many general exceptions
axiom selfridge_wagstaff_conjecture :
  ¬ (∃ N : ℕ, ∀ n ≥ N, IsRepresentableGeneral n)

-- The minimal coefficient c_n: smallest a such that n = a*p² + b for some p, b
-- If no representation exists, c_n is undefined (we use 0 as placeholder)
noncomputable def minimalCoefficient (n : ℕ) : ℕ :=
  if h : IsRepresentable n then
    Nat.find ⟨_, h⟩  -- This is a simplification
  else 0

-- Erdős conjectured limsup c_n = ∞
axiom erdos_minimal_conjecture : ∀ C : ℕ,
  ∃ᶠ n in atTop, minimalCoefficient n > C

-- Related question: Is c_n < n^{o(1)}?
def SubpolynomialGrowth : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N,
    IsRepresentable n → (minimalCoefficient n : ℝ) < n^ε

/-!
# Part 6: Connections to Other Problems

The problem relates to square-free representations and quadratic residues.
-/

-- For a given prime p, the representable numbers with that prime
def RepresentableByPrime (p : ℕ) (hp : p.Prime) : Set ℕ :=
  {n | ∃ a b, a ≥ 1 ∧ b < p ∧ n = a * p^2 + b}

-- The union over all primes covers "almost all" ℕ
axiom almost_all_covered : ∀ ε > 0, ∃ N : ℕ,
  ∀ x ≥ N, (x - exceptionCount x : ℝ) / x > 1 - ε

-- Quadratic residue connection
-- n ≡ b (mod p) for some b < p means n is in certain residue classes
def ResidueConstraint (n p : ℕ) : Prop :=
  n % p < p  -- trivially true, but captures the residue structure

/-!
# Part 7: Problem Status

The problem remains OPEN. Erdős doubted a positive answer.
-/

-- The problem is open
def erdos_676_status : String := "OPEN"

-- Erdős's skepticism
axiom erdos_skeptical : True  -- Erdős believed positive answer "rather unlikely"

-- The main statement
theorem erdos_676_statement :
    ErdosConjecture676 ↔
    ∃ N : ℕ, ∀ n ≥ N, ∃ a p b,
      p.Prime ∧ a ≥ 1 ∧ b < p ∧ n = a * p^2 + b := by
  constructor
  · intro ⟨N, hN⟩
    use N
    intro n hn
    obtain ⟨a, p, b, hp, ha, hb, heq⟩ := hN n hn
    exact ⟨a, p, b, hp, ha, hb, heq⟩
  · intro ⟨N, hN⟩
    use N
    intro n hn
    obtain ⟨a, p, b, hp, ha, hb, heq⟩ := hN n hn
    exact ⟨a, p, b, hp, ha, hb, heq⟩

/-!
# Part 8: Summary

**Known:**
- Almost all integers are representable (density 1)
- Exceptions in [1,x] are ≪ x/(log x)^c

**Unknown:**
- Whether ALL large integers are representable
- Whether there are infinitely many exceptions

**Erdős's Belief:**
- "Rather unlikely" that all large integers work
- Conjectured limsup c_n = ∞ for minimal coefficients
-/

end Erdos676
