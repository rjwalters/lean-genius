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

Axioms: 4 (brun_selberg_bound, density_one, selfridge_wagstaff_conjecture, erdos_minimal_conjecture)
Proved: 10 theorems
Sorries: 0
-/

import Mathlib

open Nat Filter Set

namespace Erdos676

/-
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

/-
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

/-
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

/-
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

/-
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

/-
# Part 6: Connections to Other Problems

The problem relates to square-free representations and quadratic residues.
-/

-- For a given prime p, the representable numbers with that prime
def RepresentableByPrime (p : ℕ) (hp : p.Prime) : Set ℕ :=
  {n | ∃ a b, a ≥ 1 ∧ b < p ∧ n = a * p^2 + b}

-- The union over all primes covers "almost all" ℕ.
-- Follows from density_one: if (x - E(x))/x → 1, then eventually > 1 - ε.
theorem almost_all_covered : ∀ ε > 0, ∃ N : ℕ,
    ∀ x ≥ N, (x - exceptionCount x : ℝ) / x > 1 - ε := by
  intro ε hε
  have hev := density_one.eventually (Metric.ball_mem_nhds 1 hε)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  exact ⟨N, fun x hx => by
    have := hN x hx
    simp only [Metric.mem_ball, Real.dist_eq] at this
    linarith [abs_lt.mp this |>.1]⟩

-- Quadratic residue connection
-- n ≡ b (mod p) for some b < p means n is in certain residue classes
def ResidueConstraint (n p : ℕ) : Prop :=
  n % p < p  -- trivially true, but captures the residue structure

/-
# Part 7: Problem Status

The problem remains OPEN. Erdős doubted a positive answer.
-/

-- The problem is open
def erdos_676_status : String := "OPEN"

-- Erdős's skepticism

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

/-
# Part 8: Structural Properties
-/

/-- Numbers less than 4 are not representable: the smallest representation
    is 1·2²+0 = 4, since a ≥ 1, p ≥ 2 (prime), and b ≥ 0. -/
theorem not_representable_of_lt_four (n : ℕ) (hn : n < 4) : ¬IsRepresentable n := by
  intro ⟨a, p, b, hp, ha, hb, heq⟩
  have hp2 : p ≥ 2 := hp.two_le
  have h1 : p ^ 2 ≥ 4 := by nlinarith
  have h2 : a * p ^ 2 ≥ 4 := by nlinarith
  omega

/-- 4 is the smallest representable number: 4 = 1·2²+0. -/
theorem four_representable : IsRepresentable 4 := by
  exact ⟨1, 2, 0, Nat.prime_two, by omega, by omega, by ring⟩

/-- The exception count is at most x (trivial upper bound). -/
theorem exceptionCount_le (x : ℕ) : exceptionCount x ≤ x :=
  (Finset.card_filter_le _ _).trans (Finset.card_range x).le

/-- The exception count is monotone non-decreasing. -/
theorem exceptionCount_mono {x y : ℕ} (hxy : x ≤ y) :
    exceptionCount x ≤ exceptionCount y :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hxy))

/-- Every multiple of p² plus a remainder b < p is representable (with a ≥ 1). -/
theorem representable_of_decomposition (n a : ℕ) (p : ℕ) (b : ℕ)
    (hp : p.Prime) (ha : a ≥ 1) (hb : b < p) (heq : n = a * p^2 + b) :
    IsRepresentable n :=
  ⟨a, p, b, hp, ha, hb, heq⟩

/-
# Part 9: Summary

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
