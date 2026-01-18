/-
  Erdős Problem #940: Sums of r-Powerful Numbers

  Source: https://erdosproblems.com/940
  Status: OPEN (main conjecture), partial results SOLVED
  Prize: None listed

  Statement:
  Let r ≥ 3. A number n is r-powerful if for every prime p dividing n, p^r | n.
  Does the set of integers which are the sum of at most r r-powerful numbers
  have density 0?

  Background:
  - Erdős (1976) claimed the density-0 result was "easy" for r = 2
  - Baker-Brüdern (1994) proved the r = 2 case rigorously
  - Heath-Brown (1988) proved all large numbers are sums of ≤ 3 squarefull numbers
  - For r = 3, even the special case of sums of ≤ 3 cubes is open
  - Recorded in 1986 Oberwolfach problem book as a problem of Erdős and Ivić

  References:
  [BaBr94] Baker-Brüdern, "On sums of two squarefull numbers" (1994)
  [Er76d] Erdős, "Problems on consecutive integers" (1976)
  [He88] Heath-Brown, "Ternary quadratic forms and sums of three square-full numbers" (1988)

  Tags: number-theory, powerful-numbers, density, additive-combinatorics
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Squarefree
import Mathlib.Data.Multiset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Erdos940

open Filter Finset

/-! ## Part I: r-Powerful Numbers -/

/-- A number n is r-powerful (or r-full) if every prime p dividing n
    satisfies p^r | n. For r = 2, these are "squarefull" numbers.
    For r = 3, these are "cubefull" numbers.

    Examples:
    - 1 is r-powerful for all r (vacuously)
    - 4 = 2² is 2-powerful but not 3-powerful
    - 8 = 2³ is 3-powerful
    - 72 = 2³ · 3² is 2-powerful but not 3-powerful
-/
def isPowerful (r n : ℕ) : Prop :=
  n ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ r ∣ n

/-- 1 is r-powerful for all r ≥ 1 (vacuously). -/
theorem one_isPowerful (r : ℕ) (hr : r ≥ 1) : isPowerful r 1 := by
  constructor
  · omega
  · intro p _ hp
    interval_cases p <;> simp_all

/-- 0 is not r-powerful (by convention). -/
theorem zero_not_isPowerful (r : ℕ) : ¬isPowerful r 0 := by
  intro h
  exact h.1 rfl

/-- Perfect r-th powers are r-powerful.
    For example, n³ is always 3-powerful. -/
theorem power_isPowerful (r n : ℕ) (hr : r ≥ 1) (hn : n ≥ 1) :
    isPowerful r (n ^ r) := by
  constructor
  · positivity
  · intro p hp hdiv
    have : p ∣ n := by
      have := hp.dvd_of_dvd_pow hdiv
      exact this
    exact Nat.pow_dvd_pow_of_dvd this r

/-! ## Part II: The Set of Sums -/

/-- The set of natural numbers that can be expressed as the sum of
    at most k r-powerful numbers. -/
def SumsOfPowerful (r k : ℕ) : Set ℕ :=
  {n : ℕ | ∃ (S : Multiset ℕ), S.card ≤ k ∧ (∀ s ∈ S, isPowerful r s) ∧ n = S.sum}

/-- The set of sums of at most r r-powerful numbers (the "diagonal" case). -/
def DiagonalSums (r : ℕ) : Set ℕ := SumsOfPowerful r r

/-- 0 is always in SumsOfPowerful (empty sum). -/
theorem zero_mem_SumsOfPowerful (r k : ℕ) : 0 ∈ SumsOfPowerful r k := by
  use ∅
  simp [SumsOfPowerful]

/-- 1 is always in SumsOfPowerful for k ≥ 1 (sum of just 1). -/
theorem one_mem_SumsOfPowerful (r k : ℕ) (hr : r ≥ 1) (hk : k ≥ 1) :
    1 ∈ SumsOfPowerful r k := by
  use {1}
  constructor
  · simp; omega
  constructor
  · intro s hs
    simp at hs
    rw [hs]
    exact one_isPowerful r hr
  · simp

/-! ## Part III: Natural Density -/

/-- The counting function for a set A up to N. -/
noncomputable def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  (Finset.range (N + 1)).filter (· ∈ A) |>.card

/-- A set A has natural density d if |A ∩ [1,N]| / N → d as N → ∞. -/
def HasDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N => (countingFunction A N : ℝ) / N) atTop (nhds d)

/-- A set has density 0 if |A ∩ [1,N]| = o(N). -/
def HasDensityZero (A : Set ℕ) : Prop := HasDensity A 0

/-! ## Part IV: The Main Conjecture (OPEN) -/

/-- **Erdős Conjecture #940 (Main Question)**

    For all r ≥ 3, the set of integers expressible as sums of at most r
    r-powerful numbers has density 0.

    Status: OPEN

    This is the diagonal case: we use r summands for r-powerful numbers.
-/
def erdos_940_conjecture : Prop :=
  ∀ r : ℕ, r ≥ 3 → HasDensityZero (DiagonalSums r)

/-- Alternative formulation: infinitely many integers are NOT representable. -/
def erdos_940_infinitely_many : Prop :=
  ∀ r : ℕ, r ≥ 3 → (DiagonalSums r)ᶜ.Infinite

/-- The conjecture implies infinitely many non-representable integers. -/
theorem conjecture_implies_infinite (h : erdos_940_conjecture) :
    erdos_940_infinitely_many := by
  intro r hr
  -- If density is 0, the complement must be infinite
  sorry

/-! ## Part V: The Squarefull Case (r = 2) -/

/-- **Baker-Brüdern Theorem (1994)**

    The set of integers expressible as sums of at most two squarefull
    numbers has density 0.

    Reference: Baker-Brüdern, "On sums of two squarefull numbers", Math. Proc.
    Cambridge Philos. Soc. (1994), 1-5.
-/
axiom baker_brudern_theorem : HasDensityZero (SumsOfPowerful 2 2)

/-- Erdős noted this case was "easy" in 1976.
    Tao gave a potential elementary argument in online comments. -/
theorem squarefull_case : HasDensityZero (SumsOfPowerful 2 2) :=
  baker_brudern_theorem

/-! ## Part VI: Heath-Brown's Representation Theorem -/

/-- **Heath-Brown's Theorem (1988)**

    All sufficiently large integers are expressible as the sum of at most
    three squarefull (2-powerful) numbers.

    This is a representation theorem, not a density theorem.
    It says eventually ALL integers are representable with 3 squarefull summands.

    Reference: Heath-Brown, "Ternary quadratic forms and sums of three
    square-full numbers" (1988), 137-163.
-/
axiom heath_brown_theorem :
    ∀ᶠ n in atTop, n ∈ SumsOfPowerful 2 3

/-- Reformulation: The complement of SumsOfPowerful 2 3 is finite. -/
theorem heath_brown_complement_finite :
    (SumsOfPowerful 2 3)ᶜ.Finite := by
  sorry

/-! ## Part VII: The Cubefull Case and Three Cubes -/

/-- **Open Problem: Sums of Three Cubes**

    Is it true that the set of integers expressible as sums of at most
    three cubes (perfect cubes, not just 3-powerful numbers) has density 0?

    This is OPEN and would be a step toward the r = 3 case of Problem #940.
-/
def three_cubes_conjecture : Prop :=
  HasDensityZero {n : ℕ | ∃ a b c : ℕ, n = a^3 + b^3 + c^3}

/-- Cubes are a subset of 3-powerful numbers.
    So the density-0 conjecture for cubes is weaker than for 3-powerful. -/
theorem cubes_subset_cubefull :
    {n : ℕ | ∃ m : ℕ, m ≥ 1 ∧ n = m^3} ⊆ {n : ℕ | isPowerful 3 n} := by
  intro n ⟨m, hm, hn⟩
  rw [hn]
  exact power_isPowerful 3 m (by omega) hm

/-- The r = 3 case (cubefull) of the main conjecture. -/
def cubefull_conjecture : Prop := HasDensityZero (DiagonalSums 3)

/-! ## Part VIII: The Large Integer Representation Question -/

/-- **Open Problem: Universal Representation**

    For all r ≥ 2, are all sufficiently large integers expressible as
    the sum of at most r r-powerful numbers?

    Status: OPEN for r ≥ 3

    Heath-Brown proved r = 2 (with 3 summands), but the diagonal case
    (exactly r summands for r-powerful) is unknown even for r = 2.
-/
def universal_representation_conjecture : Prop :=
  ∀ r : ℕ, r ≥ 2 → ∀ᶠ n in atTop, n ∈ DiagonalSums r

/-- The r = 2 diagonal case: every large n is a sum of ≤ 2 squarefull numbers.
    This is OPEN (Heath-Brown proved it for 3 summands). -/
def squarefull_diagonal_conjecture : Prop :=
  ∀ᶠ n in atTop, n ∈ DiagonalSums 2

/-! ## Part IX: Relationship Between the Questions -/

/-- Summary of the problem structure:

    The main question has two parts:
    1. Does DiagonalSums r have density 0 for r ≥ 3?
    2. Are infinitely many integers NOT in DiagonalSums r?

    Known results:
    - Baker-Brüdern: SumsOfPowerful 2 2 has density 0
    - Heath-Brown: Eventually all n ∈ SumsOfPowerful 2 3

    Open cases:
    - r = 3 with three summands (even for cubes)
    - r ≥ 3 in general
    - Whether universal representation holds for diagonal cases
-/
theorem status_summary :
    -- Baker-Brüdern: squarefull pairs have density 0
    HasDensityZero (SumsOfPowerful 2 2) ∧
    -- Heath-Brown: squarefull triples eventually cover everything
    (∀ᶠ n in atTop, n ∈ SumsOfPowerful 2 3) := by
  exact ⟨baker_brudern_theorem, heath_brown_theorem⟩

/-! ## Part X: Examples and Computations -/

/-- 4 = 2² is squarefull. -/
example : isPowerful 2 4 := by
  constructor
  · omega
  · intro p hp hdiv
    interval_cases p
    all_goals simp_all [Nat.Prime] <;> omega

/-- 8 = 2³ is cubefull. -/
example : isPowerful 3 8 := by
  constructor
  · omega
  · intro p hp hdiv
    interval_cases p
    all_goals simp_all [Nat.Prime] <;> omega

/-- 72 = 2³ · 3² is squarefull but not cubefull. -/
example : isPowerful 2 72 := by
  constructor
  · omega
  · intro p hp hdiv
    -- 72 = 8 · 9 = 2³ · 3²
    -- Prime divisors are 2 and 3
    have h72 : 72 = 2^3 * 3^2 := by norm_num
    interval_cases p
    all_goals
      simp_all [Nat.Prime]
      · norm_num
        omega
      <;> omega

/-! ## Part XI: Related Problems -/

/-- Problem #941 is about Heath-Brown's result specifically. -/
def problem_941_related : Prop :=
  ∀ᶠ n in atTop, n ∈ SumsOfPowerful 2 3

/-- Problem #1081 asks refined questions about the r = 2 case. -/
def problem_1081_related : Prop :=
  HasDensityZero (SumsOfPowerful 2 2)

/-- Problem #1107 concerns r + 1 summands instead of r summands. -/
def problem_1107_related (r : ℕ) : Prop :=
  HasDensityZero (SumsOfPowerful r (r + 1))

end Erdos940

/-!
## Summary

This file formalizes Erdős Problem #940 on sums of r-powerful numbers.

**Status**: OPEN (main conjecture), partial results SOLVED

**The Problem**: For r ≥ 3, does the set of integers expressible as sums
of at most r r-powerful numbers have density 0?

**What is an r-powerful number?**
A number n is r-powerful (or r-full) if every prime p | n satisfies p^r | n.
- r = 2: squarefull numbers (4, 8, 9, 16, 25, 27, 32, 36, ...)
- r = 3: cubefull numbers (1, 8, 27, 64, ...)

**Known Results**:
- Baker-Brüdern (1994): Sums of ≤ 2 squarefull numbers have density 0
- Heath-Brown (1988): All large n are sums of ≤ 3 squarefull numbers

**Open Cases**:
- r = 3 (even the special case of ≤ 3 cubes is open)
- r ≥ 4 (completely open)
- Whether all large integers are in DiagonalSums r for any r ≥ 2

**Historical Note**:
Erdős initially claimed a "simple counting argument" showed infinitely many
integers are not representable, but Schinzel found an error in this proof.

**What we formalize**:
1. r-powerful numbers (isPowerful predicate)
2. Set of sums of at most k r-powerful numbers (SumsOfPowerful)
3. Natural density definition
4. Main conjecture for r ≥ 3 (OPEN)
5. Baker-Brüdern theorem for r = 2 (axiom)
6. Heath-Brown's representation theorem (axiom)
7. Open variants: three cubes, universal representation
8. Connection to Problems #941, #1081, #1107

**Key axioms**:
- `baker_brudern_theorem`: Squarefull pairs have density 0
- `heath_brown_theorem`: Large integers are sums of ≤ 3 squarefull numbers
-/
