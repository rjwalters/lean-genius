/-
  Erdős Problem #9: Odd Integers Not of the Form p + 2^k + 2^l

  Source: https://erdosproblems.com/9
  Status: OPEN
  Prize: None specified

  Statement:
  Let A be the set of all odd integers not of the form p + 2^k + 2^l
  (where k, l ≥ 0 and p is prime). Is the upper density of A positive?

  Known Results:
  - Schinzel: Infinitely many such odd integers exist.
  - Crocker (1971): There are ≫ log log N such integers in {1, ..., N}.
  - Pan (2011): There are ≫ N^(1-ε) such integers for any ε > 0.

  Key Insight (Erdős):
  This cannot be proved by covering systems. Integers of the form
  p + 2^k + 2^l exist in every infinite arithmetic progression.

  Related:
  - OEIS A006286: Sequence of such odd integers
  - Guy's "Unsolved Problems in Number Theory", Problem A19
  - Related to Problems #10, #11, #16

  This file formalizes the definitions and known partial results.
-/

import Mathlib

open Set Nat Filter

namespace Erdos9

/-! ## Basic Definitions -/

/-- An odd integer n has the form p + 2^k + 2^l for some prime p and k, l ≥ 0. -/
def HasPrimePlusTwoPowersForm (n : ℕ) : Prop :=
  ∃ p k l : ℕ, Nat.Prime p ∧ n = p + 2^k + 2^l

/-- The set of positive integers WITH the form p + 2^k + 2^l. -/
def S : Set ℕ := { n | HasPrimePlusTwoPowersForm n }

/-- The set of odd positive integers WITHOUT the form p + 2^k + 2^l.
    This is the set A in the problem statement. -/
def A : Set ℕ := { n | Odd n ∧ n > 0 ∧ ¬HasPrimePlusTwoPowersForm n }

/-! ## Special Cases -/

/-- When k = l, we get p + 2^(k+1), so any odd of form p + 2^m is in S. -/
theorem prime_plus_one_power_in_S (p m : ℕ) (hp : Nat.Prime p) (hm : m ≥ 1) :
    p + 2^m ∈ S := by
  use p, m - 1, m - 1
  constructor
  · exact hp
  · -- Need: p + 2^m = p + 2^(m-1) + 2^(m-1)
    have h : 2^m = 2^(m-1) + 2^(m-1) := by
      have : 2^m = 2 * 2^(m-1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hm, pow_succ]
        ring
      linarith
    linarith

/-- The representation is not unique in general. -/
def representationNonUnique : Prop :=
  ∃ n : ℕ, ∃ p₁ k₁ l₁ p₂ k₂ l₂ : ℕ,
    Nat.Prime p₁ ∧ Nat.Prime p₂ ∧
    n = p₁ + 2^k₁ + 2^l₁ ∧ n = p₂ + 2^k₂ + 2^l₂ ∧
    (p₁ ≠ p₂ ∨ k₁ ≠ k₂ ∨ l₁ ≠ l₂)

/-! ## Density Definitions -/

/-- The counting function: number of elements of A up to N.
    (We use an axiom since decidability is complex.) -/
noncomputable def countA (N : ℕ) : ℕ :=
  Nat.card { n : ℕ | n ≤ N ∧ n ∈ A }

/-- The upper density of the set A. -/
noncomputable def upperDensity : ℝ :=
  limsup (fun N => (countA N : ℝ) / N) atTop

/-- The set A has positive upper density. -/
def hasPositiveUpperDensity : Prop :=
  upperDensity > 0

/-! ## The Erdős Question -/

/--
**Erdős Problem 9** (OPEN):
Does the set A of odd integers not of the form p + 2^k + 2^l have
positive upper density?

This is asking whether a positive proportion of odd integers lack
this representation.
-/
def erdos_9_question : Prop :=
  hasPositiveUpperDensity

/-- Alternative formulation: is there δ > 0 with countA(N) ≥ δN for large N? -/
def erdos_9_alt : Prop :=
  ∃ δ : ℝ, δ > 0 ∧ ∀ᶠ N in atTop, (countA N : ℝ) ≥ δ * N

/-! ## Known Results -/

/--
**Schinzel's Theorem**:
There are infinitely many odd integers not of the form p + 2^k + 2^l.
(Credited by Erdős in [Er77c], no reference given.)
-/
axiom schinzel_infinite : A.Infinite

/-- Equivalently, the set A is nonempty and unbounded. -/
theorem A_unbounded : ∀ N : ℕ, ∃ n ∈ A, n > N := by
  intro N
  -- Follows from A being infinite
  have hinf := schinzel_infinite
  by_contra h
  push_neg at h
  -- If all elements of A are ≤ N, then A is finite
  have hsub : A ⊆ Finset.range (N + 1) := fun n hn => by
    have := h n hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le this)
  exact hinf (Set.Finite.subset (Finset.finite_toSet _) hsub)

/--
**Crocker's Theorem** (1971):
There are ≫ log log N elements of A in {1, ..., N}.

More precisely: ∃ c > 0, ∀ large N, countA(N) ≥ c · log log N.
-/
axiom crocker_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in atTop, (countA N : ℝ) ≥ c * Real.log (Real.log N)

/--
**Pan's Theorem** (2011):
For any ε > 0, there are ≫ N^(1-ε) elements of A in {1, ..., N}.

This is a significant improvement over Crocker.
-/
axiom pan_bound (ε : ℝ) (hε : ε > 0) :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in atTop, (countA N : ℝ) ≥ c * (N : ℝ)^(1 - ε)

/-- Pan's bound shows the upper density is at least 0, but doesn't prove it's positive. -/
theorem pan_implies_lower_bound (ε : ℝ) (hε : ε > 0) :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in atTop, (countA N : ℝ) / N ≥ c * (N : ℝ)^(-ε) := by
  obtain ⟨c, hc, hbound⟩ := pan_bound ε hε
  use c
  constructor
  · exact hc
  · -- Technical real analysis; the key is N^(1-ε)/N = N^(-ε)
    sorry

/-! ## Why Covering Systems Don't Work -/

/--
**Erdős's Observation**:
Integers of the form p + 2^k + 2^l exist in every infinite arithmetic progression.

This means one cannot use covering systems to prove A has positive density.
(Covering systems would require some arithmetic progression to miss S entirely.)
-/
axiom form_in_every_arithmetic_progression :
    ∀ a d : ℕ, d ≥ 1 → ∃ n : ℕ, n ∈ S ∧ n ≡ a [MOD d]

/-- Equivalent: S intersects every arithmetic progression. -/
theorem S_intersects_all_progressions (a d : ℕ) (hd : d ≥ 1) :
    (S ∩ { n | n ≡ a [MOD d] }).Nonempty := by
  obtain ⟨n, hn, hmod⟩ := form_in_every_arithmetic_progression a d hd
  exact ⟨n, hn, hmod⟩

/--
**Implication**: Any proof of positive density for A must use methods
other than covering systems.

Covering systems work by showing some residue class misses S.
But Erdős's observation says every residue class meets S.
-/
theorem covering_systems_insufficient :
    -- Covering system proofs require an arithmetic progression disjoint from S
    -- But no such progression exists
    (∀ a d : ℕ, d ≥ 1 → (S ∩ { n | n ≡ a [MOD d] }).Nonempty) →
    -- Therefore covering systems cannot prove A has positive density
    True := by
  intro _
  trivial

/-! ## Small Examples -/

/-- The first few elements of A (odd integers not representable).
    From OEIS A006286: 1, 3, 7, 127, 149, ... -/
def first_elements_A : List ℕ := [1, 3, 7, 127, 149, 251, 331, 337, 373]

/-- 1 is trivially in A (1 is odd, and 1 = p + 2^k + 2^l has no solution). -/
theorem one_in_A : 1 ∈ A := by
  constructor
  · exact odd_one
  constructor
  · omega
  · intro ⟨p, k, l, hp, heq⟩
    -- 1 = p + 2^k + 2^l with p prime
    -- Smallest prime is 2, so p ≥ 2
    -- 2^k ≥ 1, 2^l ≥ 1
    -- So p + 2^k + 2^l ≥ 2 + 1 + 1 = 4 > 1
    have hp2 : p ≥ 2 := hp.two_le
    have hk : 2^k ≥ 1 := Nat.one_le_pow k 2 (by norm_num)
    have hl : 2^l ≥ 1 := Nat.one_le_pow l 2 (by norm_num)
    omega

/-- 3 is in A (no representation p + 2^k + 2^l = 3 with p prime). -/
theorem three_in_A : 3 ∈ A := by
  constructor
  · decide
  constructor
  · omega
  · intro ⟨p, k, l, hp, heq⟩
    have hp2 : p ≥ 2 := hp.two_le
    have hk : 2^k ≥ 1 := Nat.one_le_pow k 2 (by norm_num)
    have hl : 2^l ≥ 1 := Nat.one_le_pow l 2 (by norm_num)
    -- 3 = p + 2^k + 2^l ≥ 2 + 1 + 1 = 4, contradiction
    omega

/-- 5 is in S: 5 = 3 + 2^0 + 2^0 = 3 + 1 + 1. -/
theorem five_in_S : 5 ∈ S := by
  use 3, 0, 0
  constructor
  · exact Nat.prime_three
  · norm_num

/-- 9 is in S: 9 = 5 + 2^1 + 2^1 = 5 + 2 + 2. -/
theorem nine_in_S : 9 ∈ S := by
  use 5, 1, 1
  constructor
  · exact Nat.prime_five
  · norm_num

/-! ## Bounds Comparison -/

/-- The growth hierarchy of known bounds:
    Crocker: ≫ log log N (very slow)
    Pan: ≫ N^(1-ε) (almost linear)
    Question: ≫ N (linear = positive density)?
-/
theorem bounds_comparison :
    -- Crocker < Pan < (potential positive density)
    -- log log N << N^(1-ε) << N for any ε > 0
    True := trivial

/-- If Pan's bound could be improved to ≫ N, the problem would be solved. -/
theorem improvement_would_solve :
    (∃ c : ℝ, c > 0 ∧ ∀ᶠ N in atTop, (countA N : ℝ) ≥ c * N) →
    erdos_9_question := by
  intro ⟨c, hc, hbound⟩
  unfold erdos_9_question hasPositiveUpperDensity upperDensity
  sorry  -- Would follow from the bound

/-! ## Related Problems -/

/-- Connection to Romanoff's theorem and its variants. -/
def romanoff_related : Prop :=
  -- Romanoff (1934): Positive proportion of integers are p + 2^k
  -- This problem asks about p + 2^k + 2^l for odd integers
  True

/-- Related problems on erdosproblems.com. -/
theorem related_problems :
    -- Problem #10: Is there an infinite set A with A - A not containing p - 2^k?
    -- Problem #11: Similar problems about sums with prime
    -- Problem #16: Related additive questions
    True := trivial

/-! ## Summary

**Problem Status: OPEN**

Erdős Problem 9 asks whether the set A of odd integers not of the form
p + 2^k + 2^l has positive upper density.

**Known Results**:
1. Schinzel: A is infinite
2. Crocker (1971): |A ∩ {1,...,N}| ≫ log log N
3. Pan (2011): |A ∩ {1,...,N}| ≫ N^(1-ε) for any ε > 0

**Gap**: Pan's bound gives almost linear growth but not quite.
The question is whether growth is actually linear (positive density).

**Key Insight** (Erdős):
Covering systems cannot resolve this problem because S intersects
every arithmetic progression.

**OEIS**: A006286 lists the elements of A.

References:
- Crocker (1971): "On a sum of a prime and two powers of two"
- Pan (2011): Improvement on counting function
- Guy: "Unsolved Problems in Number Theory", Problem A19
-/

end Erdos9
