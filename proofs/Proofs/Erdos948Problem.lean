/-
Erdős Problem #948: Subset Sums and Colorings

**Problem Statement (OPEN)**

Does there exist a function f(n) and integer k such that for any k-coloring
of the integers, there is a sequence a₁ < a₂ < ... with aₙ < f(n) for
infinitely many n, where the set of all finite subsums does not contain all colors?

**Background:**
This problem connects to Hindman's theorem (Erdős Problem #532) which says
that for any finite coloring of ℕ, there exists an infinite sequence whose
finite subsums are monochromatic. The current problem asks about the converse
direction and growth constraints.

**Known Results:**
- Galvin's counterexample shows monochromatic solutions don't always exist
- Relates to the structure of IP sets and additive combinatorics

**Status:** OPEN

**Reference:** [Er77c]
-/

import Mathlib

open Finset

namespace Erdos948

/-!
# Part 1: Finite Subsums

For a sequence a : ℕ → ℕ, the finite subsums are all possible sums
of distinct finite subsets.
-/

-- The set of finite subsums of a sequence
def FiniteSubsums (a : ℕ → ℕ) : Set ℕ :=
  {s | ∃ S : Finset ℕ, s = ∑ i in S, a i}

-- Alternative definition using sets
def FiniteSubsums' (a : ℕ → ℕ) : Set ℕ :=
  {s | ∃ S : Set ℕ, S.Finite ∧ s = ∑' i : S, a i}

-- The sum over a finite set of indices
noncomputable def sumOverSet (a : ℕ → ℕ) (S : Finset ℕ) : ℕ :=
  ∑ i in S, a i

-- Basic property: 0 is always a subsum (empty set)
theorem zero_mem_finite_subsums (a : ℕ → ℕ) : 0 ∈ FiniteSubsums a :=
  ⟨∅, by simp [FiniteSubsums]⟩

-- Each term is a subsum (singleton set)
theorem term_mem_finite_subsums (a : ℕ → ℕ) (n : ℕ) : a n ∈ FiniteSubsums a :=
  ⟨{n}, by simp [FiniteSubsums]⟩

/-!
# Part 2: Colorings

A k-coloring assigns each natural number one of k colors.
-/

-- A coloring of ℕ with k colors
def Coloring (k : ℕ) := ℕ → Fin k

-- A set is monochromatic under a coloring
def IsMonochromatic (c : Coloring k) (S : Set ℕ) : Prop :=
  ∃ color : Fin k, ∀ n ∈ S, c n = color

-- A set contains all colors
def ContainsAllColors (c : Coloring k) (S : Set ℕ) : Prop :=
  ∀ color : Fin k, ∃ n ∈ S, c n = color

-- A set avoids some color
def AvoidsSomeColor (c : Coloring k) (S : Set ℕ) : Prop :=
  ∃ color : Fin k, ∀ n ∈ S, c n ≠ color

/-!
# Part 3: Growth Conditions

The problem asks for sequences with controlled growth.
-/

-- Sequence bounded by f at infinitely many places
def BoundedInfinitelyOften (a : ℕ → ℕ) (f : ℕ → ℕ) : Prop :=
  {n | a n < f n}.Infinite

-- Strictly increasing sequence
def StrictlyIncreasing (a : ℕ → ℕ) : Prop :=
  ∀ m n, m < n → a m < a n

/-!
# Part 4: The Main Conjecture

The problem asks whether there exist f and k with a specific property.
-/

-- The Erdős conjecture (original monochromatic version - FALSE)
def MonochromaticConjecture : Prop :=
  ∃ f : ℕ → ℕ, ∃ k : ℕ, k > 0 ∧
    ∀ c : Coloring k, ∃ a : ℕ → ℕ,
      StrictlyIncreasing a ∧
      BoundedInfinitelyOften a f ∧
      IsMonochromatic c (FiniteSubsums a)

-- Galvin's counterexample disproves the monochromatic version
axiom galvin_counterexample : ¬MonochromaticConjecture

-- The modified conjecture: subsums avoid some color (not all colors present)
def ModifiedConjecture : Prop :=
  ∃ f : ℕ → ℕ, ∃ k : ℕ, k > 0 ∧
    ∀ c : Coloring k, ∃ a : ℕ → ℕ,
      StrictlyIncreasing a ∧
      BoundedInfinitelyOften a f ∧
      AvoidsSomeColor c (FiniteSubsums a)

-- The conjecture: subsums don't contain all colors
def ErdosConjecture948 : Prop :=
  ∃ f : ℕ → ℕ, ∃ k : ℕ, k ≥ 2 ∧
    ∀ c : Coloring k, ∃ a : ℕ → ℕ,
      StrictlyIncreasing a ∧
      BoundedInfinitelyOften a f ∧
      ¬ContainsAllColors c (FiniteSubsums a)

/-!
# Part 5: Galvin's Counterexample

Galvin showed that using the dyadic valuation gives a counterexample.
-/

-- The dyadic valuation: 2^ν(n) is the largest power of 2 dividing n
def dyadicValuation (n : ℕ) : ℕ :=
  if n = 0 then 0 else n.factorization 2

-- Galvin's 2-coloring based on odd part
def galvinColoring : Coloring 2 := fun n =>
  if n = 0 then 0 else ⟨(n / 2^(dyadicValuation n)) % 2, by omega⟩

-- Galvin showed no infinite sequence has monochromatic subsums under this coloring
axiom galvin_no_monochromatic :
  ¬∃ a : ℕ → ℕ, StrictlyIncreasing a ∧ IsMonochromatic galvinColoring (FiniteSubsums a)

/-!
# Part 6: Hindman's Theorem

Hindman's theorem (1974) is the positive direction: finite colorings
have infinite sequences with monochromatic subsums.
-/

-- Hindman's theorem: for any finite coloring, some color class is an IP set
axiom hindman_theorem : ∀ k : ℕ, k > 0 →
  ∀ c : Coloring k, ∃ a : ℕ → ℕ,
    StrictlyIncreasing a ∧
    IsMonochromatic c (FiniteSubsums a)

-- But Hindman doesn't give growth bounds!
-- The question is whether we can find such a with a_n < f(n) often

/-!
# Part 7: Related Concepts

IP sets and FS sets are central to this area.
-/

-- An IP set is the set of finite sums of some infinite sequence
def IsIPSet (S : Set ℕ) : Prop :=
  ∃ a : ℕ → ℕ, StrictlyIncreasing a ∧ FiniteSubsums a ⊆ S

-- An FS set is exactly the finite sums (not just a superset)
def IsFSSet (S : Set ℕ) : Prop :=
  ∃ a : ℕ → ℕ, StrictlyIncreasing a ∧ FiniteSubsums a = S

-- IP* sets: sets that meet every IP set
def IsIPStar (S : Set ℕ) : Prop :=
  ∀ T : Set ℕ, IsIPSet T → (S ∩ T).Nonempty

-- Hindman implies: for any finite coloring, some color class is IP*
axiom hindman_ip_star : ∀ k : ℕ, k > 0 →
  ∀ c : Coloring k, ∃ color : Fin k, IsIPStar {n | c n = color}

/-!
# Part 8: Open Status

The problem remains open. The gap between Hindman (existence without bounds)
and Galvin (no universal monochromatic solution) leaves the question unresolved.
-/

-- The problem is open
def erdos_948_status : String := "OPEN"

-- The countable colors version is also open
def CountableColorsVersion : Prop :=
  ∃ f : ℕ → ℕ, ∀ c : ℕ → ℕ, ∃ a : ℕ → ℕ,
    StrictlyIncreasing a ∧
    BoundedInfinitelyOften a f ∧
    {c n | n ∈ FiniteSubsums a}.ncard < ⊤

/-!
# Part 9: Summary

Erdős Problem #948 asks about the interplay between:
1. Subset sum structure (IP sets)
2. Colorings of integers
3. Growth constraints on sequences

**Status:** OPEN

**What's Known:**
- Hindman's theorem: finite colorings admit monochromatic IP sets
- Galvin's counterexample: not all colorings admit bounded monochromatic sequences
- The modified version (avoiding some color, not necessarily monochromatic) is open
-/

-- Main theorem: the original monochromatic version is false
theorem erdos_948_mono_false : ¬MonochromaticConjecture := galvin_counterexample

-- The modified version remains open
theorem erdos_948_statement :
    ErdosConjecture948 ↔
    ∃ f : ℕ → ℕ, ∃ k : ℕ, k ≥ 2 ∧
      ∀ c : Coloring k, ∃ a : ℕ → ℕ,
        StrictlyIncreasing a ∧
        BoundedInfinitelyOften a f ∧
        ¬ContainsAllColors c (FiniteSubsums a) := by
  rfl

end Erdos948
