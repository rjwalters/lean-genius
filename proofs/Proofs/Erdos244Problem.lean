/-
  Erdős Problem #244: Prime Plus Powers of C (Density Problem)

  Source: https://erdosproblems.com/244
  Status: OPEN (general case) / SOLVED (integer case, Romanoff 1934)

  Statement:
  Let C > 1. Does the set of integers of the form p + ⌊C^k⌋, for some prime p
  and k ≥ 0, have positive lower density?

  History:
  - Originally asked to Erdős by Kalmár
  - Erdős believed the answer is yes for all C > 1
  - Romanoff (1934) proved the answer is yes when C is a positive integer
  - Ding (2025) proved this holds for almost all C > 1

  This problem is a generalization of Erdős Problem #10 (prime plus powers of 2).
  When C = 2, we ask about p + 2^k, which is Romanoff's original 1934 result.

  Key Insight:
  The integer case (C ∈ ℕ) is easier because the sequence ⌊C^k⌋ = C^k is exact,
  avoiding floor function complications. For non-integer C, the floor creates
  irregularity that makes density arguments more delicate.

  What We Formalize:
  1. The definition of representability as p + ⌊C^k⌋
  2. Lower density concepts
  3. Romanoff's result for integer C (axiom - proved in 1934)
  4. The general conjecture as an open problem

  Tags: number-theory, primes, density, additive-combinatorics, erdos-problem
-/

import Mathlib

namespace Erdos244

/-! ## Part I: Basic Definitions -/

/-- A natural number n is representable as p + ⌊C^k⌋ for a prime p and some k ≥ 0.
    This is the set we want to show has positive density. -/
def IsRepresentable (C : ℝ) (n : ℕ) : Prop :=
  ∃ (p k : ℕ), p.Prime ∧ n = p + ⌊C ^ k⌋₊

/-- The set of representable integers for a given C > 1. -/
def RepresentableSet (C : ℝ) : Set ℕ :=
  {n | IsRepresentable C n}

/-- For integer C, the floor simplifies: ⌊C^k⌋ = C^k exactly. -/
theorem floor_pow_nat {C : ℕ} (hC : C > 0) (k : ℕ) : ⌊(C : ℝ) ^ k⌋₊ = C ^ k := by
  have h : (C : ℝ) ^ k = (C ^ k : ℕ) := by simp
  rw [h]
  exact Nat.floor_natCast (C ^ k)

/-- For integer C ≥ 2, representability becomes p + C^k. -/
def IsRepresentableNat (C : ℕ) (n : ℕ) : Prop :=
  ∃ (p k : ℕ), p.Prime ∧ n = p + C ^ k

/-- The natural definition matches the real definition for integer C. -/
theorem representable_nat_iff_real {C : ℕ} (hC : C > 0) (n : ℕ) :
    IsRepresentableNat C n ↔ IsRepresentable (C : ℝ) n := by
  unfold IsRepresentableNat IsRepresentable
  constructor
  · intro ⟨p, k, hp, hn⟩
    use p, k, hp
    rw [hn, floor_pow_nat hC]
  · intro ⟨p, k, hp, hn⟩
    use p, k, hp
    rw [floor_pow_nat hC] at hn
    exact hn

/-! ## Part II: Density Concepts

Lower density captures what fraction of integers (asymptotically) belong to a set.
For a set S ⊆ ℕ, the lower density is:
  lim inf_{N→∞} |S ∩ [1,N]| / N
-/

/-- Counting function: number of elements of S up to N.
    Requires decidability of membership to be computable. -/
noncomputable def countingFunction (S : Set ℕ) (N : ℕ) : ℕ :=
  Nat.card {n : ℕ | n ≤ N ∧ n ∈ S}

/-- Lower density of a set of natural numbers.
    This is defined as the limit inferior of the proportion of S up to N. -/
noncomputable def lowerDensity (S : Set ℕ) : ℝ :=
  Filter.liminf (fun N => (countingFunction S N : ℝ) / N) Filter.atTop

/-- Upper density of a set. -/
noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  Filter.limsup (fun N => (countingFunction S N : ℝ) / N) Filter.atTop

/-- A set has positive density if its lower density is positive. -/
def HasPositiveDensity (S : Set ℕ) : Prop :=
  0 < lowerDensity S

/-! ## Part III: Romanoff's Theorem (1934)

Romanoff proved that for any integer C ≥ 2, the set of integers representable
as p + C^k (prime p, k ≥ 0) has positive lower density.

This was a landmark result in additive number theory, showing that primes and
geometric progressions interact in a density-positive way.

The proof uses sieve methods and careful counting arguments.
-/

/-- **Romanoff's Theorem (1934)**

    For any integer C ≥ 2, the set of integers of the form p + C^k
    (where p is prime and k ≥ 0) has positive lower density.

    Reference: Romanoff, N. P., "Über einige Sätze der additiven Zahlentheorie."
    Math. Ann. 109 (1934), 668-678.

    This is stated as an axiom because the proof requires analytic number theory
    techniques (sieve methods, prime number theorem applications) that go beyond
    basic Mathlib. -/
axiom romanoff_theorem (C : ℕ) (hC : 2 ≤ C) :
    HasPositiveDensity (RepresentableSet (C : ℝ))

/-- Corollary: The specific case C = 2 (Erdős Problem #10 related).
    The set of p + 2^k has positive density. -/
theorem romanoff_base_2 : HasPositiveDensity (RepresentableSet 2) :=
  romanoff_theorem 2 (by norm_num)

/-- The set {p + 2^k | p prime, k ≥ 0} is nonempty (obvious but useful). -/
theorem representable_set_nonempty (C : ℝ) (hC : C > 1) :
    (RepresentableSet C).Nonempty := by
  use 3  -- 3 = 2 + ⌊C^0⌋ = 2 + 1
  unfold RepresentableSet IsRepresentable
  use 2, 0
  constructor
  · exact Nat.prime_two
  · simp only [pow_zero]
    have h1 : (1 : ℝ) ≤ 1 := le_refl 1
    have hfloor : ⌊(1 : ℝ)⌋₊ = 1 := by norm_num
    rw [hfloor]

/-! ## Part IV: The General Conjecture (Open Problem)

The full conjecture asks: for ANY real C > 1 (not just integers),
does the set {p + ⌊C^k⌋ | p prime, k ≥ 0} have positive density?

Erdős believed yes. Recent work by Ding (2025) shows this holds for
"almost all" C > 1 (in the sense of Lebesgue measure).
-/

/-- **Erdős Problem #244** (General Form)

    For any real C > 1, does the set of integers of the form p + ⌊C^k⌋
    have positive lower density?

    Status: OPEN
    Erdős's prediction: YES

    This is the main open conjecture. -/
def erdos_244_conjecture : Prop :=
  ∀ C : ℝ, C > 1 → HasPositiveDensity (RepresentableSet C)

/-- **Ding's Theorem (2025)**

    The conjecture holds for almost all C > 1 (with respect to Lebesgue measure).

    Reference: Ding, Y., "On a Romanoff type problem of Erdős and Kalmár."
    arXiv:2503.22700 (2025).

    This represents significant progress but doesn't resolve the conjecture
    for specific troublesome values of C. -/
axiom ding_almost_all :
    ∃ (N : Set ℝ), MeasureTheory.volume N = 0 ∧
    ∀ C : ℝ, C > 1 → C ∉ N → HasPositiveDensity (RepresentableSet C)

/-! ## Part V: Small Examples -/

/-- 3 = 2 + 2^0 is representable for any C ≥ 1. -/
theorem three_representable (C : ℝ) (hC : C ≥ 1) : IsRepresentable C 3 := by
  use 2, 0
  constructor
  · exact Nat.prime_two
  · simp only [pow_zero]
    have hfloor : ⌊(1 : ℝ)⌋₊ = 1 := by norm_num
    rw [hfloor]

/-- 5 = 3 + 2^1 is representable for C = 2. -/
theorem five_representable_C2 : IsRepresentable 2 5 := by
  use 3, 1
  constructor
  · exact Nat.prime_three
  · simp only [pow_one]
    norm_num

/-- 10 = 2 + 2^3 is representable for C = 2. -/
theorem ten_representable_C2 : IsRepresentable 2 10 := by
  use 2, 3
  constructor
  · exact Nat.prime_two
  · norm_num

/-! ## Part VI: Connection to Erdős #10 -/

/-- When C = 2, this is exactly the Romanoff set from Problem #10.
    The key difference from Problem #10 is:
    - Problem #10 asks: can EVERY integer be written as p + (≤k powers of 2)?
    - Problem #244 asks: does the set {p + 2^k} have positive DENSITY?

    Problem #10's negative answer (some integers can't be represented with any k)
    is consistent with Problem #244's positive answer (the representable set
    still has positive density). -/
theorem density_vs_universality :
    -- Even if not every integer is representable (Problem #10 is likely false),
    -- the representable set can still have positive density (Problem #244 is true for C=2)
    HasPositiveDensity (RepresentableSet 2) := romanoff_base_2

/-! ## Part VII: Summary -/

/-- Summary of known results:
    1. Integer C ≥ 2: Density is positive (Romanoff 1934) ✓
    2. Almost all C > 1: Density is positive (Ding 2025) ✓
    3. All C > 1: Density is positive? (OPEN - Erdős believes yes) -/
theorem problem_244_summary :
    -- Romanoff's result for integers
    (∀ C : ℕ, 2 ≤ C → HasPositiveDensity (RepresentableSet (C : ℝ))) ∧
    -- Ding's result for almost all C
    (∃ (N : Set ℝ), MeasureTheory.volume N = 0 ∧
      ∀ C : ℝ, C > 1 → C ∉ N → HasPositiveDensity (RepresentableSet C)) :=
  ⟨romanoff_theorem, ding_almost_all⟩

#check erdos_244_conjecture
#check romanoff_theorem
#check ding_almost_all

end Erdos244
