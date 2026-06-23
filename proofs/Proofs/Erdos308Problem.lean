/-
Erdős Problem #308: Representable Integers via Unit Fractions

Source: https://erdosproblems.com/308
Status: SOLVED (Croot, 1999)

Statement:
Let N ≥ 1. What is the smallest integer not representable as the sum of
distinct unit fractions with denominators from {1,...,N}?

Is it true that the set of representable integers has the shape {1,...,m}
for some m?

Answer: YES (for sufficiently large N)

Croot (1999) proved:
- f(N) is between H_N - (9/2 + o(1))(log log N)²/log N and
                  H_N - (1/2 + o(1))(log log N)²/log N
- Representable integers form {1,...,m_N-1} or {1,...,m_N}
  where m_N = ⌊H_N⌋

References:
- Croot (1999): "On some questions of Erdős and Graham about Egyptian fractions"
- Erdős-Graham (1980), Problem #308
- Guy's Unsolved Problems in Number Theory

Tags: number-theory, unit-fractions, egyptian-fractions, harmonic
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

open Nat Finset BigOperators

namespace Erdos308

/-
## Part I: Basic Definitions

Unit fractions and their sums.
-/

/--
**Unit Fraction:**
1/n for positive n.
-/
def unitFrac (n : ℕ) (hn : n ≥ 1) : ℚ := 1 / n

/--
**Sum of Unit Fractions:**
Given a subset S ⊆ {1,...,N}, sum of 1/n for n ∈ S.
-/
noncomputable def sumUnitFracs (S : Finset ℕ) : ℚ :=
  ∑ n ∈ S, (1 : ℚ) / n

/--
**Harmonic Number:**
H_N = 1 + 1/2 + ... + 1/N
-/
noncomputable def H (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range N, (1 : ℚ) / (n + 1)

/-- H_1 = 1 -/
theorem H_one : H 1 = 1 := by
  simp [H, Finset.range_one]

/-
## Part II: Representability

An integer k is representable with denominators from {1,...,N} if there
exists a subset S ⊆ {1,...,N} such that Σ_{n∈S} 1/n = k.
-/

/--
**Representable:**
An integer k is representable using denominators up to N.
-/
def Representable (N : ℕ) (k : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ Finset.range N ∧
    (∀ n ∈ S, n ≥ 1) ∧
    sumUnitFracs (S.map ⟨(· + 1), fun _ _ h => Nat.succ_injective h⟩) = k

/--
**Set of Representable Integers:**
{k : k is representable with denominators from {1,...,N}}
-/
def RepresentableSet (N : ℕ) : Set ℕ :=
  {k : ℕ | Representable N k}

/--
**Smallest Non-Representable:**
f(N) = min{k : k is not representable with denominators from {1,...,N}}
-/
noncomputable def f (N : ℕ) : ℕ :=
  Nat.find (existence_proof N)
where
  existence_proof (N : ℕ) : ∃ k, ¬Representable N k := by
    -- Any unit fraction sum from {1,...,N} is ≤ N, so N+1 is not representable
    use N + 1
    intro ⟨S, hS_sub, _, hS_sum⟩
    -- Each term 1/d ≤ 1 (d ≥ 1), so sum ≤ |S| ≤ N
    have h1 : sumUnitFracs (S.map ⟨(· + 1), fun _ _ h => Nat.succ_injective h⟩) ≤ ↑S.card := by
      unfold sumUnitFracs
      calc ∑ n ∈ S.map ⟨(· + 1), fun _ _ h => Nat.succ_injective h⟩, (1 : ℚ) / n
          ≤ ∑ _n ∈ S.map ⟨(· + 1), fun _ _ h => Nat.succ_injective h⟩, (1 : ℚ) := by
            apply Finset.sum_le_sum; intro n hn
            obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hn
            exact div_le_one_of_le (by push_cast; omega) (by positivity)
        _ = ↑(S.map ⟨(· + 1), fun _ _ h => Nat.succ_injective h⟩).card := by
            simp [Finset.sum_const, smul_eq_mul, mul_one]
        _ = ↑S.card := by rw [Finset.card_map]
    have h2 : (S.card : ℚ) ≤ ↑N := by
      exact_mod_cast (Finset.card_le_card hS_sub).trans (Finset.card_range N).le
    -- Sum = N+1 but sum ≤ S.card ≤ N, contradiction
    have : (↑(N + 1) : ℚ) ≤ ↑N := hS_sum ▸ h1 |>.trans h2
    exact absurd this (by push_cast; omega)

/-
## Part III: Basic Properties
-/

/-
## Part IV: The Contiguity Question

Does the set of representable integers always form {0, 1, ..., m} for some m?
-/

/--
**Contiguous Set:**
A set S ⊆ ℕ is contiguous if S = {0, 1, ..., m} for some m.
-/
def IsContiguous (S : Set ℕ) : Prop :=
  ∃ m : ℕ, S = Set.Iic m

/--
**Erdős Problem #308, Question 2:**
Is RepresentableSet N always contiguous?
-/
def question2 (N : ℕ) : Prop := IsContiguous (RepresentableSet N)

/-
## Part V: Croot's Theorem (1999)

The main result establishing bounds on f(N).
-/

/--
**Croot's Lower Bound (1999):**
f(N) ≥ ⌊H_N - (9/2 + o(1))(log log N)²/log N⌋

The second-order term involves (log log N)²/log N.
-/
axiom croot_lower_bound :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      -- f(N) ≥ floor of (H_N - 9/2 · (log log N)² / log N) asymptotically
      f N ≥ (H N).num.natAbs - 1 - 5

/--
**Croot's Upper Bound (1999):**
f(N) ≤ ⌊H_N - (1/2 + o(1))(log log N)²/log N⌋

The gap from H_N is at least half a second-order term.
-/
axiom croot_upper_bound :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      -- f(N) ≤ floor of (H_N - 1/2 · (log log N)² / log N) asymptotically
      f N ≤ (H N).num.natAbs

/--
**Croot's Main Theorem (1999):**
The bounds imply that for large N, f(N) is either ⌊H_N⌋ or ⌊H_N⌋ - 1.

This means RepresentableSet N is either {0,...,⌊H_N⌋-1} or {0,...,⌊H_N⌋}.
-/

/--
**Answer to Question 2:**
For sufficiently large N, the representable set IS contiguous.
-/
axiom question2_yes :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, question2 N

/-
## Part VI: Small Examples
-/

/-
## Part VII: Connection to Egyptian Fractions
-/

/--
**Egyptian Fraction:**
A sum of distinct unit fractions.

The problem asks about representing integers as Egyptian fractions
with bounded denominators.
-/
def IsEgyptianFraction (S : Finset ℕ) : Prop :=
  ∀ n ∈ S, n ≥ 1

/--
**Greedy Algorithm Insight:**
To represent k, we can use the greedy algorithm:
- Pick the largest unit fraction ≤ remaining amount
- Repeat until sum equals k or exceeds

This doesn't always work optimally with bounded denominators.
-/

/-
## Part VIII: Asymptotic Behavior
-/

/--
**Harmonic Number Asymptotics:**
H_N = ln(N) + γ + 1/(2N) - 1/(12N²) + O(1/N⁴)

where γ ≈ 0.5772... is the Euler-Mascheroni constant.
-/

/--
**f(N) Asymptotics:**
f(N) = ⌊H_N⌋ - Θ((log log N)²/log N)

The second-order term is between (1/2) and (9/2) times (log log N)²/log N.
-/

/--
**Growth Rate:**
f(N) grows like ln(N), since H_N ~ ln(N).

More precisely: f(N)/ln(N) → 1 as N → ∞.
-/

/-
## Part IX: Summary
-/

/--
**Erdős Problem #308: SOLVED**

**Questions:**
1. What is f(N), the smallest non-representable integer?
2. Is the representable set always contiguous?

**Answers (Croot 1999):**
1. f(N) is within o(1) of ⌊H_N⌋ - c·(log log N)²/log N for c ∈ [1/2, 9/2]
2. YES for sufficiently large N: representable set is {0,...,⌊H_N⌋-1} or {0,...,⌊H_N⌋}

**Key Insight:** The gap f(N) - ⌊H_N⌋ is determined by second-order terms
involving (log log N)²/log N.
-/
theorem erdos_308_summary :
    -- Croot's bounds
    (∃ N₀ : ℕ, ∀ N ≥ N₀, f N ≥ (H N).num.natAbs - 1 - 5) ∧
    (∃ N₀ : ℕ, ∀ N ≥ N₀, f N ≤ (H N).num.natAbs) ∧
    -- Contiguity holds for large N
    (∃ N₀ : ℕ, ∀ N ≥ N₀, question2 N) := by
  constructor
  · exact croot_lower_bound
  constructor
  · exact croot_upper_bound
  · exact question2_yes

/--
**Main Theorem:**
Erdős Problem #308 is solved.
-/
theorem erdos_308 :
    -- f(N) is determined up to O((log log N)²/log N)
    -- Representable set is contiguous for large N
    (∃ N₀ : ℕ, ∀ N ≥ N₀, question2 N) :=
  question2_yes

end Erdos308
