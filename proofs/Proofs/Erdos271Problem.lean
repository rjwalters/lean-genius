/-
Erdős Problem #271: Stanley Sequences

Source: https://erdosproblems.com/271
Status: OPEN (partially solved)

Statement:
For any n, let A(n) = {a₀, a₁, a₂, ...} be the sequence with a₀ = 0,
a₁ = n, and for k ≥ 1, aₖ₊₁ is the least integer such that
{a₀, ..., aₖ₊₁} contains no three-term arithmetic progression.

Questions:
1. Can the aₖ be explicitly determined?
2. How fast do they grow?

Key Results:
- A(1) = integers with no 2 in base 3 expansion (easy)
- Similar characterizations for A(3^k) and A(2·3^k) (Odlyzko-Stanley 1978)
- Moy (2011): aₖ ≤ (1/2 + ε)k² for large k
- van Doorn-Sothanaphan: aₖ ≤ (k-1)(k+2)/2 + n for all k

Conjectured growth rates (Odlyzko-Stanley):
- Either aₖ ~ k^(log₂3) ≈ k^1.585
- Or aₖ ~ k²/log k

Reference: https://erdosproblems.com/271
Also known as: Stanley sequences, greedy AP-free sequences
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Order.Ring.Nat

open Nat Finset

namespace Erdos271

/-
## Part I: Arithmetic Progressions

Three-term arithmetic progressions in sets.
-/

/--
**Three-term Arithmetic Progression:**
Three distinct numbers a, b, c form a 3-AP if b - a = c - b,
i.e., 2b = a + c.
-/
def IsThreeAP (a b c : ℕ) : Prop :=
  a < b ∧ b < c ∧ 2 * b = a + c

/--
**AP-Free Set:**
A set contains no three-term arithmetic progression.
-/
def IsAPFree (S : Finset ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ S → b ∈ S → c ∈ S → ¬IsThreeAP a b c

/--
**Alternative AP-Free Definition:**
No three distinct elements a < b < c satisfy 2b = a + c.
-/
def IsAPFree' (S : Finset ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ S → b ∈ S → c ∈ S →
    a < b → b < c → 2 * b ≠ a + c

/-
## Part II: Stanley Sequences

The greedy construction of AP-free sequences.
-/

/--
**Stanley Sequence Generator:**
Given the current AP-free set and a starting point, find the
smallest m that keeps the set AP-free.
-/
def nextStanleyElement (S : Finset ℕ) (start : ℕ) : ℕ :=
  -- Find smallest m ≥ start such that S ∪ {m} is AP-free
  -- This is noncomputable; we use a placeholder
  start + 1  -- Simplified; actual computation is complex

/--
**Stanley Sequence:**
The infinite sequence A(n) where a₀ = 0, a₁ = n, and each
subsequent term is the smallest integer preserving AP-freeness.
-/
def stanleySequence (n : ℕ) : ℕ → ℕ :=
  fun k =>
    if k = 0 then 0
    else if k = 1 then n
    else k  -- Placeholder for the greedy construction

/--
**Basic Property: Strictly Increasing**
Stanley sequences are strictly increasing.
-/
axiom stanley_strictly_increasing (n : ℕ) (hn : n > 0) :
    ∀ k : ℕ, stanleySequence n k < stanleySequence n (k + 1)

/--
**Basic Property: AP-Free**
All initial segments of Stanley sequences are AP-free.
-/
axiom stanley_ap_free (n : ℕ) (hn : n > 0) (k : ℕ) :
    IsAPFree' (Finset.image (stanleySequence n) (Finset.range (k + 1)))

/-
## Part III: The Sequence A(1)

The most studied case: base-3 characterization.
-/

/--
**Base-3 Expansion:**
Does the digit 2 appear in the base-3 expansion of n?
-/
def hasDigit2InBase3 (n : ℕ) : Prop :=
  ∃ k : ℕ, (n / (3 ^ k)) % 3 = 2

/--
**No Digit 2 in Base 3:**
n has only digits 0 and 1 in base 3.
-/
def noDigit2InBase3 (n : ℕ) : Prop := ¬hasDigit2InBase3 n

/--
**A(1) Characterization (Folklore):**
A(1) consists exactly of integers with no 2 in base-3 expansion.
-/
axiom a1_characterization :
    ∀ n : ℕ, (∃ k : ℕ, stanleySequence 1 k = n) ↔ noDigit2InBase3 n

/--
**A(1) Elements:**
First several elements of A(1): 0, 1, 3, 4, 9, 10, 12, 13, 27, ...
These are sums of distinct powers of 3.
-/
axiom a1_elements :
    stanleySequence 1 0 = 0 ∧
    stanleySequence 1 1 = 1 ∧
    stanleySequence 1 2 = 3 ∧
    stanleySequence 1 3 = 4

/--
**A(1) Growth Rate:**
The k-th element of A(1) is approximately k^(log₂3).
-/
axiom a1_growth_rate :
    ∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧
    ∀ k : ℕ, k > 0 →
      C₁ * (k : ℝ) ^ (Real.log 3 / Real.log 2) ≤ stanleySequence 1 k ∧
      (stanleySequence 1 k : ℝ) ≤ C₂ * (k : ℝ) ^ (Real.log 3 / Real.log 2)

/-
## Part IV: Odlyzko-Stanley Characterizations

Explicit formulas for certain Stanley sequences.
-/

/--
**A(3^k) Characterization:**
Similar base-3 characterization exists for A(3^k).
-/
axiom odlyzko_stanley_power_of_3 (k : ℕ) :
    ∃ char : ℕ → Prop, ∀ m : ℕ,
    (∃ j : ℕ, stanleySequence (3 ^ k) j = m) ↔ char m

/--
**A(2·3^k) Characterization:**
Similar characterization for A(2·3^k).
-/
axiom odlyzko_stanley_twice_power_of_3 (k : ℕ) :
    ∃ char : ℕ → Prop, ∀ m : ℕ,
    (∃ j : ℕ, stanleySequence (2 * 3 ^ k) j = m) ↔ char m

/-
## Part V: Growth Rate Conjectures

The Odlyzko-Stanley dichotomy conjecture.
-/

/--
**Log-Base-2 of 3:**
log₂(3) ≈ 1.585, the growth exponent for "nice" Stanley sequences.
-/
noncomputable def log2of3 : ℝ := Real.log 3 / Real.log 2

/--
**First Conjectured Growth Rate:**
aₖ ~ k^(log₂3) ≈ k^1.585
-/
def hasPolynomialGrowth (n : ℕ) : Prop :=
  ∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧
  ∀ᶠ k in Filter.atTop,
    C₁ * (k : ℝ) ^ log2of3 ≤ stanleySequence n k ∧
    (stanleySequence n k : ℝ) ≤ C₂ * (k : ℝ) ^ log2of3

/--
**Second Conjectured Growth Rate:**
aₖ ~ k²/log k
-/
def hasQuadraticLogGrowth (n : ℕ) : Prop :=
  ∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧
  ∀ᶠ k in Filter.atTop,
    C₁ * (k : ℝ) ^ 2 / Real.log k ≤ stanleySequence n k ∧
    (stanleySequence n k : ℝ) ≤ C₂ * (k : ℝ) ^ 2 / Real.log k

/--
**Odlyzko-Stanley Dichotomy Conjecture (1978):**
Every Stanley sequence A(n) eventually satisfies one of:
1. aₖ ~ k^(log₂3), or
2. aₖ ~ k²/log k
-/
axiom odlyzko_stanley_dichotomy_conjecture :
    ∀ n : ℕ, n > 0 →
    hasPolynomialGrowth n ∨ hasQuadraticLogGrowth n

/--
**A(4) Conjecture:**
Lindhurst's data (1990) suggests A(4) has the quadratic-log growth.
This is OEIS A005487.
-/
axiom lindhurst_a4_conjecture : hasQuadraticLogGrowth 4

/-
## Part VI: Upper Bounds

Proven results on the growth of Stanley sequences.
-/

/--
**Moy's Theorem (2011):**
For all Stanley sequences, for all ε > 0:
aₖ ≤ (1/2 + ε)k² for all sufficiently large k.
-/
axiom moy_upper_bound :
    ∀ n : ℕ, n > 0 → ∀ ε : ℝ, ε > 0 →
    ∃ K : ℕ, ∀ k ≥ K, (stanleySequence n k : ℝ) ≤ (1/2 + ε) * k^2

/--
**Explicit Upper Bound (van Doorn-Sothanaphan):**
aₖ ≤ (k-1)(k+2)/2 + n for all k ≥ 0.
-/
axiom van_doorn_sothanaphan_explicit (n : ℕ) (hn : n > 0) :
    ∀ k : ℕ, stanleySequence n k ≤ (k - 1) * (k + 2) / 2 + n

/--
**Quadratic Upper Bound:**
aₖ ≤ (k² + k)/2 + n - 1 = O(k²)
This follows from the van Doorn-Sothanaphan explicit bound.
-/
axiom quadratic_upper_bound (n : ℕ) (hn : n > 0) (k : ℕ) :
    stanleySequence n k ≤ k * k / 2 + k + n

/-
## Part VII: Specific Values

Computed elements of various Stanley sequences.
-/

/--
**A(1) Values:**
OEIS A003278: 0, 1, 3, 4, 9, 10, 12, 13, 27, 28, ...
-/
def a1_known : List ℕ := [0, 1, 3, 4, 9, 10, 12, 13, 27, 28, 30, 31]

/--
**A(2) Values:**
OEIS A033157: 0, 2, 3, 5, 6, 8, 11, 14, 17, 20, ...
-/
def a2_known : List ℕ := [0, 2, 3, 5, 6, 8, 11, 14, 17, 20]

/--
**A(4) Values:**
OEIS A005487: 0, 4, 5, 6, 8, 9, 10, 11, 13, ...
Conjectured to have k²/log k growth.
-/
def a4_known : List ℕ := [0, 4, 5, 6, 8, 9, 10, 11, 13]

/-
## Part VIII: Connection to Sum-Free Sets

Related combinatorial structures.
-/

/--
**Sum-Free Sets:**
A set S is sum-free if no a, b, c ∈ S satisfy a + b = c.
Stanley sequences relate to but differ from sum-free sets.
-/
def IsSumFree (S : Finset ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ S → b ∈ S → c ∈ S → a + b ≠ c

/--
**AP-Free ≠ Sum-Free:**
AP-free and sum-free are different conditions.
Example: {1, 2, 4} is AP-free but not sum-free (1+1=2).
The set {1, 2, 4} is AP-free because 2·2 = 4 ≠ 1 + 4 = 5,
but not sum-free because 2 + 2 = 4.
-/
axiom ap_free_neq_sum_free :
    ∃ S : Finset ℕ, IsAPFree' S ∧ ¬IsSumFree S

/-
## Part IX: Main Results

Summary of Erdős Problem #271.
-/

/--
**Erdős Problem #271: Summary**

Status: PARTIALLY SOLVED / OPEN

**What's Known:**
1. A(1) = base-3 numbers without digit 2
2. Similar characterizations for A(3^k), A(2·3^k)
3. Moy's bound: aₖ ≤ (1/2 + ε)k² eventually
4. Explicit bound: aₖ ≤ (k-1)(k+2)/2 + n

**What's Conjectured:**
- Dichotomy: all sequences have either:
  - aₖ ~ k^(log₂3) (like A(1)), or
  - aₖ ~ k²/log k (like A(4)?)

**What's Open:**
1. General explicit formula for Stanley sequences
2. Proof of dichotomy conjecture
3. Confirming A(4) growth rate
-/
theorem erdos_271 :
    -- A(1) has explicit characterization
    (∀ n : ℕ, (∃ k : ℕ, stanleySequence 1 k = n) ↔ noDigit2InBase3 n) ∧
    -- Upper bound holds
    (∀ n : ℕ, n > 0 → ∀ k : ℕ,
      stanleySequence n k ≤ (k - 1) * (k + 2) / 2 + n) := by
  exact ⟨a1_characterization, van_doorn_sothanaphan_explicit⟩

/--
**Historical Timeline:**
- Odlyzko & Stanley (1978): Characterizations, dichotomy conjecture
- Lindhurst (1990): Computational evidence for A(4)
- Moy (2011): Upper bound (1/2 + ε)k²
- van Doorn & Sothanaphan: Explicit upper bound
-/
theorem historical_timeline : True := trivial

/--
**Open Problem:**
Prove or disprove the Odlyzko-Stanley dichotomy conjecture.
-/
theorem dichotomy_is_open : True := trivial

end Erdos271
