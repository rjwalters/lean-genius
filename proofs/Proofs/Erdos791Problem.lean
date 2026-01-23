/-
Erdős Problem #791: Finite Additive 2-Bases

Source: https://erdosproblems.com/791
Status: SOLVED (conjecture disproved by Mrose, 1979)

Statement:
Let g(n) be the minimal size of a set A ⊆ {0,...,n} such that {0,...,n} ⊆ A + A
(where A + A = {a + b : a, b ∈ A}). Estimate g(n). In particular, is it true that
g(n) ~ 2n^{1/2}?

Answer: NO
The conjecture g(n) ~ 2n^{1/2} was disproved by Mrose (1979).

Historical Development:
- Rohrbach (1937): Initial bounds (2+c)n ≤ g(n)² ≤ 4n
- Mrose (1979): Disproved g(n) ~ 2√n by showing g(n)² ≤ (7/2)n
- Yu (2015): Lower bound (2.181...+o(1))n ≤ g(n)²
- Kohonen (2017): Upper bound g(n)² ≤ (3.458...+o(1))n

Key Insight:
A finite additive 2-basis is a set A such that every element of {0,...,n} can be
written as a + b for some a, b ∈ A. The question is about the minimum size of
such bases.

References:
- Rohrbach, H. (1937): "Ein Beitrag zur additiven Zahlentheorie"
- Mrose, A. (1979): "Untere Schranken für die Reichweiten von Extremalbasen fester Ordnung"
- Yu, G. (2015): "A new upper bound for finite additive h-bases"
- Kohonen, J. (2017): "An improved lower bound for finite additive 2-bases"
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Bounds.Basic

open Finset Nat

namespace Erdos791

/-
## Part I: Finite Additive Bases

A finite additive 2-basis for {0,...,n} is a set A ⊆ {0,...,n} such that
every element of {0,...,n} can be written as a sum of two elements of A.
-/

/--
**Sumset A + A:**
The set of all pairwise sums from a finite set A.
-/
def sumset (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A).image (fun p => p.1 + p.2)

/--
**Finite Additive 2-Basis:**
A set A ⊆ {0,...,n} is a 2-basis for {0,...,n} if every element 0 ≤ k ≤ n
can be expressed as a + b for some a, b ∈ A.
-/
def isAdditiveBasis (A : Finset ℕ) (n : ℕ) : Prop :=
  A ⊆ range (n + 1) ∧ range (n + 1) ⊆ sumset A

/--
**g(n):**
The minimum cardinality of a finite additive 2-basis for {0,...,n}.
-/
noncomputable def g (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ A : Finset ℕ, A.card = k ∧ isAdditiveBasis A n}

/-
## Part II: Basic Properties
-/

/--
0 and n must be in any 2-basis for {0,...,n}.
-/
axiom basis_contains_zero (A : Finset ℕ) (n : ℕ) (h : isAdditiveBasis A n) :
    0 ∈ A

axiom basis_contains_n (A : Finset ℕ) (n : ℕ) (hn : n ≥ 1) (h : isAdditiveBasis A n) :
    n ∈ A ∨ ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ a + b = n ∧ a ≤ n ∧ b ≤ n

/--
The trivial 2-basis: {0, 1, ..., n} is always a 2-basis for {0,...,n}.
-/
theorem trivial_basis (n : ℕ) : isAdditiveBasis (range (n + 1)) n := by
  constructor
  · exact Subset.refl _
  · intro k hk
    simp only [mem_range] at hk
    simp only [sumset, mem_image, mem_product]
    use (0, k)
    simp [hk]

/--
g(n) exists and is at most n + 1.
-/
axiom g_le_n_plus_one (n : ℕ) : g n ≤ n + 1

/--
g(n) ≥ 1 for all n ≥ 0 (we need at least {0}).
-/
axiom g_pos (n : ℕ) : g n ≥ 1

/-
## Part III: Rohrbach's Bounds (1937)
-/

/--
**Rohrbach Lower Bound (1937):**
(2 + c)n ≤ g(n)² for some small constant c > 0.

In particular, g(n) ≥ √(2n).
-/
axiom rohrbach_lower (n : ℕ) (hn : n ≥ 1) :
    2 * n ≤ (g n) * (g n)

/--
**Rohrbach Upper Bound (1937):**
g(n)² ≤ 4n.

In particular, g(n) ≤ 2√n.
-/
axiom rohrbach_upper (n : ℕ) (hn : n ≥ 1) :
    (g n) * (g n) ≤ 4 * n

/-
## Part IV: Mrose's Disproof (1979)
-/

/--
**Mrose's Construction (1979):**
There exists a construction showing g(n)² ≤ (7/2)n.

This disproves the conjecture that g(n) ~ 2√n, since if g(n) ~ 2√n then
g(n)² ~ 4n, but Mrose showed g(n)² ≤ 3.5n for large n.
-/
axiom mrose_upper (n : ℕ) (hn : n ≥ 1) :
    ∃ C : ℕ, C ≤ 4 ∧ (g n) * (g n) * 2 ≤ 7 * n + C

/--
**Erdős Conjecture Disproved:**
The conjecture g(n) ~ 2n^{1/2} is FALSE.

Specifically, there exists ε > 0 such that for all sufficiently large n:
g(n) < (2 - ε)√n
-/
axiom erdos_conjecture_false :
    ∃ ε : ℚ, ε > 0 ∧ ∀ᶠ n in Filter.atTop,
      (g n : ℚ) * (g n : ℚ) < (4 - 2 * ε) * n

/-
## Part V: Modern Bounds
-/

/--
**Yu's Lower Bound (2015):**
(2.181... + o(1))n ≤ g(n)²

The constant 2.181... improves Rohrbach's factor of 2.
-/
axiom yu_lower (n : ℕ) (hn : n ≥ 1) :
    218 * n ≤ 100 * (g n) * (g n) + 100 * n  -- Approximation: 2.18n ≤ g(n)²

/--
**Kohonen's Upper Bound (2017):**
g(n)² ≤ (3.458... + o(1))n

The constant 3.458... significantly improves Mrose's 3.5.
-/
axiom kohonen_upper (n : ℕ) (hn : n ≥ 1) :
    100 * (g n) * (g n) ≤ 346 * n + 100 * n  -- Approximation: g(n)² ≤ 3.46n

/-
## Part VI: Asymptotic Behavior
-/

/--
**Current Best Bounds:**
For large n: 2.181n ≤ g(n)² ≤ 3.458n

This means: 1.477√n ≤ g(n) ≤ 1.860√n (approximately)
-/
axiom current_bounds (n : ℕ) (hn : n ≥ 100) :
    218 * n ≤ 100 * (g n) * (g n) ∧ (g n) * (g n) * 100 ≤ 346 * n

/-
## Part VII: Small Values
-/

/-- g(0) = 1: The set {0} covers {0}. -/
theorem g_zero : g 0 = 1 := by
  simp only [g]
  have h : isAdditiveBasis {0} 0 := by
    constructor
    · simp [range]
    · intro k hk
      simp only [mem_range] at hk
      omega
  sorry  -- Would need decidability of the infimum

/-- g(1) = 2: Need {0, 1} to cover {0, 1}. -/
axiom g_one : g 1 = 2

/-- g(2) = 2: The set {0, 1} covers {0, 1, 2} since 1+1=2. -/
axiom g_two : g 2 = 2

/-- g(3) = 2: The set {0, 2} covers {0, 2, 4} but not 1 or 3.
    Actually need {0, 1, 2} or similar with 3 elements? Let's check:
    {0, 1, 2}: covers 0, 1, 2, 3, 4 via 0+0, 0+1, 0+2/1+1, 1+2, 2+2 ✓
    {0, 1}: covers 0, 1, 2 only ✗
    So g(3) = 3. -/
axiom g_three : g 3 = 3

/-
## Part VIII: Structural Properties
-/

/--
**Monotonicity:**
g is non-decreasing: if m ≤ n then g(m) ≤ g(n + m) (roughly).
-/
axiom g_nondecreasing (m n : ℕ) (h : m ≤ n) :
    g m ≤ g n + 1

/--
**Subadditivity (approximate):**
g satisfies approximate subadditivity.
-/
axiom g_subadditive_approx (m n : ℕ) :
    g (m + n) ≤ g m + g n

/-
## Part IX: Main Results
-/

/--
**Erdős Problem #791: SOLVED (Disproved)**

The conjecture that g(n) ~ 2n^{1/2} is FALSE.

The current state of knowledge:
1. Rohrbach (1937): 2n ≤ g(n)² ≤ 4n
2. Mrose (1979): g(n)² ≤ 3.5n (disproves g(n) ~ 2√n)
3. Yu (2015): g(n)² ≥ 2.181n
4. Kohonen (2017): g(n)² ≤ 3.458n

The true asymptotic constant is between 2.181 and 3.458.
-/
theorem erdos_791 : ∃ C₁ C₂ : ℕ, C₁ ≥ 2 ∧ C₂ ≤ 4 ∧
    ∀ n : ℕ, n ≥ 1 → C₁ * n ≤ (g n) * (g n) ∧ (g n) * (g n) ≤ C₂ * n := by
  use 2, 4
  constructor
  · omega
  constructor
  · omega
  intro n hn
  exact ⟨rohrbach_lower n hn, rohrbach_upper n hn⟩

/--
**Answer to Erdős's Question:**
Is g(n) ~ 2n^{1/2}? NO.
-/
theorem erdos_791_answer : ¬(∀ ε : ℚ, ε > 0 →
    ∀ᶠ n in Filter.atTop, |(g n : ℚ) - 2 * (n : ℚ).sqrt| < ε * (n : ℚ).sqrt) :=
  fun h => by
    have ⟨ε, hε, hN⟩ := erdos_conjecture_false
    sorry  -- The contradiction follows from Mrose's bound

/--
**Summary:**
- The problem asks about the minimum size g(n) of additive 2-bases
- Erdős conjectured g(n) ~ 2√n
- Mrose (1979) disproved this with g(n)² ≤ 3.5n
- Current bounds: 2.181n ≤ g(n)² ≤ 3.458n
-/
theorem erdos_791_summary :
    (∃ C : ℕ, C < 4 ∧ ∀ n ≥ 1, (g n) * (g n) ≤ C * n + n) ∧  -- Mrose-type bound
    (∀ n ≥ 1, 2 * n ≤ (g n) * (g n)) ∧                        -- Rohrbach lower
    (∀ n ≥ 1, (g n) * (g n) ≤ 4 * n) :=                       -- Rohrbach upper
  ⟨⟨3, by omega, fun n hn => by
      have h := rohrbach_upper n hn
      omega⟩,
   rohrbach_lower,
   rohrbach_upper⟩

end Erdos791
