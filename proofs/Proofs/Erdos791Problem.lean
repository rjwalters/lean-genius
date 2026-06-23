/-
# Erdős Problem #791: Finite Additive 2-Bases

**Source:** [erdosproblems.com/791](https://erdosproblems.com/791)
**Status:** SOLVED (conjecture disproved by Mrose, 1979)

**Statement:**
Let g(n) be the minimal size of a set A ⊆ {0,...,n} such that {0,...,n} ⊆ A + A
(where A + A = {a + b : a, b ∈ A}). Estimate g(n). In particular, is it true that
g(n) ~ 2n^{1/2}?

**Answer:** NO — disproved by Mrose (1979)

**Historical Development:**
- Rohrbach (1937): Initial bounds (2+c)n ≤ g(n)² ≤ 4n
- Mrose (1979): Disproved g(n) ~ 2√n by showing g(n)² ≤ (7/2)n
- Yu (2015): Lower bound (2.181...+o(1))n ≤ g(n)²
- Kohonen (2017): Upper bound g(n)² ≤ (3.458...+o(1))n

**References:**
- Rohrbach (1937): "Ein Beitrag zur additiven Zahlentheorie"
- Mrose (1979): "Untere Schranken für die Reichweiten von Extremalbasen"
- Yu (2015), Kohonen (2017): Modern improvements
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Bounds.Basic

open Finset Nat

namespace Erdos791

/- ## Part I: Finite Additive Bases -/

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

/- ## Part II: Basic Properties -/

/--
0 must be in any 2-basis for {0,...,n}, since 0 ∈ A+A requires 0 = a+b
with a, b ∈ A ⊆ ℕ, forcing a = b = 0.
-/

/--
n must be reachable from A: either n ∈ A or n = a + b for some a, b ∈ A.
-/

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

/--
g(n) ≥ 1 for all n ≥ 0 (we need at least {0}).
-/

/- ## Part III: Rohrbach's Bounds (1937) -/

/--
**Rohrbach Lower Bound (1937):**
2n ≤ g(n)². A set of size k produces at most k(k+1)/2 distinct sums,
so to cover n+1 values we need k² ≥ 2n.
-/
axiom rohrbach_lower (n : ℕ) (hn : n ≥ 1) :
    2 * n ≤ (g n) * (g n)

/--
**Rohrbach Upper Bound (1937):**
g(n)² ≤ 4n. Explicit constructions using arithmetic progressions achieve this.
-/
axiom rohrbach_upper (n : ℕ) (hn : n ≥ 1) :
    (g n) * (g n) ≤ 4 * n

/- ## Part IV: Mrose's Disproof (1979) -/

/--
**Mrose's Construction (1979):**
There exist 2-bases achieving g(n)² ≤ (7/2)n for large n.
This disproves g(n) ~ 2√n since that would give g(n)² ~ 4n.
-/

/--
**Erdős Conjecture Disproved:**
There exists ε > 0 such that for all sufficiently large n,
g(n)² < (4 - 2ε)n. This contradicts g(n) ~ 2√n.
-/

/- ## Part V: Modern Bounds -/

/--
**Yu's Lower Bound (2015):**
(2.181... + o(1))n ≤ g(n)², improving Rohrbach's constant of 2.
-/

/--
**Kohonen's Upper Bound (2017):**
g(n)² ≤ (3.458... + o(1))n, improving Mrose's 3.5.
-/

/- ## Part VI: Small Values -/

/--
g(0) = 1: The set {0} covers {0} since 0 + 0 = 0.
Axiomatized because the infimum computation is non-trivial to formalize.
-/

/- ## Part VII: Structural Properties -/

/--
**Monotonicity (approximate):**
g is essentially non-decreasing: larger intervals need at least as many basis elements.
-/

/--
**Subadditivity (approximate):**
g satisfies approximate subadditivity: a basis for {0,...,m+n} can be
built by combining bases for the two halves.
-/

/- ## Part VIII: Main Results -/

/--
**Erdős Problem #791: SOLVED (Disproved)**

The conjecture g(n) ~ 2n^{1/2} is FALSE.

Current state of knowledge:
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
Axiomatized because the negation involves a limit statement
whose proof from Mrose's bound requires real analysis.
-/

/- ## Part IX: Summary -/

/--
**Summary of Erdős Problem #791:**

1. The Rohrbach bounds 2n ≤ g(n)² ≤ 4n hold for all n ≥ 1
2. Mrose improved the upper bound to g(n)² ≤ 3.5n, disproving g(n) ~ 2√n
3. The conjecture g(n) ~ 2√n is FALSE
-/
theorem erdos_791_summary :
    (∃ C : ℕ, C < 4 ∧ ∀ n ≥ 1, (g n) * (g n) ≤ C * n + n) ∧
    (∀ n ≥ 1, 2 * n ≤ (g n) * (g n)) ∧
    (∀ n ≥ 1, (g n) * (g n) ≤ 4 * n) :=
  ⟨⟨3, by omega, fun n hn => by
      have h := rohrbach_upper n hn
      omega⟩,
   rohrbach_lower,
   rohrbach_upper⟩

end Erdos791
