/-
# Erdős Problem #796: Second-Order Terms for g_k(n)

Source: https://erdosproblems.com/796
Status: OPEN

Statement:
Let k ≥ 2 and g_k(n) be the largest |A| for A ⊆ {1,...,n} such that
every m has < k solutions to m = a₁a₂ with a₁ < a₂ ∈ A.

Is it true that:
  g₃(n) = (log log n / log n)·n + (c + o(1))·n/(log n)²
for some constant c?

Known Results:
- Erdős (1964): For 2^{r-1} < k ≤ 2^r,
  g_k(n) ~ ((log log n)^{r-1} / (r-1)!) · n/log n
- For k = 3 (so r = 2): g₃(n) ~ (log log n / log n)·n
- Second-order term bounds: c₁·n/(log n)² ≤ error ≤ c₂·n/(log n)²
- Exact value of c: OPEN

Related: Problem #425 handles k = 2 case

References:
- Erdős (1964): "On the multiplicative representation of integers"
- Erdős (1969): Discussion of second-order terms

Tags: number-theory, multiplicative-representation, asymptotics
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Real Finset

namespace Erdos796

/-
## Part I: Basic Definitions
-/

/--
**Product Representation:**
(a₁, a₂) is a representation of m if a₁ < a₂ and a₁·a₂ = m.
-/
def IsProductRep (m : ℕ) (a₁ a₂ : ℕ) : Prop :=
  a₁ < a₂ ∧ a₁ * a₂ = m

/--
**Representation Count:**
The number of ways to write m as a₁·a₂ with a₁ < a₂, both in A.
-/
noncomputable def repCount (A : Finset ℕ) (m : ℕ) : ℕ :=
  (A.filter fun a₁ => ∃ a₂ ∈ A, a₁ < a₂ ∧ a₁ * a₂ = m).card

/--
**k-Bounded Representation:**
Every integer has fewer than k representations from A.
-/
def IsBoundedRep (A : Finset ℕ) (k : ℕ) : Prop :=
  ∀ m : ℕ, repCount A m < k

/--
**Valid Subset:**
A ⊆ {1,...,n} with bounded representations.
-/
def IsValidSubset (A : Finset ℕ) (n k : ℕ) : Prop :=
  (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) ∧ IsBoundedRep A k

/-
## Part II: The g_k(n) Function
-/

/--
**The Function g_k(n):**
Maximum size of A ⊆ {1,...,n} where every m has < k representations.
-/
noncomputable def g (k n : ℕ) : ℕ :=
  Finset.sup (Finset.filter (fun A => IsValidSubset A n k)
    (Finset.powerset (Finset.range (n + 1)))) Finset.card

/--
**g is well-defined:**
The maximum exists since we're optimizing over a finite set.
-/
/-
## Part III: Erdős's First-Order Asymptotics
-/

/--
**Integers with r Distinct Prime Factors:**
Count of n-smooth integers with exactly r distinct prime factors.
-/
noncomputable def omega_count (n r : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter (fun m => m.factors.toFinset.card = r) |>.card

/--
**Asymptotic Formula for omega_count:**
|{m ≤ n : ω(m) = r}| ~ ((log log n)^{r-1} / (r-1)!) · n/log n
-/
/--
**Erdős (1964) Main Theorem:**
For 2^{r-1} < k ≤ 2^r, we have g_k(n) ~ ω-count with r factors.

In particular:
- k = 2: g₂(n) ~ n/log n (primes!)
- k = 3, 4: g_k(n) ~ (log log n / log n)·n (semiprimes)
- k = 5,...,8: g_k(n) ~ ((log log n)² / 2·log n)·n
-/
axiom erdos_1964_main (k r : ℕ) (hk : k ≥ 2) (hr : 2^(r-1) < k ∧ k ≤ 2^r) :
    ∀ ε > 0, ∀ᶠ n in Filter.atTop,
      |((g k n : ℝ) - (Real.log (Real.log n))^(r-1) / (r-1).factorial *
        n / Real.log n)| < ε * n / Real.log n

/-
## Part IV: The k = 3 Case
-/

/--
**First-Order for k = 3:**
g₃(n) ~ (log log n / log n)·n

Here 2^1 = 2 < 3 ≤ 4 = 2^2, so r = 2.
-/
theorem g3_first_order :
    ∀ ε > 0, ∀ᶠ n in Filter.atTop,
      |((g 3 n : ℝ) - (Real.log (Real.log n)) * n / Real.log n)| <
        ε * n / Real.log n := by
  intro ε hε
  have := erdos_1964_main 3 2 (by norm_num) ⟨by norm_num, by norm_num⟩ ε hε
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at this
  exact this

/-
## Part V: Second-Order Terms
-/

/--
**Second-Order Term for g₃(n):**
Define E₃(n) = g₃(n) - (log log n / log n)·n
The question is whether E₃(n) = (c + o(1))·n/(log n)² for some c.
-/
noncomputable def E3 (n : ℕ) : ℝ :=
  (g 3 n : ℝ) - (Real.log (Real.log n)) * n / Real.log n

/--
**Known Bounds on E₃(n):**
c₁·n/(log n)² ≤ E₃(n) ≤ c₂·n/(log n)² for some 0 < c₁ ≤ c₂.
-/
axiom E3_bounded :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
      ∀ᶠ n in Filter.atTop,
        c₁ * n / (Real.log n)^2 ≤ E3 n ∧
        E3 n ≤ c₂ * n / (Real.log n)^2

/--
**The Main Conjecture (OPEN):**
E₃(n) = (c + o(1))·n/(log n)² for some specific constant c.
-/
def erdosConjecture796 : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ ε > 0, ∀ᶠ n in Filter.atTop,
    |E3 n - c * n / (Real.log n)^2| < ε * n / (Real.log n)^2

/-
## Part VI: The k = 2 Case (Problem #425)
-/

/--
**g₂(n) and Primes:**
For k = 2, we need A with no m having ≥2 representations.
This is closely related to the prime counting function.
-/
/-
## Part VII: Optimal Sets
-/

/--
**Near-Optimal Sets for g₃:**
Sets achieving g₃(n) are related to integers with 2 prime factors.
-/
def IsNearOptimal3 (A : Finset ℕ) (n : ℕ) : Prop :=
  IsValidSubset A n 3 ∧
  (A.card : ℝ) ≥ (1 - 0.01) * (g 3 n : ℝ)

/--
**Optimal sets resemble Ω=2 integers:**
Integers with exactly 2 prime factors (with multiplicity).
-/
/-
## Part VIII: Multiplicative Structure
-/

/--
**Divisor Function Connection:**
If τ(m) = d (divisor count), then m has ≤ d/2 representations.
Numbers with τ(m) ≤ 2k-1 are "safe" for g_k.
-/
/-
## Part IX: Summary

Erdős Problem #796 is OPEN.
-/

/-- Summary of Erdős Problem #796:
    1. First-order asymptotics known (Erdős 1964)
    2. Second-order bounds known (E₃ is Θ(n/(log n)²))
    3. Exact constant c in second-order term is OPEN -/
theorem erdos_796_summary :
    -- First-order asymptotics for k=3
    (∀ ε > 0, ∀ᶠ n in Filter.atTop,
      |((g 3 n : ℝ) - (Real.log (Real.log n)) * n / Real.log n)| <
        ε * n / Real.log n) ∧
    -- Second-order bounds exist
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
      ∀ᶠ n in Filter.atTop,
        c₁ * n / (Real.log n)^2 ≤ E3 n ∧
        E3 n ≤ c₂ * n / (Real.log n)^2) :=
  ⟨g3_first_order, E3_bounded⟩

end Erdos796
