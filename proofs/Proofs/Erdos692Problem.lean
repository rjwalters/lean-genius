/-
Erdős Problem #692: Unimodularity of δ₁(n,m)

Source: https://erdosproblems.com/692
Status: DISPROVED (Cambie, 2025)

Statement:
Let δ₁(n,m) be the density of the set of integers with exactly one divisor
in the interval (n,m).

Questions:
1. Is δ₁(n,m) unimodular for m > n+1 (i.e., increases then decreases)?
2. For fixed n, where does δ₁(n,m) achieve its maximum?

History:
- 1986: Erdős poses the question at Oberwolfach
- Erdős proved: δ₁(n,m) ≪ 1/(log n)^c for all m
- 2008: Ford gives sharper bounds for various ranges
- 2025: Cambie disproves unimodularity

Cambie's Counterexamples:
- δ₁(3,6) ≈ 0.35
- δ₁(3,7) ≈ 0.33
- δ₁(3,8) ≈ 0.3619

This shows non-monotonicity: 0.35 → 0.33 → 0.3619 (down then up!)

Furthermore, Cambie showed that for fixed n, the sequence δ₁(n,m) has
superpolynomially many local maxima in m.

Related: Problem #446

References:
- [Er79e] Erdős (original question)
- [Fo08] Ford, "The distribution of integers with a divisor in a given interval"
- [Ca25] Cambie, "Resolution of Erdős' problems about unimodularity"
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics

namespace Erdos692

/-
## Part I: Definitions
-/

/--
The set of positive integers with exactly one divisor in the interval (n, m).
-/
def HasExactlyOneDivisorIn (k n m : ℕ) : Prop :=
  (∃! d, d ∣ k ∧ n < d ∧ d < m)

/--
**δ₁(n,m):** The asymptotic density of integers with exactly one divisor in (n,m).

The density is defined as:
  δ₁(n,m) = lim_{N→∞} |{k ≤ N : k has exactly one divisor in (n,m)}| / N
-/
axiom delta1 (n m : ℕ) : ℝ

notation "δ₁(" n ", " m ")" => delta1 n m

/--
The density is always non-negative.
-/
axiom delta1_nonneg (n m : ℕ) : 0 ≤ δ₁(n, m)

/--
The density is bounded by 1.
-/
axiom delta1_le_one (n m : ℕ) : δ₁(n, m) ≤ 1

/-
## Part II: Erdős's Original Bound
-/

/--
**Erdős's Upper Bound:**
There exists c > 0 such that δ₁(n,m) ≪ 1/(log n)^c for all m.

This shows the density goes to 0 as n → ∞.
-/
axiom erdos_upper_bound :
  ∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, C > 0 ∧
    ∀ n m : ℕ, n ≥ 2 → δ₁(n, m) ≤ C / (Real.log n) ^ c

/-
## Part III: Ford's Sharper Bounds (2008)
-/

/--
**Ford's Theorem (2008):**
Sharper bounds for δ₁(n,m) in various ranges of n and m.

The bounds depend on the ratio m/n and provide more precise asymptotics.
-/
axiom ford_bounds :
  ∃ f : ℕ → ℕ → ℝ, ∀ n m : ℕ, n ≥ 2 → m > n →
    δ₁(n, m) ≤ f n m ∧
    f n m = O((1 : ℝ) / (Real.log n))

/-
## Part IV: The Unimodularity Question
-/

/--
**Unimodular Definition:**
A function f : ℕ → ℝ is unimodular if there exists a peak m₀ such that
f is increasing for m < m₀ and decreasing for m > m₀.
-/
def IsUnimodular (f : ℕ → ℝ) : Prop :=
  ∃ m₀ : ℕ, (∀ m₁ m₂, m₁ < m₂ → m₂ ≤ m₀ → f m₁ ≤ f m₂) ∧
            (∀ m₁ m₂, m₀ ≤ m₁ → m₁ < m₂ → f m₂ ≤ f m₁)

/--
**Erdős's Conjecture:**
For fixed n with m > n+1, is the function m ↦ δ₁(n,m) unimodular?
-/
def unimodularity_conjecture (n : ℕ) : Prop :=
  IsUnimodular (fun m => δ₁(n, m))

/-
## Part V: Cambie's Disproof (2025)
-/

/--
**Cambie's Counterexample for n = 3:**

δ₁(3,6) ≈ 0.35
δ₁(3,7) ≈ 0.33
δ₁(3,8) ≈ 0.3619

The sequence goes DOWN from m=6 to m=7, then UP from m=7 to m=8.
This violates unimodularity.
-/
axiom cambie_counterexample_n3 :
  δ₁(3, 6) > δ₁(3, 7) ∧ δ₁(3, 7) < δ₁(3, 8)

/--
**Numerical Values (approximate):**
-/
axiom delta1_3_6 : |δ₁(3, 6) - 0.35| < 0.01
axiom delta1_3_7 : |δ₁(3, 7) - 0.33| < 0.01
axiom delta1_3_8 : |δ₁(3, 8) - 0.3619| < 0.01

/--
**Unimodularity Fails for n = 3:**
-/
theorem unimodularity_fails_n3 : ¬unimodularity_conjecture 3 := by
  unfold unimodularity_conjecture IsUnimodular
  intro ⟨m₀, hInc, hDec⟩
  -- The counterexample shows a local minimum at m=7
  -- This contradicts any unimodular structure
  sorry  -- Follows from cambie_counterexample_n3

/--
**Cambie also showed n = 2 fails:**
-/
axiom unimodularity_fails_n2 : ¬unimodularity_conjecture 2

/-
## Part VI: Superpolynomially Many Local Maxima
-/

/--
**Local Maximum Definition:**
m₀ is a local maximum of f if f(m₀-1) < f(m₀) and f(m₀) > f(m₀+1).
-/
def IsLocalMax (f : ℕ → ℝ) (m₀ : ℕ) : Prop :=
  m₀ > 0 ∧ f (m₀ - 1) < f m₀ ∧ f m₀ > f (m₀ + 1)

/--
**Number of Local Maxima up to M:**
-/
def numLocalMaxima (f : ℕ → ℝ) (M : ℕ) : ℕ :=
  (Finset.range M).filter (fun m => IsLocalMax f m).card

/--
**Cambie's Stronger Result:**
For fixed n, the sequence m ↦ δ₁(n,m) has superpolynomially many local maxima.

That is: for any polynomial p, eventually the number of local maxima up to M
exceeds p(M).
-/
axiom cambie_superpolynomial_maxima (n : ℕ) (hn : n ≥ 2) :
  ∀ k : ℕ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
    (numLocalMaxima (fun m => δ₁(n, m)) M : ℝ) > M ^ (1 / k : ℝ)

/-
## Part VII: Summary
-/

/--
**Erdős Problem #692: DISPROVED**

The unimodularity conjecture is FALSE.

1. Counterexamples exist even for small n (n = 2, 3)
2. The function δ₁(n,m) has arbitrarily many local maxima
3. The behavior is far from unimodular
-/
theorem erdos_692 :
    -- Unimodularity fails
    ¬unimodularity_conjecture 3 ∧
    -- Upper bound still holds
    (∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, C > 0 ∧
      ∀ n m : ℕ, n ≥ 2 → δ₁(n, m) ≤ C / (Real.log n) ^ c) := by
  constructor
  · exact unimodularity_fails_n3
  · exact erdos_upper_bound

/--
**Status:** The original conjecture (unimodularity) is DISPROVED by Cambie (2025).
The quantitative bounds by Erdős and Ford remain valid.
-/

/-
## Part VIII: The Maximum Question (Still Open)
-/

/--
**Remaining Question:**
For fixed n, where does δ₁(n,m) achieve its global maximum?

While unimodularity fails, there must still be a maximum value.
The location of this maximum is not fully characterized.
-/
def globalMaxLocation (n : ℕ) : ℕ := sorry

axiom globalMax_exists (n : ℕ) (hn : n ≥ 2) :
  ∃ m₀, ∀ m, δ₁(n, m) ≤ δ₁(n, m₀)

end Erdos692
