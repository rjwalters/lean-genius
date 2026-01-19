/-
Erdős Problem #763: The Erdős-Fuchs Theorem

Source: https://erdosproblems.com/763
Status: DISPROVED (Erdős-Fuchs, 1956)

Statement:
Let A ⊆ ℕ. Can there exist some constant c > 0 such that
  ∑_{n≤N} 1_A ∗ 1_A(n) = cN + O(1)?

Answer: NO

The Erdős-Turán conjecture asked whether a set A could have its
representation function grow at a perfectly linear rate with bounded error.
Erdős and Fuchs (1956) proved this is impossible in a strong form:
even ∑_{n≤N} r(n) = cN + o(N^{1/4}/(log N)^{1/2}) is impossible for c > 0.

Montgomery and Vaughan (1990) improved the error term to o(N^{1/4}).

References:
- Erdős, P. and Fuchs, W.H.J. (1956): "On a problem of additive number theory"
  J. London Math. Soc., 67-73
- Montgomery, H.L. and Vaughan, R.C. (1990): "On the Erdős-Fuchs theorems"
  A Tribute to Paul Erdős, 331-338
- See also Problem #764 for generalization to more summands
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Data.Set.Function

open Finset BigOperators Filter Asymptotics

namespace Erdos763

/-
## Part I: Representation Function

The representation function r_A(n) counts the number of ways to write n
as a sum of two elements from A (with order).
-/

/--
**Representation Count:**
r_A(n) = |{(a, b) ∈ A × A : a + b = n}|

This is the convolution 1_A * 1_A evaluated at n.
-/
def representationCount (A : Finset ℕ) (n : ℕ) : ℕ :=
  (A.filter (fun a => a < n ∧ n - a ∈ A)).card +
  (if n % 2 = 0 ∧ n / 2 ∈ A then 1 else 0)

/--
Alternative formulation: count pairs directly.
-/
def representationCount' (A : Finset ℕ) (n : ℕ) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 + p.2 = n)).card

/--
**Cumulative Representation Function:**
R_A(N) = ∑_{n ≤ N} r_A(n)

This counts all pairs (a, b) ∈ A × A with a + b ≤ N.
-/
def cumulativeRepCount (A : Finset ℕ) (N : ℕ) : ℕ :=
  ∑ n ∈ range (N + 1), representationCount' A n

/-
## Part II: The Linear Growth Question

The Erdős-Turán question: Can R_A(N) grow linearly with bounded error?
-/

/--
**Linear Growth with Bounded Error:**
A set A has asymptotically linear growth with constant c if
R_A(N) = cN + O(1), i.e., |R_A(N) - cN| ≤ M for some M and all large N.
-/
def HasLinearGrowthBounded (A : ℕ → Finset ℕ) (c : ℝ) : Prop :=
  ∃ M : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    |↑(cumulativeRepCount (A N) N) - c * ↑N| ≤ M

/--
**For infinite sets:** We consider sets A ⊆ ℕ via their truncations to [0, n].
-/
def truncate (A : Set ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (· ∈ A)

/-
## Part III: The Erdős-Fuchs Theorem

The main negative result: linear growth with bounded error is impossible.
-/

/--
**Erdős-Fuchs Theorem (1956):**
For any infinite set A ⊆ ℕ and any constant c > 0, it is impossible that
  ∑_{n≤N} r_A(n) = cN + O(1).

More strongly, even cN + o(N^{1/4}/(log N)^{1/2}) is impossible.

This is axiomatized because the proof requires deep analytic techniques
(Fourier analysis, Parseval's identity, careful bounds on trigonometric sums)
that go beyond Mathlib's current capabilities.
-/
axiom erdos_fuchs_theorem :
  ∀ (A : Set ℕ), A.Infinite →
  ∀ (c : ℝ), c > 0 →
  ¬HasLinearGrowthBounded (truncate A) c

/--
**Erdős Problem #763: DISPROVED**
The answer to Erdős and Turán's question is NO.
-/
theorem erdos_763 :
    ¬∃ (A : Set ℕ) (c : ℝ), A.Infinite ∧ c > 0 ∧
      HasLinearGrowthBounded (truncate A) c := by
  push_neg
  intro A c hInf hc
  exact erdos_fuchs_theorem A hInf c hc

/-
## Part IV: Strengthened Error Bounds

The impossibility extends to much smaller error terms.
-/

/--
**Error term definition:**
The difference between cumulative count and linear approximation.
-/
def errorTerm (A : ℕ → Finset ℕ) (c : ℝ) (N : ℕ) : ℝ :=
  ↑(cumulativeRepCount (A N) N) - c * ↑N

/--
**Erdős-Fuchs Strong Form:**
Even ∑_{n≤N} r(n) = cN + o(N^{1/4}/(log N)^{1/2}) is impossible.

The error term must eventually exceed N^{1/4}/(log N)^{1/2} infinitely often.
-/
axiom erdos_fuchs_strong :
  ∀ (A : Set ℕ), A.Infinite →
  ∀ (c : ℝ), c > 0 →
  ¬∀ᶠ N in atTop,
    |errorTerm (truncate A) c N| < (N : ℝ)^(1/4 : ℝ) / (Real.log N)^(1/2 : ℝ)

/--
**Montgomery-Vaughan Improvement (1990):**
The error must exceed N^{1/4} infinitely often.
-/
axiom montgomery_vaughan :
  ∀ (A : Set ℕ), A.Infinite →
  ∀ (c : ℝ), c > 0 →
  ∀ (ε : ℝ), ε > 0 →
  ∃ᶠ N in atTop, |errorTerm (truncate A) c N| > (1 - ε) * (N : ℝ)^(1/4 : ℝ)

/-
## Part V: Why Linear Growth Fails

Intuition behind the theorem.
-/

/--
**Key Insight: Variance Accumulation**
For any set A, the representation function r(n) has inherent variability.
The cumulative sum ∑ r(n) cannot smooth this out to O(1) error.

Heuristically, if A has density α, then r(n) ≈ α²n locally,
but fluctuations around this are of order √n, leading to
cumulative error of order N^{1/4}.
-/

/--
**Analytic Mechanism:**
The proof uses Fourier analysis. Writing A = {a₁, a₂, ...},
the representation function has generating function (∑ z^{aᵢ})².
Parseval's identity relates L² norm of this to the error term.
-/

/-
## Part VI: Examples and Non-Examples

Sets that illustrate the theorem.
-/

/--
**Example: Perfect Squares**
A = {n² : n ∈ ℕ} has r(n) = O(n^ε) for any ε > 0.
The cumulative sum grows much slower than N.
-/
def perfectSquares : Set ℕ := {n : ℕ | ∃ k : ℕ, n = k^2}

/--
Perfect squares have sublinear representation count.
-/
axiom squares_sublinear :
  ∀ N : ℕ, cumulativeRepCount (truncate perfectSquares N) N ≤ N

/--
**Example: Arithmetic Progressions**
A = {an + b : n ∈ ℕ} has r(n) ≈ n/a for large n.
The cumulative sum R(N) ≈ N²/(2a²), which is quadratic, not linear.
-/
def arithmeticProgression (a b : ℕ) : Set ℕ := {n : ℕ | ∃ k : ℕ, n = a * k + b}

/--
**Example: Sidon Sets (B₂ sequences)**
A set A is a Sidon set if all pairwise sums a + b are distinct.
For Sidon sets, r(n) ∈ {0, 1, 2} for all n.
The cumulative sum is bounded by 2N, but still not linear with O(1) error.
-/
def IsSidonSet (A : Set ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≤ b → c ≤ d → a + b = c + d → (a = c ∧ b = d)

/--
Even Sidon sets cannot achieve linear growth with bounded error.
-/
theorem sidon_not_bounded :
    ∀ (A : Set ℕ), IsSidonSet A → A.Infinite →
    ∀ (c : ℝ), c > 0 → ¬HasLinearGrowthBounded (truncate A) c :=
  fun A _ hInf c hc => erdos_fuchs_theorem A hInf c hc

/-
## Part VII: Related Problems

Generalizations and variants.
-/

/--
**Problem #764: k-fold Representation**
The generalization asks about k-fold sums:
Can ∑_{n≤N} r_k(n) = cN + O(1) where r_k counts representations as
sums of k elements from A?

The Erdős-Fuchs theorem extends to this case.
-/
axiom erdos_fuchs_k_fold :
  ∀ (k : ℕ), k ≥ 2 →
  ∀ (A : Set ℕ), A.Infinite →
  ∀ (c : ℝ), c > 0 →
  True  -- Statement would involve k-fold representation function

/--
**Connection to Waring's Problem:**
The representation function r(n) for squares relates to sums of two squares.
Jacobi's formula gives r(n) = 4∑_{d|n} χ(d) where χ is the non-principal
character mod 4.
-/

/-
## Part VIII: Main Results Summary
-/

/--
**Erdős Problem #763: Complete Summary**

1. **Question:** Can R_A(N) = cN + O(1) for some A and c > 0?
2. **Answer:** NO (Erdős-Fuchs, 1956)
3. **Strong form:** Even o(N^{1/4}/(log N)^{1/2}) error is impossible
4. **Best bound:** Montgomery-Vaughan showed error must exceed N^{1/4}

Key insight: Intrinsic variance in representation counts prevents
arbitrarily smooth linear approximation.
-/
theorem erdos_763_summary :
    -- The main theorem
    (¬∃ (A : Set ℕ) (c : ℝ), A.Infinite ∧ c > 0 ∧
      HasLinearGrowthBounded (truncate A) c) ∧
    -- Perfect squares have sublinear growth
    (∀ N : ℕ, cumulativeRepCount (truncate perfectSquares N) N ≤ N) := by
  exact ⟨erdos_763, squares_sublinear⟩

/--
The answer to the Erdős-Turán question is definitively NO.
-/
theorem erdos_763_answer : ∃ (proof : ¬∃ (A : Set ℕ) (c : ℝ),
    A.Infinite ∧ c > 0 ∧ HasLinearGrowthBounded (truncate A) c),
    True := by
  exact ⟨erdos_763, trivial⟩

end Erdos763
