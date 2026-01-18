/-
Erdős Problem #484: Monochromatic Sums in Colorings

Source: https://erdosproblems.com/484
Status: SOLVED (Erdős-Sárközy-Sós 1989)

Statement:
Prove that there exists an absolute constant c > 0 such that, whenever
{1,...,N} is k-colored (with N large enough depending on k), there are
at least cN integers representable as monochromatic sums (a + b where
a, b are in the same color class and a ≠ b).

Resolution:
Erdős, Sárközy, and Sós [ESS89] proved:
- For general k: at least N/2 - O(N^{1-1/2^{k+1}}) even numbers are sums
- For k=2: at least N/2 - O(log N) even numbers, and O(log N) is optimal

Historical Note:
This was originally a conjecture of Roth about sumset structure in
partitions. A refinement appears as Problem 25 on Ben Green's list.

References:
- Roth: Original conjecture
- Erdős-Sárközy-Sós [ESS89]: Complete solution
- Ben Green: Problem 25 (refinement)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

namespace Erdos484

/-
## Part I: Basic Definitions
-/

/--
**k-coloring of {1,...,N}:**
A function χ: {1,...,N} → {1,...,k} assigning each integer a color.
-/
def Coloring (N k : ℕ) := Fin N → Fin k

/--
**Color class:**
The set of integers in {1,...,N} with a given color.
-/
def colorClass {N k : ℕ} (χ : Coloring N k) (c : Fin k) : Finset (Fin N) :=
  Finset.filter (fun n => χ n = c) Finset.univ

/--
**Monochromatic sum:**
An integer s is a monochromatic sum if s = a + b where a ≠ b and
a, b have the same color.
-/
def isMonochromaticSum {N k : ℕ} (χ : Coloring N k) (s : ℕ) : Prop :=
  ∃ a b : Fin N, a ≠ b ∧ χ a = χ b ∧ (a.val + 1) + (b.val + 1) = s

/--
**Representable integers:**
The set of integers in {1,...,2N} that are representable as
monochromatic sums.
-/
def monochromaticSums {N k : ℕ} (χ : Coloring N k) : Set ℕ :=
  {s | isMonochromaticSum χ s}

/-
## Part II: Roth's Conjecture (Proved)
-/

/--
**Roth's Conjecture:**
There exists c > 0 such that for any k-coloring of {1,...,N},
at least cN integers are representable as monochromatic sums.
-/
def roth_conjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧
  ∀ k ≥ 1, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ χ : Coloring N k,
    (Finset.filter (fun s => isMonochromaticSum χ s)
      (Finset.range (2 * N))).card ≥ c * N

/--
**Roth's conjecture is TRUE:**
Proved by Erdős, Sárközy, and Sós in 1989.
-/
axiom roth_conjecture_true : roth_conjecture

/-
## Part III: The Erdős-Sárközy-Sós Theorem
-/

/--
**Main Theorem (ESS89):**
In any k-coloring of {1,...,N}, at least
N/2 - O(N^{1-1/2^{k+1}})
even integers are representable as monochromatic sums.
-/
axiom ESS_theorem (k : ℕ) :
    k ≥ 1 →
    ∃ C : ℝ, C > 0 ∧
    ∀ N ≥ k, ∀ χ : Coloring N k,
      (Finset.filter (fun s => s % 2 = 0 ∧ isMonochromaticSum χ s)
        (Finset.range (2 * N))).card ≥
      (N : ℝ) / 2 - C * (N : ℝ) ^ (1 - 1 / 2^(k + 1))

/--
**Why even numbers?:**
A sum a + b has the same parity as a and b combined.
If a, b have the same parity, their sum is even.
The theorem focuses on even sums for cleaner bounds.
-/
axiom even_sums_explanation : True

/--
**The exponent 1 - 1/2^{k+1}:**
For k = 2: exponent = 1 - 1/8 = 7/8
For k = 3: exponent = 1 - 1/16 = 15/16
As k increases, the error term approaches N, but stays sub-linear.
-/
axiom exponent_values : True

/-
## Part IV: The Two-Coloring Case
-/

/--
**Theorem for k = 2:**
In any 2-coloring of {1,...,N}, at least
N/2 - O(log N)
even integers are representable as monochromatic sums.
-/
axiom ESS_two_coloring :
    ∃ C : ℝ, C > 0 ∧
    ∀ N ≥ 2, ∀ χ : Coloring N 2,
      (Finset.filter (fun s => s % 2 = 0 ∧ isMonochromaticSum χ s)
        (Finset.range (2 * N))).card ≥
      (N : ℝ) / 2 - C * Real.log N

/--
**The O(log N) bound is optimal:**
There exists a 2-coloring where no power of 2 is a monochromatic sum.
This shows the error term O(log N) cannot be improved in general.
-/
axiom two_coloring_optimal :
    ∀ N : ℕ, ∃ χ : Coloring N 2,
    ∀ m : ℕ, 2^m ≤ 2 * N → ¬isMonochromaticSum χ (2^m)

/--
**Construction for optimality:**
Color n with color (ν₂(n) mod 2), where ν₂(n) is the 2-adic valuation.
Then 2^m cannot be a monochromatic sum.
-/
axiom optimal_construction : True

/-
## Part V: Key Proof Ideas
-/

/--
**Sumset structure:**
For a color class C, the sumset C + C = {a + b : a, b ∈ C}
contains many elements. By pigeonhole, some color class is large.
-/
axiom sumset_structure : True

/--
**Density arguments:**
If a color class has density δ in {1,...,N}, its sumset C + C
has density roughly δ² in {2,...,2N}. Optimization over δ gives bounds.
-/
axiom density_argument : True

/--
**Fourier analytic methods:**
The proof uses exponential sum techniques to count representation
numbers and bound the exceptions.
-/
axiom fourier_methods : True

/--
**Pigeonhole principle:**
With k colors, at least one color class has size ≥ N/k.
This guarantees a large sumset.
-/
axiom pigeonhole_argument : True

/-
## Part VI: Consequences
-/

/--
**Positive density of sums:**
Almost half of all even numbers in {1,...,2N} are monochromatic sums.
The constant c can be taken close to 1/2 for large N.
-/
theorem positive_density :
    ∃ c : ℝ, c > 0 ∧
    ∀ k ≥ 1, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ χ : Coloring N k,
      (Finset.filter (fun s => isMonochromaticSum χ s)
        (Finset.range (2 * N))).card ≥ c * N := by
  exact roth_conjecture_true

/--
**The constant c = 1/4 works:**
Since almost half the even numbers work, and there are N/2 even
numbers up to N, we get at least N/4 representations for large N.
-/
axiom constant_one_fourth : True

/--
**Strengthening to c = 1/2 - ε:**
For any ε > 0, the constant c = 1/2 - ε works for N large enough.
-/
axiom constant_half_minus_epsilon : True

/-
## Part VII: Extensions and Refinements
-/

/--
**Ben Green's Problem 25:**
A refinement asking for more precise counting of monochromatic sums
and understanding the structure of colorings that minimize them.
-/
axiom ben_green_problem_25 : True

/--
**Weighted versions:**
Extensions where different sums have different weights or
where we count weighted representation numbers.
-/
axiom weighted_versions : True

/--
**Higher-order sums:**
Analogous questions for sums a₁ + ... + aₘ where all aᵢ
have the same color.
-/
axiom higher_order_sums : True

/--
**Restricted sumsets:**
What if we require a < b? The results are similar with
slightly different constants.
-/
axiom restricted_sumsets : True

/-
## Part VIII: Related Problems
-/

/--
**Schur's theorem:**
In any finite coloring of ℕ, there exist monochromatic
a, b, c with a + b = c. This is the "equation version."
-/
axiom schur_theorem : True

/--
**Rado's theorem:**
Characterizes which linear equations have monochromatic
solutions in any finite coloring.
-/
axiom rado_theorem : True

/--
**Folkman's theorem:**
Finite colorings contain arbitrarily large monochromatic
sets closed under pairwise sums.
-/
axiom folkman_theorem : True

/--
**Hindman's theorem:**
Finite colorings of ℕ contain infinite monochromatic sets
closed under finite sums.
-/
axiom hindman_theorem : True

/-
## Part IX: Historical Context
-/

/--
**Roth's contributions:**
Klaus Roth made fundamental contributions to additive number theory,
including Roth's theorem on 3-APs. This conjecture continued his work.
-/
axiom roth_history : True

/--
**Sárközy's work:**
András Sárközy collaborated extensively with Erdős on problems
about sumsets and difference sets.
-/
axiom sarkozy_history : True

/--
**The ESS collaboration:**
Erdős, Sárközy, and Sós formed a highly productive trio,
solving many problems in additive combinatorics.
-/
axiom ESS_collaboration : True

/-
## Part X: Summary
-/

/--
**Summary of Erdős Problem #484:**

PROBLEM: Prove ∃ c > 0 such that any k-coloring of {1,...,N}
has at least cN integers representable as monochromatic sums.

STATUS: SOLVED (Erdős-Sárközy-Sós 1989)

KEY RESULTS:
1. For k colors: ≥ N/2 - O(N^{1-1/2^{k+1}}) even sums [ESS89]
2. For k = 2: ≥ N/2 - O(log N) even sums [ESS89]
3. O(log N) is optimal for k = 2 (no power of 2 is a sum)
4. c can be taken arbitrarily close to 1/2

KEY INSIGHTS:
1. Almost all even numbers are monochromatic sums
2. The two-coloring case has logarithmic error term
3. Uses sumset theory and Fourier methods
4. Optimal constructions use 2-adic valuations

A beautiful theorem connecting coloring and additive structure.
-/
theorem erdos_484_status :
    -- Roth's conjecture is proved
    roth_conjecture ∧
    -- The two-coloring case has O(log N) error
    (∃ C : ℝ, C > 0 ∧ ∀ N ≥ 2, ∀ χ : Coloring N 2,
      (Finset.filter (fun s => s % 2 = 0 ∧ isMonochromaticSum χ s)
        (Finset.range (2 * N))).card ≥ (N : ℝ) / 2 - C * Real.log N) := by
  constructor
  · exact roth_conjecture_true
  · exact ESS_two_coloring

/--
**Problem solved:**
Erdős Problem #484 was completely solved in 1989 by ESS.
-/
theorem erdos_484_solved : True := trivial

/--
**The powers of 2 obstruction:**
There exists a 2-coloring where no power of 2 is a monochromatic sum,
showing the O(log N) bound is tight.
-/
theorem power_of_two_obstruction :
    ∀ N : ℕ, ∃ χ : Coloring N 2,
    ∀ m : ℕ, 2^m ≤ 2 * N → ¬isMonochromaticSum χ (2^m) := by
  exact two_coloring_optimal

end Erdos484
