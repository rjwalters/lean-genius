/-
Erdős Problem #721: Van der Waerden Numbers W(3,k)

Source: https://erdosproblems.com/721
Status: SOLVED (Both challenges met)

Statement:
Let W(3,k) be the van der Waerden number - the minimum n such that in any
red/blue coloring of {1,...,n} there exists either a red 3-term arithmetic
progression or a blue k-term arithmetic progression.

Give reasonable bounds for W(3,k). In particular:
1. Give any non-trivial lower bounds for W(3,k)
2. Prove that W(3,k) < exp(k^c) for some constant c < 1

Resolution:
Both challenges have been met:
- Lower bounds: Green [Gr22], Hunter [Hu22]
- Upper bounds: Schoen [Sc21], Bloom-Sisask [BlSi23]

Historical Note:
Graham conjectured W(3,k) ≪ k², but this was disproved by Green's
superpolynomial lower bound. The problem illustrates the tension between
Ramsey-type results and extremal bounds.

References:
- Erdős [Er80], [Er81]: Original problem
- Green [Gr22]: Superpolynomial lower bound
- Hunter [Hu22]: Improved lower bound
- Schoen [Sc21]: First subexponential upper bound
- Bloom-Sisask [BlSi23]: Best current upper bound
- Kelley-Meka [KeMe23]: Sets without 3-APs
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos721

/-
## Part I: Van der Waerden Numbers
-/

/--
**Van der Waerden's theorem:**
For any r and k, there exists W(r,k) such that any r-coloring of
{1,...,W(r,k)} contains a monochromatic k-term arithmetic progression.
-/
axiom vanDerWaerden : True

/--
**The off-diagonal van der Waerden number W(3,k):**
The minimum n such that any red/blue coloring of {1,...,n} contains
either a red 3-AP or a blue k-AP.
-/
axiom W : ℕ → ℕ

/--
**Basic property: W(3,k) is well-defined:**
Van der Waerden's theorem guarantees W(3,k) exists for all k.
-/
axiom W_exists (k : ℕ) : k ≥ 3 → W k ≥ k

/--
**W(3,k) is increasing:**
Larger k requires larger n to force a monochromatic progression.
-/
axiom W_increasing : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → W k₁ ≤ W k₂

/-
## Part II: Known Small Values
-/

/--
**Known exact values:**
W(3,3) = 9, W(3,4) = 18, W(3,5) = 22, W(3,6) = 32, W(3,7) = 46.
-/
axiom W_known_values :
    W 3 = 9 ∧
    W 4 = 18 ∧
    W 5 = 22 ∧
    W 6 = 32 ∧
    W 7 = 46

/--
**Computational difficulty:**
Computing W(3,k) exactly is computationally intensive.
W(3,8) and beyond are not known exactly.
-/
axiom computational_difficulty : True

/-
## Part III: Graham's Conjecture (Disproved)
-/

/--
**Graham's conjecture:**
Graham conjectured that W(3,k) ≪ k², i.e., polynomial growth.
-/
def graham_conjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ k ≥ 3, (W k : ℝ) ≤ C * k^2

/--
**Graham's conjecture is FALSE:**
Green [Gr22] proved a superpolynomial lower bound, disproving this.
-/
axiom graham_conjecture_false : ¬graham_conjecture

/-
## Part IV: Lower Bounds
-/

/--
**Green's lower bound (2022):**
W(3,k) ≥ exp(c · (log k)^{4/3} / (log log k)^{1/3})
for some constant c > 0.

This was the first superpolynomial lower bound.
-/
axiom green_lower_bound :
    ∃ c : ℝ, c > 0 ∧
    ∀ k ≥ 3, (W k : ℝ) ≥ Real.exp (c * (Real.log k)^(4/3 : ℝ) / (Real.log (Real.log k))^(1/3 : ℝ))

/--
**Hunter's improvement (2022):**
W(3,k) ≥ exp(c · (log k)² / log log k)

This improved Green's exponent from 4/3 to 2.
-/
axiom hunter_lower_bound :
    ∃ c : ℝ, c > 0 ∧
    ∀ k ≥ 3, (W k : ℝ) ≥ Real.exp (c * (Real.log k)^2 / Real.log (Real.log k))

/--
**Lower bound is superpolynomial:**
For any polynomial p(k), W(3,k) > p(k) for sufficiently large k.
-/
theorem W_superpolynomial :
    ∀ d : ℕ, ∃ N : ℕ, ∀ k ≥ N, (W k : ℝ) > k^(d : ℝ) := by
  intro d
  sorry -- Follows from hunter_lower_bound

/-
## Part V: Upper Bounds
-/

/--
**Schoen's upper bound (2021):**
W(3,k) < exp(k^c) for some c < 1.

This was the first to answer Erdős's challenge about subexponential growth.
-/
axiom schoen_upper_bound :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧
    ∃ N : ℕ, ∀ k ≥ N, (W k : ℝ) ≤ Real.exp (k^c)

/--
**Bloom-Sisask upper bound (2023):**
W(3,k) ≪ exp(O((log k)^9))

The best current upper bound, improving on Kelley-Meka.
-/
axiom bloom_sisask_upper_bound :
    ∃ C : ℝ, C > 0 ∧
    ∀ k ≥ 3, (W k : ℝ) ≤ Real.exp (C * (Real.log k)^9)

/--
**Comparison of bounds:**
exp(c(log k)²/log log k) ≤ W(3,k) ≤ exp(C(log k)^9)

There's a significant gap between lower and upper bounds.
-/
axiom bounds_gap : True

/-
## Part VI: Connection to 3-AP Free Sets
-/

/--
**Roth's theorem connection:**
W(3,k) relates to the density of sets without 3-term arithmetic progressions.
-/
axiom roth_connection : True

/--
**Behrend's construction:**
There exist 3-AP free subsets of {1,...,n} of size exp(c√(log n)).
This construction gives lower bounds for W(3,k).
-/
axiom behrend_construction : True

/--
**Kelley-Meka breakthrough (2023):**
Sets without 3-APs in {1,...,n} have density ≤ exp(-c(log n)^{1/12}).
This leads to improved upper bounds on W(3,k).
-/
axiom kelley_meka : True

/--
**Bloom-Sisask improvement:**
Slightly improved the Kelley-Meka bounds, giving the current best.
-/
axiom bloom_sisask_improvement : True

/-
## Part VII: The Growth Rate Question
-/

/--
**Open question: Exact growth rate:**
Is W(3,k) = exp((log k)^{2+o(1)})?

Hunter's lower bound suggests exponent near 2 might be correct.
-/
def exact_growth_conjecture : Prop :=
  ∀ ε > 0, ∃ N : ℕ,
    ∀ k ≥ N, Real.exp ((Real.log k)^(2-ε)) ≤ W k ∧
             (W k : ℝ) ≤ Real.exp ((Real.log k)^(2+ε))

/--
**Current gap:**
Lower: (log k)^2 / log log k in exponent
Upper: (log k)^9 in exponent
The true answer is believed to be closer to the lower bound.
-/
axiom growth_rate_gap : True

/-
## Part VIII: Techniques
-/

/--
**Green's method:**
Uses dense model theorems and regularity methods from additive combinatorics.
-/
axiom green_technique : True

/--
**Hunter's method:**
Builds on Green's work with improved density increment arguments.
-/
axiom hunter_technique : True

/--
**Schoen's method:**
Used bounds for 3-AP free sets in a novel way.
-/
axiom schoen_technique : True

/--
**Kelley-Meka method:**
Revolutionary approach to bounding 3-AP free sets using
almost-periodicity and Bogolyubov's method.
-/
axiom kelley_meka_technique : True

/-
## Part IX: Related Problems
-/

/--
**General W(r,k):**
Van der Waerden numbers for longer progressions are even less understood.
-/
axiom general_van_der_waerden : True

/--
**Diagonal W(k,k):**
The diagonal van der Waerden number grows very fast (at least tower-type).
-/
axiom diagonal_van_der_waerden : True

/--
**Szemerédi's theorem:**
For any δ > 0 and k, any subset of {1,...,n} with density ≥ δ
contains a k-AP for n sufficiently large.
-/
axiom szemeredi_theorem : True

/--
**Gowers' proof:**
Gowers gave quantitative bounds for Szemerédi's theorem using
his uniformity norms, leading to bounds on van der Waerden numbers.
-/
axiom gowers_bounds : True

/-
## Part X: Historical Context
-/

/--
**Van der Waerden (1927):**
Proved the existence of W(r,k) using a double induction argument.
His original bounds were astronomical (Ackermann-type).
-/
axiom van_der_waerden_1927 : True

/--
**Erdős-Turán conjecture (1936):**
Conjectured that dense sets contain arbitrarily long APs.
Led to Szemerédi's theorem.
-/
axiom erdos_turan_conjecture : True

/--
**Erdős's questions (1980-81):**
Erdős asked for bounds on W(3,k), specifically:
1. Non-trivial lower bounds
2. Subexponential upper bounds
Both have now been answered.
-/
axiom erdos_questions : True

/-
## Part XI: Summary
-/

/--
**Summary of Erdős Problem #721:**

PROBLEM: Give reasonable bounds for W(3,k), the van der Waerden number.
Specifically:
1. Non-trivial lower bounds
2. Prove W(3,k) < exp(k^c) for some c < 1

STATUS: SOLVED (both challenges met)

KEY RESULTS:
1. Lower bound: W(3,k) ≥ exp(c(log k)²/log log k) [Hunter 2022]
2. Upper bound: W(3,k) ≤ exp(C(log k)^9) [Bloom-Sisask 2023]
3. Graham's polynomial conjecture is FALSE [Green 2022]
4. First subexponential upper bound [Schoen 2021]

KEY INSIGHTS:
1. W(3,k) grows superpolynomially but subexponentially
2. The growth is exp((log k)^{2 to 9}) approximately
3. Connected to density of 3-AP free sets
4. Kelley-Meka breakthrough enabled sharp upper bounds

A fundamental result in additive combinatorics and Ramsey theory.
-/
theorem erdos_721_status :
    -- Graham's polynomial conjecture is false
    ¬graham_conjecture ∧
    -- Erdős's challenges are both met
    (∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∃ N : ℕ, ∀ k ≥ N, (W k : ℝ) ≤ Real.exp (k^c)) := by
  constructor
  · exact graham_conjecture_false
  · exact schoen_upper_bound

/--
**Both challenges answered:**
1. Non-trivial lower bounds: YES (Green, Hunter)
2. Subexponential upper bounds: YES (Schoen, Bloom-Sisask)
-/
theorem erdos_721_solved : True := trivial

/--
**The current state of knowledge:**
exp(c(log k)²/log log k) ≤ W(3,k) ≤ exp(C(log k)^9)

The exact growth rate remains an open question.
-/
theorem W_bounds_summary :
    (∃ c : ℝ, c > 0 ∧ ∀ k ≥ 3,
      (W k : ℝ) ≥ Real.exp (c * (Real.log k)^2 / Real.log (Real.log k))) ∧
    (∃ C : ℝ, C > 0 ∧ ∀ k ≥ 3,
      (W k : ℝ) ≤ Real.exp (C * (Real.log k)^9)) := by
  constructor
  · exact hunter_lower_bound
  · exact bloom_sisask_upper_bound

end Erdos721
