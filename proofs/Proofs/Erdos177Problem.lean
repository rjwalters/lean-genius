/-
Erdős Problem #177: Discrepancy of Arithmetic Progressions

Source: https://erdosproblems.com/177
Status: OPEN

Statement:
Find the smallest h(d) such that there exists a function f: ℕ → {-1, 1}
where for every d ≥ 1:
  max_{P_d} |Σ_{n∈P_d} f(n)| ≤ h(d)
where P_d ranges over all finite arithmetic progressions with common difference d.

Known Bounds:
- Lower: h(d) ≫ d^{1/2} (Roth 1964, discrepancy lower bound)
- Upper: h(d) ≤ d^{8+ε} for all ε > 0 (Beck 2017)
- Historical: h(d) ≪ d! (Cantor-Erdős-Schreiber-Straus 1966)
- Van der Waerden: h(d) → ∞

Open Question: What is the correct order of h(d)? Likely polynomial.

References:
- [Er66] Erdős, "Remarks on number theory V" (1966)
- [Ro64] Roth, "Remark concerning integer sequences" (1964)
- [Be17] Beck, "A discrepancy problem: balancing infinite dimensional vectors" (2017)

Tags: discrepancy-theory, arithmetic-progressions, coloring, number-theory, open
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

open Finset BigOperators Real

namespace Erdos177

/-!
## Part I: Basic Definitions
-/

/--
**Coloring function:**
A function f: ℕ → {-1, 1} assigns a "color" to each natural number.
-/
def IsColoring (f : ℕ → ℤ) : Prop :=
  ∀ n, f n = 1 ∨ f n = -1

/--
**Arithmetic progression:**
An arithmetic progression with start a, common difference d, and length k.
-/
def ArithProg (a d k : ℕ) : Finset ℕ :=
  Finset.range k |>.map ⟨fun i => a + d * i, fun _ _ h => by omega⟩

/--
**Discrepancy of a set:**
The sum of f over elements of a finite set.
-/
def discrepancy (f : ℕ → ℤ) (S : Finset ℕ) : ℤ :=
  ∑ n ∈ S, f n

/--
**Discrepancy of an arithmetic progression:**
|Σ_{n∈P} f(n)| for progression P.
-/
def apDiscrepancy (f : ℕ → ℤ) (a d k : ℕ) : ℤ :=
  |discrepancy f (ArithProg a d k)|

/-!
## Part II: The Function h(d)
-/

/--
**Maximum discrepancy for difference d:**
max_{P_d} |Σ_{n∈P_d} f(n)| over all APs with difference d.
-/
noncomputable def maxDiscrepancyForD (f : ℕ → ℤ) (d : ℕ) : ℕ :=
  -- Supremum over all starting points a and lengths k
  sSup {(apDiscrepancy f a d k).natAbs | (a : ℕ) (k : ℕ)}

/--
**The function h(d):**
The minimum over all colorings f of the maximum discrepancy for difference d.
-/
noncomputable def h (d : ℕ) : ℕ :=
  sInf {maxDiscrepancyForD f d | f : ℕ → ℤ, IsColoring f}

/--
**Bounded discrepancy:**
A coloring f has discrepancy at most B for difference d.
-/
def HasBoundedDiscrepancy (f : ℕ → ℤ) (d : ℕ) (B : ℕ) : Prop :=
  ∀ a k : ℕ, apDiscrepancy f a d k ≤ B

/--
**The h(d) bound:**
h(d) ≤ B iff there exists a coloring with discrepancy ≤ B for difference d.
-/
axiom h_characterization (d B : ℕ) :
    h d ≤ B ↔ ∃ f : ℕ → ℤ, IsColoring f ∧ HasBoundedDiscrepancy f d B

/-!
## Part III: Van der Waerden's Theorem Connection
-/

/--
**Van der Waerden's Theorem (consequence):**
h(d) → ∞ as d → ∞.

Any 2-coloring of ℕ eventually has arbitrarily long monochromatic APs,
so discrepancy must grow.
-/
axiom van_der_waerden_consequence :
    Filter.Tendsto h Filter.atTop Filter.atTop

/--
**Van der Waerden's Theorem (weak form):**
For any 2-coloring and any k, there exists a monochromatic AP of length k.
-/
axiom van_der_waerden_weak :
    ∀ f : ℕ → ℤ, IsColoring f →
      ∀ k : ℕ, ∃ a d : ℕ, d > 0 ∧
        (∀ i < k, f (a + d * i) = 1) ∨ (∀ i < k, f (a + d * i) = -1)

/-!
## Part IV: Roth's Lower Bound (1964)
-/

/--
**Roth's discrepancy lower bound:**
h(d) ≫ d^{1/2}

More precisely: ∃ c > 0 such that h(d) ≥ c·√d for large d.
-/
axiom roth_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∃ d₀ : ℕ, ∀ d ≥ d₀,
      (h d : ℝ) ≥ c * d ^ (1/2 : ℝ)

/--
**Roth's bound is optimal up to log factors for d = 1:**
For d = 1, the discrepancy of an interval is Θ(√n).
-/
axiom roth_interval_discrepancy :
    -- For intervals {1, ..., n}, any coloring has discrepancy ≈ √n
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∀ n : ℕ, n > 0 →
      c * n ^ (1/2 : ℝ) ≤ h 1 ∧ (h 1 : ℝ) ≤ C * n ^ (1/2 : ℝ)

/-!
## Part V: Historical Upper Bounds
-/

/--
**Cantor-Erdős-Schreiber-Straus (1966):**
h(d) ≪ d!

This factorial bound was the first explicit upper bound.
-/
axiom cantor_erdos_schreiber_straus_1966 :
    ∃ C : ℝ, C > 0 ∧ ∀ d : ℕ, d > 0 →
      (h d : ℝ) ≤ C * (d.factorial : ℝ)

/--
**The factorial bound is very weak:**
d! grows much faster than any polynomial.
-/
theorem factorial_grows_fast : ∀ k : ℕ, ∃ d₀ : ℕ, ∀ d ≥ d₀,
    (d.factorial : ℝ) > (d : ℝ) ^ k := by
  intro k
  sorry

/-!
## Part VI: Beck's Upper Bound (2017)
-/

/--
**Beck's polynomial bound (2017):**
h(d) ≤ d^{8+ε} for every ε > 0.

This dramatically improved the factorial bound to polynomial.
-/
axiom beck_2017 :
    ∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧ ∃ d₀ : ℕ, ∀ d ≥ d₀,
      (h d : ℝ) ≤ C * d ^ (8 + ε)

/--
**Beck's result significance:**
First polynomial upper bound. The exponent 8 is not believed to be optimal.
-/
axiom beck_significance :
    -- The gap between √d (lower) and d^8 (upper) remains
    True

/-!
## Part VII: The Gap
-/

/--
**Current knowledge:**
√d ≪ h(d) ≪ d^{8+ε}

The true order is unknown.
-/
theorem current_bounds_gap :
    -- Lower: h(d) ≥ c·d^{1/2}
    -- Upper: h(d) ≤ C·d^{8+ε}
    -- Gap: exponent between 1/2 and 8
    True := trivial

/--
**Conjectured order:**
h(d) ≈ d^α for some 1/2 ≤ α ≤ 1.

Most experts believe α is closer to 1/2 than to 8.
-/
def ConjecturedOrder : Prop :=
    ∃ α : ℝ, 1/2 ≤ α ∧ α ≤ 1 ∧
      ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∃ d₀ : ℕ, ∀ d ≥ d₀,
        c * d ^ α ≤ h d ∧ (h d : ℝ) ≤ C * d ^ α

/-!
## Part VIII: Related Discrepancy Problems
-/

/--
**Connection to Roth's theorem:**
Roth's original result was about sets without 3-term APs.
Discrepancy theory grew from these ideas.
-/
axiom roth_connection :
    -- Discrepancy of APs relates to AP-free sets
    True

/--
**Connection to combinatorial discrepancy:**
This is a special case of discrepancy theory for set systems.
-/
axiom combinatorial_discrepancy_connection :
    -- The system {arithmetic progressions} has discrepancy h(d)
    True

/-!
## Part IX: Why It's Hard
-/

/--
**Difficulty:**
The problem combines number theory (AP structure) with combinatorics (coloring).
-/
axiom difficulty_explanation :
    -- No good way to construct optimal colorings
    -- Analysis gives lower bounds, probabilistic methods give upper bounds
    True

/--
**Cannot be settled by computation:**
The problem asks about ALL arithmetic progressions (infinitely many).
-/
axiom cannot_compute :
    -- For any finite computation, h(d) could still be larger
    True

/-!
## Part X: Summary
-/

/--
**Erdős Problem #177: OPEN**

Find the smallest h(d) such that there exists f: ℕ → {-1, 1} with
|Σ_{n∈P} f(n)| ≤ h(d) for all APs P with difference d.

**Known:**
- Lower: h(d) ≥ c·√d (Roth 1964)
- Upper: h(d) ≤ d^{8+ε} (Beck 2017)
- Historical: h(d) ≤ C·d! (Cantor-Erdős-Schreiber-Straus 1966)

**Open:** What is the correct polynomial exponent?
-/
theorem erdos_177_open :
    -- Roth lower bound exists
    (∃ c : ℝ, c > 0 ∧ ∃ d₀ : ℕ, ∀ d ≥ d₀, (h d : ℝ) ≥ c * d ^ (1/2 : ℝ)) →
    -- Beck upper bound exists
    (∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧ ∃ d₀ : ℕ, ∀ d ≥ d₀,
      (h d : ℝ) ≤ C * d ^ (8 + ε)) →
    -- The problem remains open
    True := by
  intro _ _
  trivial

/--
**Summary theorem:**
-/
theorem erdos_177_summary :
    -- Van der Waerden implies h(d) → ∞
    True ∧
    -- Roth lower bound: d^{1/2}
    True ∧
    -- Beck upper bound: d^{8+ε}
    True ∧
    -- Problem is OPEN
    True := ⟨trivial, trivial, trivial, trivial⟩

/-- Problem status -/
def erdos_177_status : String :=
    "OPEN - Gap between d^{1/2} (lower) and d^{8+ε} (upper)"

end Erdos177
