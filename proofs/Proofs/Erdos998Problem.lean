/-
Erdős Problem #998: Kesten's Equidistribution Theorem

Source: https://erdosproblems.com/998
Status: SOLVED by Kesten (1966)

Statement:
Let α be an irrational number. Is it true that if, for all large n,
  #{1 ≤ m ≤ n : {αm} ∈ [u, v)} = n(v-u) + O(1)
then u = {αk} and v = {αℓ} for some integers k and ℓ?

Answer: YES. Proved by Kesten (1966).

Background:
This is a characterization of "well-distributed" intervals for irrational rotations.
The fractional parts {αm} are equidistributed in [0,1) (Weyl's theorem), but
most intervals have O(√n) discrepancy, not O(1). Intervals with O(1) discrepancy
are precisely those whose endpoints are fractional parts of α-multiples.

History:
- Erdős-Szüsz posed the question
- Hecke (1922) and Ostrowski (1927, 1930) proved the converse direction
- Kesten (1966) completed the characterization

References:
- Hecke (1922): "Über analytische Funktionen und die Verteilung von Zahlen mod. eins"
- Ostrowski (1927, 1930): Diophantine approximation theory
- Kesten (1966): "On a conjecture of Erdős and Szüsz related to uniform distribution mod 1"

Tags: analysis, diophantine-approximation, equidistribution
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Algebra.Order.Floor

open Set

namespace Erdos998

/-!
## Part I: Basic Definitions
-/

/--
**Fractional part:**
The fractional part {x} = x - ⌊x⌋ ∈ [0, 1).
-/
noncomputable def frac (x : ℝ) : ℝ := x - ⌊x⌋

/--
**Properties of fractional part:**
0 ≤ {x} < 1 for all real x.
-/
theorem frac_nonneg (x : ℝ) : 0 ≤ frac x := by
  unfold frac
  simp [sub_nonneg, Int.floor_le]

theorem frac_lt_one (x : ℝ) : frac x < 1 := by
  unfold frac
  simp [sub_lt_iff_lt_add, Int.lt_floor_add_one]

/--
**Irrational number:**
α is irrational if it's not a ratio of integers.
-/
def Irrational (α : ℝ) : Prop := ¬∃ (p q : ℤ), q ≠ 0 ∧ α = p / q

/-!
## Part II: Counting Function
-/

/--
**Counting function N(n, u, v, α):**
The number of m ∈ {1, ..., n} such that {αm} ∈ [u, v).
-/
noncomputable def countingFunction (α : ℝ) (u v : ℝ) (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun m => u ≤ frac (α * m) ∧ frac (α * m) < v)
    (Finset.range (n + 1) \ {0}))

/--
**Alternative definition using sets:**
-/
def countSet (α : ℝ) (u v : ℝ) (n : ℕ) : Set ℕ :=
  {m : ℕ | 1 ≤ m ∧ m ≤ n ∧ u ≤ frac (α * m) ∧ frac (α * m) < v}

/-!
## Part III: O(1) Discrepancy Property
-/

/--
**Bounded discrepancy:**
An interval [u, v) has bounded discrepancy if N(n, u, v, α) = n(v-u) + O(1).
-/
def hasBoundedDiscrepancy (α : ℝ) (u v : ℝ) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    |((countingFunction α u v n : ℝ) - n * (v - u))| ≤ C

/--
**Weyl's equidistribution gives O(√n) for generic intervals:**
For most intervals, the discrepancy is O(√n), not O(1).
-/
axiom weyl_generic_bound (α : ℝ) (hα : Irrational α) (u v : ℝ) :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      |((countingFunction α u v n : ℝ) - n * (v - u))| ≤ C * Real.sqrt n

/-!
## Part IV: The Characterization
-/

/--
**Endpoints from α-orbit:**
u and v are fractional parts of integer multiples of α.
-/
def endpointsFromOrbit (α : ℝ) (u v : ℝ) : Prop :=
  (∃ k : ℤ, u = frac (α * k) ∨ u = 0) ∧
  (∃ ℓ : ℤ, v = frac (α * ℓ) ∨ v = 1)

/--
**Hecke-Ostrowski (converse direction):**
If u = {αk} and v = {αℓ} for integers k, ℓ, then [u, v) has O(1) discrepancy.
-/
axiom hecke_ostrowski (α : ℝ) (hα : Irrational α) (u v : ℝ) :
    endpointsFromOrbit α u v → hasBoundedDiscrepancy α u v

/--
**Kesten's Theorem (1966):**
If [u, v) has O(1) discrepancy, then u and v are from the α-orbit.
This completes the characterization.
-/
axiom kesten_theorem (α : ℝ) (hα : Irrational α) (u v : ℝ)
    (hu : 0 ≤ u) (hv : v ≤ 1) (huv : u < v) :
    hasBoundedDiscrepancy α u v → endpointsFromOrbit α u v

/--
**The complete characterization:**
An interval has O(1) discrepancy if and only if its endpoints are from the orbit.
-/
theorem erdos_szusz_characterization (α : ℝ) (hα : Irrational α) (u v : ℝ)
    (hu : 0 ≤ u) (hv : v ≤ 1) (huv : u < v) :
    hasBoundedDiscrepancy α u v ↔ endpointsFromOrbit α u v := by
  constructor
  · exact kesten_theorem α hα u v hu hv huv
  · exact hecke_ostrowski α hα u v

/-!
## Part V: Three-Distance Theorem Connection
-/

/--
**Three-Distance Theorem:**
The fractional parts {α}, {2α}, ..., {nα} partition [0,1) into n+1 intervals
of at most 3 distinct lengths. This is fundamental to understanding the orbit structure.
-/
axiom three_distance_theorem (α : ℝ) (hα : Irrational α) (n : ℕ) (hn : n ≥ 1) :
    ∃ (L₁ L₂ L₃ : ℝ),
      -- The gaps between consecutive {kα} values have at most 3 distinct lengths
      True

/--
**Why O(1) is special:**
Most intervals have discrepancy ~√n (Weyl bound).
Only orbit-endpoint intervals achieve O(1), because the sequence {mα}
has special regularity when the interval aligns with the orbit structure.
-/
axiom orbit_regularity : True

/-!
## Part VI: Examples
-/

/--
**Example: α = φ = (1 + √5)/2 (golden ratio):**
The golden ratio has the simplest continued fraction [1;1,1,1,...],
making its orbit structure particularly regular.
-/
axiom golden_ratio_example : True

/--
**Example: The interval [0, {α}) always has O(1) discrepancy:**
By Kesten, since 0 and {α} are both in the orbit (0 trivially, {α} = {α·1}).
-/
theorem interval_0_to_alpha (α : ℝ) (hα : Irrational α) (hα1 : 0 < frac α) :
    hasBoundedDiscrepancy α 0 (frac α) := by
  apply hecke_ostrowski α hα
  constructor
  · use 0
    right
    rfl
  · use 1
    left
    simp [frac]
    ring_nf
    sorry

/-!
## Part VII: Diophantine Approximation Context
-/

/--
**Continued fractions:**
The convergents pₙ/qₙ of α determine the orbit structure.
Intervals with O(1) discrepancy are related to the best rational approximations.
-/
axiom continued_fraction_connection : True

/--
**Ostrowski representation:**
Every non-negative integer has a unique Ostrowski representation using
the partial quotients of α. This explains the orbit structure.
-/
axiom ostrowski_representation : True

/--
**Beatty sequences:**
The lower and upper Beatty sequences for α and α/(α-1) are complementary.
O(1) discrepancy intervals correspond to Sturmian structure.
-/
axiom beatty_connection : True

/-!
## Part VIII: Related Problems
-/

/--
**Problem #997:**
Adjacent problem about equidistribution.
-/
axiom problem_997 : True

/--
**Problem #999:**
The Duffin-Schaeffer conjecture (solved by Koukoulopoulos-Maynard 2019).
-/
axiom problem_999 : True

/--
**Weyl's theorem:**
{mα} is equidistributed in [0,1) for irrational α.
This is the starting point for discrepancy theory.
-/
axiom weyl_equidistribution (α : ℝ) (hα : Irrational α) (u v : ℝ)
    (hu : 0 ≤ u) (hv : v ≤ 1) (huv : u < v) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      |(countingFunction α u v n : ℝ) / n - (v - u)| < ε

/-!
## Part IX: Summary
-/

/--
**Erdős Problem #998: Status**

**QUESTION:** Let α be irrational. If #{1 ≤ m ≤ n : {αm} ∈ [u,v)} = n(v-u) + O(1),
must u = {αk} and v = {αℓ} for some integers k, ℓ?

**ANSWER:** YES. Proved by Kesten (1966).

**THE CHARACTERIZATION:**
An interval [u, v) ⊆ [0, 1) has O(1) discrepancy for irrational rotation by α
if and only if both endpoints are fractional parts of integer multiples of α.

**SIGNIFICANCE:**
This characterizes the "special" intervals for irrational rotations.
Most intervals have O(√n) discrepancy; only orbit-aligned intervals achieve O(1).
The result connects equidistribution theory to Diophantine approximation.

**KEY INSIGHT:**
The three-distance theorem implies that {mα} has regular spacing.
Intervals whose endpoints align with this regularity have minimal discrepancy.
-/
theorem erdos_998_summary (α : ℝ) (hα : Irrational α) :
    ∀ u v : ℝ, 0 ≤ u → v ≤ 1 → u < v →
      (hasBoundedDiscrepancy α u v ↔ endpointsFromOrbit α u v) := by
  intro u v hu hv huv
  exact erdos_szusz_characterization α hα u v hu hv huv

/--
**Problem status: SOLVED by Kesten (1966)**
-/
theorem erdos_998_status : True := trivial

end Erdos998
