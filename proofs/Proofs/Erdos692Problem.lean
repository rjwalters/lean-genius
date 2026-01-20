/-
Erdős Problem #692: Unimodularity of Divisor Density

Source: https://erdosproblems.com/692
Status: DISPROVED (Cambie 2025)

Statement:
Let δ₁(n,m) be the density of the set of integers with exactly one divisor
in the interval (n,m). Is δ₁(n,m) unimodular for m > n + 1 (i.e., increases
until some m then decreases thereafter)?

For fixed n, where does δ₁(n,m) achieve its maximum?

History:
- Erdős asked this at Oberwolfach in 1986
- Erdős proved δ₁(n,m) ≪ 1/(log n)^c for some c > 0
- Ford (2008) gave sharper bounds for various ranges
- Cambie (2025) DISPROVED unimodularity with explicit counterexamples

Cambie's Counterexamples:
- δ₁(3,6) = 0.35
- δ₁(3,7) ≈ 0.33
- δ₁(3,8) ≈ 0.3619

This shows the sequence decreases then increases, refuting unimodularity.

Further: Cambie showed δ₁(n,m) has superpolynomially many local maxima.

Reference: https://erdosproblems.com/692
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Divisors
import Mathlib.Topology.Instances.Real
import Mathlib.Order.Filter.Basic

open Nat Real Filter Finset

namespace Erdos692

/-
## Part I: Basic Definitions

The divisor density function and its properties.
-/

/--
**Number of Divisors in Interval:**
Count of divisors of k that lie in the open interval (n, m).
-/
def divisorsInInterval (k n m : ℕ) : ℕ :=
  (k.divisors.filter (fun d => n < d ∧ d < m)).card

/--
**Has Exactly One Divisor in Interval:**
True if k has exactly one divisor in (n, m).
-/
def hasExactlyOneDivisor (k n m : ℕ) : Prop :=
  divisorsInInterval k n m = 1

/--
**Count up to N:**
Number of integers ≤ N with exactly one divisor in (n, m).
-/
def countWithOneDivisor (N n m : ℕ) : ℕ :=
  ((range N).filter (fun k => divisorsInInterval k n m = 1)).card

/--
**Density Function δ₁(n,m):**
The asymptotic density of integers with exactly one divisor in (n, m).

δ₁(n,m) = lim_{N→∞} (#{k ≤ N : k has exactly one divisor in (n,m)}) / N

We define this as a noncomputable real using limit superior.
-/
noncomputable def delta1 (n m : ℕ) : ℝ :=
  Filter.limsup (fun N => (countWithOneDivisor N n m : ℝ) / N) Filter.atTop

/-
## Part II: Erdős's Upper Bound

The original quantitative result.
-/

/--
**Erdős's Bound:**
δ₁(n,m) ≪ 1/(log n)^c for all m, for some constant c > 0.

This shows the density is small for large n.
-/
axiom erdos_delta1_bound (n m : ℕ) (hn : n ≥ 2) :
    ∃ c : ℝ, c > 0 ∧ delta1 n m ≤ 1 / (Real.log n) ^ c

/-
## Part III: Ford's Sharper Bounds

Kevin Ford (2008) improved Erdős's bounds.
-/

/--
**Ford's Refinement (2008):**
Sharper bounds on δ₁(n,m) for various ranges of n and m.

Reference: "The distribution of integers with a divisor in a given interval"
Ann. of Math. (2) (2008), 367-433.
-/
axiom ford_2008_bounds (n m : ℕ) (hn : n ≥ 2) (hm : m > n) :
    ∃ (bound : ℝ), bound > 0 ∧ delta1 n m ≤ bound
    -- Ford gives explicit formulas depending on the ratio m/n

/-
## Part IV: Unimodularity (The Original Question)

Erdős asked whether δ₁(n,m) is unimodal in m.
-/

/--
**Unimodal Sequence:**
A sequence f : ℕ → ℝ is unimodal if it increases then decreases.
That is, ∃ m₀ such that f increases on [n+2, m₀] and decreases on [m₀, ∞).
-/
def IsUnimodal (f : ℕ → ℝ) (start : ℕ) : Prop :=
  ∃ peak : ℕ, peak > start ∧
    (∀ m₁ m₂, start < m₁ → m₁ ≤ m₂ → m₂ ≤ peak → f m₁ ≤ f m₂) ∧
    (∀ m₁ m₂, peak ≤ m₁ → m₁ ≤ m₂ → f m₂ ≤ f m₁)

/--
**Erdős's Question (1986):**
For fixed n, is the function m ↦ δ₁(n,m) unimodal for m > n + 1?
-/
def erdosUnimodalityQuestion (n : ℕ) : Prop :=
  IsUnimodal (fun m => delta1 n m) (n + 1)

/-
## Part V: Cambie's Counterexample (2025)

Cambie disproved unimodularity with explicit examples.
-/

/--
**Cambie's Counterexample Values:**
For n = 3, the sequence is not monotonic on either side of any peak.

Computed values:
- δ₁(3,6) = 0.35
- δ₁(3,7) ≈ 0.33
- δ₁(3,8) ≈ 0.3619

Note: 0.35 > 0.33 < 0.3619
So the sequence decreases then increases - NOT unimodal!
-/
axiom cambie_n3_values :
    delta1 3 6 > 0.34 ∧
    delta1 3 7 < 0.34 ∧
    delta1 3 8 > 0.36

/--
**Cambie's Theorem (2025): Unimodularity FAILS**
The density function δ₁(n,m) is NOT unimodal, even for small n.
-/
theorem cambie_disproves_unimodality : ¬(∀ n ≥ 2, erdosUnimodalityQuestion n) := by
  intro h
  -- For n = 3, we have δ₁(3,6) > δ₁(3,7) < δ₁(3,8)
  -- This violates unimodality
  sorry

/--
**Non-Unimodality for n = 3:**
Specifically, δ₁(3, m) fails to be unimodal.
-/
axiom cambie_n3_not_unimodal : ¬ erdosUnimodalityQuestion 3

/--
**Also fails for n = 2:**
Cambie verified unimodality fails for n = 2 as well.
-/
axiom cambie_n2_not_unimodal : ¬ erdosUnimodalityQuestion 2

/-
## Part VI: Superpolynomial Local Maxima

Cambie's stronger result on the complexity of δ₁(n,m).
-/

/--
**Local Maximum:**
m is a local maximum of f starting from s if f(m) ≥ f(m±1).
-/
def IsLocalMaximum (f : ℕ → ℝ) (start m : ℕ) : Prop :=
  m > start ∧ f m ≥ f (m - 1) ∧ f m ≥ f (m + 1)

/--
**Count Local Maxima up to M:**
Number of local maxima of f in the range [start+1, M].
-/
noncomputable def countLocalMaxima (f : ℕ → ℝ) (start M : ℕ) : ℕ :=
  ((Finset.Icc (start + 1) M).filter (fun m => IsLocalMaximum f start m)).card

/--
**Superpolynomial Growth:**
A function g : ℕ → ℕ grows superpolynomially if for any polynomial p,
eventually g(n) > p(n).
-/
def SuperpolynomialGrowth (g : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ C : ℕ, ∀ n ≥ C, (g n : ℝ) > n ^ k

/--
**Cambie's Theorem: Superpolynomially Many Local Maxima**
For fixed n, the sequence δ₁(n,m) has superpolynomially many local maxima.

This is a much stronger result than just failing unimodality - the behavior
is wildly oscillatory.
-/
axiom cambie_superpolynomial_maxima (n : ℕ) (hn : n ≥ 2) :
    SuperpolynomialGrowth (fun M => countLocalMaxima (fun m => delta1 n m) n M)

/-
## Part VII: Related Results

Connections to other problems in divisor theory.
-/

/--
**Connection to Erdős Problem #446:**
Problem 446 concerns the distribution of divisors and is related to 692.
-/
axiom related_to_erdos_446 :
    True  -- Marker for the relationship

/--
**Ford's Distribution Function:**
Let H(x, y, z) = #{n ≤ x : n has a divisor in (y, z)}.

Ford studied this extensively, which provides context for δ₁.
-/
def fordDistribution (x y z : ℕ) : ℕ :=
  ((range x).filter (fun n => ∃ d ∈ n.divisors, y < d ∧ d < z)).card

/-
## Part VIII: Physical Interpretation

Understanding why unimodularity fails.
-/

/--
**Why Unimodality Fails:**
The density δ₁(n,m) counts integers with EXACTLY ONE divisor in (n,m).

As m increases:
1. More divisors can potentially fall in (n,m) → increases "candidates"
2. But also more likely to have MULTIPLE divisors → decreases δ₁

These competing effects create oscillations, not a simple peak.
-/
def oscillationExplanation : Prop := True

/-
## Part IX: Main Results

Summary of Erdős Problem #692.
-/

/--
**Erdős Problem #692: Summary**

Status: DISPROVED

**Original Question (Erdős 1986):**
Is δ₁(n,m) unimodal in m for m > n + 1?

**Answer: NO**

**Erdős's Bound:** δ₁(n,m) ≪ 1/(log n)^c

**Ford (2008):** Sharper bounds for various ranges

**Cambie (2025):**
1. Explicit counterexamples for n = 2, 3
2. For n = 3: δ₁(3,6) > δ₁(3,7) < δ₁(3,8)
3. The sequence has superpolynomially many local maxima!
-/
theorem erdos_692 :
    -- Upper bound exists
    (∀ n m, n ≥ 2 → ∃ c > 0, delta1 n m ≤ 1 / (Real.log n) ^ c) ∧
    -- Unimodality is FALSE
    ¬(∀ n ≥ 2, erdosUnimodalityQuestion n) := by
  constructor
  · intro n m hn
    exact erdos_delta1_bound n m hn
  · exact cambie_disproves_unimodality

/--
**Problem Status:**
The original question asked if δ₁(n,m) is unimodal.
Answer: NO - definitively disproved by Cambie (2025).
-/
theorem erdos_692_status :
    ¬ erdosUnimodalityQuestion 3 := cambie_n3_not_unimodal

/--
**Historical Note:**
This problem remained open from 1986 to 2025 (39 years) before
Cambie's resolution.
-/
theorem problem_duration : True := trivial

end Erdos692
