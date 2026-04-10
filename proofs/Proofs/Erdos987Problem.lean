/-
Erdős Problem #987: Exponential Sums and Sequence Discrepancy

Source: https://erdosproblems.com/987
Status: SOLVED (Alexeev-Putterman-Sawhney-Sellke-Valiant 2026,
arXiv:2604.06609)

Statement:
Let x₁, x₂, ... ∈ (0,1) be an infinite sequence and define:
  Aₖ = sup_{N≥1} |∑_{j<N} e(kxⱼ)|
where e(x) = e^{2πix}.

Questions:
1. Is limsup_{k→∞} Aₖ = ∞? YES (Erdős 1964)
2. Is it possible for Aₖ = o(k)? YES (APSSV 2026)

Known Results:
- Erdős (1965): Aₖ ≫ log k infinitely often
- Clunie (1967): Aₖ ≫ √k infinitely often; also ∃ sequences with Aₖ ≤ k ∀k
- Tao: Independently proved Aₖ ≫ √k infinitely often
- Liu (1969): With finitely many distinct points, Aₖ ≫ k^{1-ε} infinitely often
- APSSV (2026): ∃ sequence with Aₖ ≪ √(k log k), resolving the o(k) question

The construction is a randomized binary scrambling of the van der Corput
sequence. Combined with Clunie's √k lower bound, the optimal growth rate
is pinpointed up to a √(log k) factor.

Reference: https://erdosproblems.com/987
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential

open Complex Real Filter

namespace Erdos987

/- ## Part I: Basic Definitions

Exponential sums and the Aₖ function.
-/

/--
**The Exponential Function e(x):**
e(x) = e^{2πix} = cos(2πx) + i·sin(2πx)

This maps reals to the unit circle in the complex plane.
For x ∈ [0,1], e(x) traces the unit circle once.
-/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * x * Complex.I)

/--
**Partial Exponential Sum:**
Sₙ(k) = ∑_{j=1}^n e(k·xⱼ)

This is a sum of unit vectors in the complex plane.
-/
noncomputable def partialSum (x : ℕ → ℝ) (k n : ℕ) : ℂ :=
  ∑ j in Finset.range n, e (k * x (j + 1))

/--
**The Aₖ Function:**
Aₖ = limsup_{n→∞} |Sₙ(k)|

This measures how large the partial sums can get for the k-th harmonic.
-/
noncomputable def A (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  Filter.limsup (fun n => Complex.abs (partialSum x k n)) Filter.atTop

/- ## Part II: Erdős's Basic Results

Early observations about exponential sums.
-/

/--
**Sequence in Unit Interval:**
All sequence elements are in (0,1).
-/
def InUnitInterval (x : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, n ≥ 1 → 0 < x n ∧ x n < 1

/--
**Erdős (1964): Supremum is Unbounded**
For any sequence, the supremum of partial sums over n is unbounded as k → ∞.

"Easy to see": limsup_{k→∞} (sup_n |∑_{j≤n} e(kxⱼ)|) = ∞
-/

/--
**Erdős (1965): Logarithmic Lower Bound**
Aₖ ≫ log k for infinitely many k.

"Very easy" proof that the limsup of partial sums grows at least logarithmically.
-/

/- ## Part III: Clunie's Results (1967)

Stronger bounds and upper bound constructions.
-/

/--
**Clunie's Lower Bound (1967):**
Aₖ ≫ √k for infinitely many k.

This is a substantial improvement over Erdős's log k bound.
-/
axiom clunie_sqrt_bound (x : ℕ → ℝ) (hx : InUnitInterval x) :
    ∃ C : ℝ, C > 0 ∧ ∀ M : ℕ, ∃ k ≥ M, A x k ≥ C * Real.sqrt k

/--
**Clunie's Upper Bound (1967):**
There exist sequences with Aₖ ≤ k for all k.

This shows that linear growth is achievable (no explosion).
-/
axiom clunie_upper_construction :
    ∃ x : ℕ → ℝ, InUnitInterval x ∧ ∀ k : ℕ, A x k ≤ k

/--
**Tao's Independent Proof:**
Tao independently found that Aₖ ≫ √k infinitely often.
-/

/- ## Part IV: Liu's Results (1969)

Finite distinct points case.
-/

/--
**Finite Distinct Points:**
The sequence takes only finitely many distinct values.
-/
def FinitelyManyDistinct (x : ℕ → ℝ) : Prop :=
  ∃ S : Finset ℝ, ∀ n : ℕ, n ≥ 1 → x n ∈ S

/--
**Liu's Theorem (1969):**
If there are finitely many distinct points, then for any ε > 0,
Aₖ ≫ k^{1-ε} infinitely often.
-/

/--
**Clunie's Observation:**
Under the finite distinct points assumption, Aₖ = ∞ infinitely often!
(Noted in MathSciNet review of Liu's paper)
-/

/- ## Part V: The Open Question

Is Aₖ = o(k) possible?
-/

/--
**Sublinear Growth Definition:**
Aₖ = o(k) means Aₖ/k → 0 as k → ∞.
-/
def SublinearGrowth (x : ℕ → ℝ) : Prop :=
  Filter.Tendsto (fun k => A x k / k) Filter.atTop (nhds 0)

/--
**The Main Question (RESOLVED):**
Is there a sequence x with InUnitInterval x such that Aₖ = o(k)?

This was asked by Erdős (1965) and repeated by Hayman (1974).
RESOLVED YES by Alexeev-Putterman-Sawhney-Sellke-Valiant (2026):
there exists a sequence with Aₖ ≪ √(k log k), which is o(k).
-/
def openQuestion : Prop :=
  ∃ x : ℕ → ℝ, InUnitInterval x ∧ SublinearGrowth x

/-- SOLVED: The open question is TRUE.
    Alexeev-Putterman-Sawhney-Sellke-Valiant (2026, arXiv:2604.06609)
    constructed a randomized sequence achieving Aₖ ≪ √(k log k).
    In fact, a stronger bound holds: sup_N |S_N(k)| ≪ √(k log k). -/
axiom erdos_987_resolved : openQuestion

/--
**What We Know:**
- Lower: Aₖ ≫ √k infinitely often (so NOT Aₖ = o(√k))
- Upper: There exist sequences with Aₖ ≤ k (so Aₖ = O(k) is possible)
- Gap: Can we achieve o(k) but not O(√k)?
-/
theorem known_bounds :
    -- Lower bound: A_k >= C√k infinitely often
    (∀ x, InUnitInterval x → ∃ C > 0, ∀ M, ∃ k ≥ M, A x k ≥ C * Real.sqrt k) ∧
    -- Upper bound: Some sequences have A_k ≤ k
    (∃ x, InUnitInterval x ∧ ∀ k, A x k ≤ k) := by
  exact ⟨clunie_sqrt_bound, clunie_upper_construction⟩

/- ## Part VI: Physical Interpretation

Understanding the problem geometrically.
-/

/--
**Weyl's Equidistribution:**
For equidistributed sequences (like nα mod 1 for irrational α),
the sums have cancellation.

e(kxⱼ) = e(kjα) = e(jkα)

Weyl sums: |∑_{j=1}^n e(jθ)| ≤ csc(πθ/2) for θ ∉ ℤ.
-/

/- ## Part VII: Connection to Discrepancy Theory

The relationship between exponential sums and uniform distribution.
-/

/--
**Discrepancy:**
A measure of how far a sequence deviates from uniform distribution.
-/
def discrepancy (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ⨆ (a b : ℝ) (hab : 0 ≤ a ∧ a < b ∧ b ≤ 1),
    |((Finset.range n).filter (fun j => a ≤ x (j+1) ∧ x (j+1) < b)).card / n - (b - a)|

/--
**Erdős-Turán Inequality:**
Exponential sums control discrepancy.
-/

/- ## Part VIII: Main Results

Summary of Erdős Problem #987.
-/

/-- A_k grows unboundedly for any sequence in (0,1).
    Follows from clunie_sqrt_bound since √k → ∞. -/
axiom erdos_987_unbounded (x : ℕ → ℝ) (hx : InUnitInterval x) :
    ∀ M : ℝ, ∃ k : ℕ, A x k > M

theorem erdos_987 :
    -- A_k grows unboundedly
    (∀ x, InUnitInterval x → ∀ M : ℝ, ∃ k : ℕ, A x k > M) ∧
    -- A_k ≥ C√k infinitely often
    (∀ x, InUnitInterval x → ∃ C > 0, ∀ N, ∃ k ≥ N, A x k ≥ C * Real.sqrt k) ∧
    -- Upper bound: some sequences have A_k ≤ k
    (∃ x, InUnitInterval x ∧ ∀ k, A x k ≤ k) :=
  ⟨erdos_987_unbounded, clunie_sqrt_bound, clunie_upper_construction⟩

end Erdos987
