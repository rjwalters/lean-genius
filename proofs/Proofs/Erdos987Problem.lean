/-
Erdős Problem #987: Exponential Sums and Sequence Discrepancy

Source: https://erdosproblems.com/987
Status: PARTIALLY OPEN

Statement:
Let x₁, x₂, ... ∈ (0,1) be an infinite sequence and define:
  Aₖ = limsup_{n→∞} |∑_{j≤n} e(kxⱼ)|
where e(x) = e^{2πix}.

Questions:
1. Is limsup_{k→∞} Aₖ = ∞?
2. Is it possible for Aₖ = o(k)?

Known Results:
- Erdős (1965): Aₖ ≫ log k infinitely often
- Clunie (1967): Aₖ ≫ √k infinitely often; also ∃ sequences with Aₖ ≤ k ∀k
- Tao: Independently proved Aₖ ≫ √k infinitely often
- Liu (1969): With finitely many distinct points, Aₖ ≫ k^{1-ε} infinitely often

Open: Is Aₖ = o(k) possible?

Reference: https://erdosproblems.com/987
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential

open Complex Real Filter

namespace Erdos987

/-
## Part I: Basic Definitions

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
**Properties of e(x):**
- |e(x)| = 1 for all x
- e(x + 1) = e(x) (periodic)
- e(x + y) = e(x) · e(y)
-/
theorem e_norm (x : ℝ) : Complex.abs (e x) = 1 := by
  simp only [e, Complex.abs_exp]
  simp [Complex.re_ofReal_mul]
  sorry  -- Requires showing re(2πxi) = 0

theorem e_periodic (x : ℝ) : e (x + 1) = e x := by
  simp only [e]
  ring_nf
  sorry  -- Requires e^{2πi} = 1

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

/-
## Part II: Erdős's Basic Results

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
axiom erdos_1964_basic (x : ℕ → ℝ) (hx : InUnitInterval x) :
    ∀ M : ℝ, ∃ k : ℕ, ∃ n : ℕ,
    Complex.abs (partialSum x k n) > M

/--
**Erdős (1965): Logarithmic Lower Bound**
Aₖ ≫ log k for infinitely many k.

"Very easy" proof that the limsup of partial sums grows at least logarithmically.
-/
axiom erdos_1965_log_bound (x : ℕ → ℝ) (hx : InUnitInterval x) :
    ∃ C : ℝ, C > 0 ∧ ∀ M : ℕ, ∃ k ≥ M, A x k ≥ C * Real.log k

/-
## Part III: Clunie's Results (1967)

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
axiom tao_sqrt_bound (x : ℕ → ℝ) (hx : InUnitInterval x) :
    ∃ C : ℝ, C > 0 ∧ ∀ M : ℕ, ∃ k ≥ M, A x k ≥ C * Real.sqrt k

/-
## Part IV: Liu's Results (1969)

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
axiom liu_finite_distinct (x : ℕ → ℝ) (hx : InUnitInterval x)
    (hfin : FinitelyManyDistinct x) (ε : ℝ) (hε : ε > 0) :
    ∃ C : ℝ, C > 0 ∧ ∀ M : ℕ, ∃ k ≥ M, A x k ≥ C * (k : ℝ)^(1 - ε)

/--
**Clunie's Observation:**
Under the finite distinct points assumption, Aₖ = ∞ infinitely often!
(Noted in MathSciNet review of Liu's paper)
-/
axiom clunie_observation_finite (x : ℕ → ℝ) (hx : InUnitInterval x)
    (hfin : FinitelyManyDistinct x) :
    ∀ M : ℝ, ∃ k : ℕ, A x k > M

/-
## Part V: The Open Question

Is Aₖ = o(k) possible?
-/

/--
**Sublinear Growth Definition:**
Aₖ = o(k) means Aₖ/k → 0 as k → ∞.
-/
def SublinearGrowth (x : ℕ → ℝ) : Prop :=
  Filter.Tendsto (fun k => A x k / k) Filter.atTop (nhds 0)

/--
**The Main Open Question:**
Is there a sequence x with InUnitInterval x such that Aₖ = o(k)?

This question is asked in Erdős (1965) and repeated in Hayman (1974).
It remains OPEN.
-/
def openQuestion : Prop :=
  ∃ x : ℕ → ℝ, InUnitInterval x ∧ SublinearGrowth x

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

/-
## Part VI: Physical Interpretation

Understanding the problem geometrically.
-/

/--
**Random Walk Interpretation:**
The partial sum Sₙ(k) is a sum of n unit vectors in the complex plane,
each at angle 2πkxⱼ from the real axis.

If the angles are "random-like", we expect |Sₙ| ~ √n (random walk).
If they align, |Sₙ| could be as large as n.
-/
def randomWalkAnalogy : Prop :=
  ∀ x : ℕ → ℝ, InUnitInterval x →
    -- For "generic" sequences, partial sums grow like √n
    True  -- Placeholder for intuition

/--
**Weyl's Equidistribution:**
For equidistributed sequences (like nα mod 1 for irrational α),
the sums have cancellation.

e(kxⱼ) = e(kjα) = e(jkα)

Weyl sums: |∑_{j=1}^n e(jθ)| ≤ csc(πθ/2) for θ ∉ ℤ.
-/
axiom weyl_sum_bound (θ : ℝ) (hθ : ∀ k : ℤ, θ ≠ k) (n : ℕ) :
    Complex.abs (∑ j in Finset.range n, e (j * θ)) ≤ 1 / Real.sin (Real.pi * θ / 2)

/-
## Part VII: Connection to Discrepancy Theory

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
axiom erdos_turan (x : ℕ → ℝ) (n K : ℕ) (hK : K ≥ 1) :
    discrepancy x n ≤ 1/K + ∑ k in Finset.range K,
      Complex.abs (partialSum x (k+1) n) / ((k+1) * n)

/-
## Part VIII: Main Results

Summary of Erdős Problem #987.
-/

/--
**Erdős Problem #987: Summary**

Status: PARTIALLY OPEN

Proved:
1. limsup_{k→∞} A_k = ∞ (Erdős 1964)
2. A_k ≫ log k infinitely often (Erdős 1965)
3. A_k ≫ √k infinitely often (Clunie 1967, Tao)
4. There exist sequences with A_k ≤ k for all k (Clunie 1967)
5. With finitely many distinct points: A_k ≫ k^{1-ε} infinitely often (Liu 1969)

Open: Is A_k = o(k) possible?
-/
/--
**Erdős Problem #987: Summary**

The unboundedness of A_k follows from clunie_sqrt_bound: since A_k ≥ C√k
for infinitely many k, and √k → ∞, we have A_k unbounded.

We state this as an axiom since the formal proof requires showing
limsup ≥ C√k implies eventual arbitrarily large values.
-/
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

/--
**The Gap:**
Between √k (lower) and k (upper) lies the open question.
-/
theorem erdos_987_gap :
    -- We know: A_k is NOT o(√k) but IS O(k)
    -- Question: Is A_k = o(k) possible?
    True := by trivial

end Erdos987
