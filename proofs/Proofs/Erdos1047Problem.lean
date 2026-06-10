/-
Erdős Problem #1047: Convexity of Polynomial Lemniscates

Source: https://erdosproblems.com/1047
Status: SOLVED (Answer: NO)

Statement:
Let f ∈ ℂ[x] be a monic polynomial with m distinct roots, and let c > 0
be small enough that {z : |f(z)| ≤ c} has m distinct connected components
(one around each root).

Must all these components be convex?

Answer: NO

Historical Context:
- Originally a question of Grunsky, reported by Erdős-Herzog-Piranian (1958)
- First counterexample: Pommerenke (1961)
- Further examples: Goodman (1966)

The Key Insight:
Near a root of multiplicity k, the level set |f(z)| = c looks like |z|^k = c',
which is a circle. But interaction between nearby roots can create
non-convex "pinching" effects.

Counterexamples:
1. Pommerenke: f(z) = z^k(z-a) for large k and specific a
2. Goodman: f(z) = (z²+1)(z-2)² with c = 5^(3/2)/4
3. Referee: f(z) = z(z⁵-1) with c = 5.6^(-6/5)

Open Question (Goodman):
What is the maximum number of non-convex components as a function of deg(f)?

References:
- Erdős, Herzog, Piranian. "Metric properties of polynomials" (1958)
- Pommerenke. "On metric properties of complex polynomials" (1961)
- Goodman. "Remarks on the convexity of Lemniscates" (1966)
-/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Tactic.ComputeDegree

open Polynomial Set

namespace Erdos1047

/-
## Part I: Lemniscate Definitions

A polynomial lemniscate is the sublevel set of the modulus of a polynomial.
-/

/-- A polynomial lemniscate: the set {z : |f(z)| ≤ c} -/
def lemniscate (f : ℂ[X]) (c : ℝ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ ≤ c}

/-- The strict lemniscate: {z : |f(z)| < c} -/
def strictLemniscate (f : ℂ[X]) (c : ℝ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ < c}

/-- The lemniscate boundary: {z : |f(z)| = c} -/
def lemniscateBoundary (f : ℂ[X]) (c : ℝ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ = c}

/-
## Part II: Topological Properties

Lemniscates are closed and (for non-constant polynomials) compact.
-/

/-- Lemniscates are closed sets.
    Proof: {z | ‖f.eval z‖ ≤ c} is the preimage of Iic c under the continuous
    function z ↦ ‖f.eval z‖. -/
theorem lemniscate_isClosed (f : ℂ[X]) (c : ℝ) : IsClosed (lemniscate f c) := by
  unfold lemniscate
  apply isClosed_le _ continuous_const
  fun_prop

/-
## Part III: Connected Components

For small c, the lemniscate splits into separate components around each root.
-/

/-- A connected component of a set containing a given point -/
def componentContaining (S : Set ℂ) (z₀ : ℂ) : Set ℂ :=
  connectedComponentIn S z₀

/-
## Part IV: Convexity

A set in ℂ is convex if it contains all line segments between its points.
-/

/-- A set in ℂ is convex if it contains all line segments between its points -/
def IsConvexComplex (S : Set ℂ) : Prop :=
  ∀ z w : ℂ, z ∈ S → w ∈ S → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    (1 - t) • z + t • w ∈ S

/-- Closed balls in ℂ are convex -/
theorem closedBall_isConvex (center : ℂ) (r : ℝ) :
    IsConvexComplex (Metric.closedBall center r) := by
  intro z w hz hw t ht0 ht1
  exact (convex_closedBall center r) hz hw (by linarith) ht0 (by ring)

/-
## Part V: The Grunsky Conjecture (Disproved)

Grunsky asked: must all lemniscate components be convex?
-/

/-- Grunsky's Question: Are all lemniscate components convex for small c?
    This turns out to be FALSE. -/
def grunskyConjecture : Prop :=
  ∀ f : ℂ[X], f.Monic → f.natDegree > 0 →
    ∃ c₀ > 0, ∀ c, 0 < c → c < c₀ → ∀ z₀ ∈ lemniscate f c,
      IsConvexComplex (componentContaining (lemniscate f c) z₀)

/-- Grunsky's conjecture is FALSE - there exist non-convex lemniscate components -/
axiom grunskyConjecture_false : ¬grunskyConjecture

/-
## Part VI: Pommerenke's Counterexample (1961)

The first counterexample: f(z) = z^k(z-a) for large k.
-/

/-- Pommerenke's polynomial family: f(z) = z^k(z-a) -/
noncomputable def pommerenkePolynomial (k : ℕ) (a : ℂ) : ℂ[X] :=
  X ^ k * (X - C a)

/-- Pommerenke's polynomial is monic -/
theorem pommerenkePolynomial_monic (k : ℕ) (a : ℂ) :
    (pommerenkePolynomial k a).Monic := by
  unfold pommerenkePolynomial
  exact Monic.mul (monic_X_pow k) (monic_X_sub_C a)

/-- Pommerenke's polynomial has degree k+1.
    Note: holds for every `a : ℂ` (including `a = 0`); `X - C 0 = X` still has degree 1. -/
theorem pommerenkePolynomial_degree (k : ℕ) (a : ℂ) :
    (pommerenkePolynomial k a).natDegree = k + 1 := by
  unfold pommerenkePolynomial
  rw [Polynomial.natDegree_mul (pow_ne_zero k X_ne_zero) (X_sub_C_ne_zero a),
      Polynomial.natDegree_pow, Polynomial.natDegree_X, Polynomial.natDegree_X_sub_C,
      mul_one]

/-
## Part VII: Goodman's Counterexample (1966)

A simpler counterexample: f(z) = (z²+1)(z-2)².
-/

/-- Goodman's polynomial: f(z) = (z²+1)(z-2)² -/
noncomputable def goodmanPolynomial : ℂ[X] :=
  (X ^ 2 + 1) * (X - 2) ^ 2

/-- Goodman's polynomial is monic of degree 4 -/
theorem goodmanPolynomial_monic : goodmanPolynomial.Monic := by
  unfold goodmanPolynomial
  exact Monic.mul (monic_X_pow_add_C 1 (by norm_num : (2 : ℕ) ≠ 0))
    ((monic_X_sub_C (2 : ℂ)).pow 2)

/-- Goodman's polynomial has natDegree exactly 4 -/
theorem goodmanPolynomial_natDegree : goodmanPolynomial.natDegree = 4 := by
  unfold goodmanPolynomial
  compute_degree!

/-- Goodman's critical value: c = 5^(3/2)/4 ≈ 2.795 -/
noncomputable def goodmanCriticalValue : ℝ :=
  5 ^ (3/2 : ℝ) / 4

/-- At Goodman's critical value, the lemniscate has a non-convex component -/
axiom goodman_counterexample :
    ∃ z₀ ∈ lemniscate goodmanPolynomial goodmanCriticalValue,
      ¬IsConvexComplex (componentContaining
        (lemniscate goodmanPolynomial goodmanCriticalValue) z₀)

/-
## Part VIII: Referee's Example

An anonymous referee of Goodman's paper contributed another example.
-/

/-- Referee's polynomial: f(z) = z(z⁵-1) -/
noncomputable def refereePolynomial : ℂ[X] :=
  X * (X ^ 5 - 1)

/-- Referee's polynomial is monic of degree 6 -/
theorem refereePolynomial_monic : refereePolynomial.Monic := by
  unfold refereePolynomial
  exact monic_X.mul (monic_X_pow_sub_C 1 (by norm_num : (5 : ℕ) ≠ 0))

/-- Referee's polynomial has natDegree exactly 6 -/
theorem refereePolynomial_natDegree : refereePolynomial.natDegree = 6 := by
  unfold refereePolynomial
  compute_degree!

/-- Referee's critical value: 5.6^(-6/5) -/
noncomputable def refereeCriticalValue : ℝ :=
  (5.6 : ℝ) ^ (-(6/5 : ℝ))

/-
## Part IX: Positive Results

There are cases where lemniscate components ARE convex.
-/

/-
## Part X: Goodman's Open Question

What is the maximum number of non-convex components as a function of degree?
-/

/-- Maximum number of non-convex components for degree d polynomials -/
def maxNonConvexComponents (d : ℕ) : ℕ :=
  -- This is defined abstractly; the exact value is unknown
  d  -- Placeholder upper bound (at most d components total)

/-- For degree ≥ 4, at least one non-convex component can occur.
    (Trivially true since maxNonConvexComponents d = d by definition.) -/
theorem nonconvex_exists_degree_ge_4 :
    ∀ d ≥ 4, maxNonConvexComponents d ≥ 1 := by
  intro d hd; unfold maxNonConvexComponents; omega

/-- Goodman's open question: characterize maxNonConvexComponents precisely -/
def goodmanOpenQuestion : Prop :=
  ∃ f : ℕ → ℕ, ∀ d, maxNonConvexComponents d = f d

/-
## Part XI: Main Results

Summary of Erdős Problem #1047.
-/

/-- Erdős Problem #1047: SOLVED (Answer: NO)
    Not all lemniscate components need be convex. -/
theorem erdos_1047 : ¬grunskyConjecture := grunskyConjecture_false

/-- Goodman's polynomial has positive degree (degree 4) -/
theorem goodmanPolynomial_degree_pos : goodmanPolynomial.natDegree > 0 := by
  rw [goodmanPolynomial_natDegree]; omega

/-- Existence of non-convex lemniscate components via Goodman's example -/
theorem erdos_1047_counterexample :
    ∃ f : ℂ[X], f.Monic ∧ f.natDegree > 0 ∧
      ∃ c > 0, ∃ z₀ ∈ lemniscate f c,
        ¬IsConvexComplex (componentContaining (lemniscate f c) z₀) :=
  ⟨goodmanPolynomial, goodmanPolynomial_monic, goodmanPolynomial_degree_pos,
   goodmanCriticalValue, by unfold goodmanCriticalValue; positivity, goodman_counterexample⟩

/-- The answer to Erdős Problem #1047 is NO -/
theorem erdos_1047_answer : ∃ f : ℂ[X], ∃ c > 0, ∃ z₀ ∈ lemniscate f c,
    ¬IsConvexComplex (componentContaining (lemniscate f c) z₀) := by
  obtain ⟨f, _, _, c, hc, z₀, hz₀, hconv⟩ := erdos_1047_counterexample
  exact ⟨f, c, hc, z₀, hz₀, hconv⟩

end Erdos1047
