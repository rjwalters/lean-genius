/-!
# Erdős Problem 119: Maximum Modulus of Polynomials on the Unit Circle

For $n \geq 1$, let $z_1, z_2, \ldots, z_n$ be points on the unit circle and define
$$p_n(z) = \prod_{i=1}^{n} (z - z_i),$$
$$M_n = \max_{|z|=1} |p_n(z)|.$$

**Part 1 (Solved):** Is it true that $\limsup M_n = \infty$?

Wagner (1980) proved $M_n > (\log n)^c$ infinitely often for some $c > 0$.

**Part 2 (Solved):** Does there exist $c > 0$ such that $M_n > n^c$ infinitely often?

Beck (1991) proved $\max_{n \leq N} M_n > N^c$ for some $c > 0$.

**Part 3 (Open, $100):** Does there exist $c > 0$ such that $\sum_{k \leq n} M_k > n^{1+c}$
for all large $n$?

*Reference:* [erdosproblems.com/119](https://www.erdosproblems.com/119)
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

open Filter Finset

/-! ## Polynomial product and maximum modulus -/

/-- The polynomial `p_n(z) = ∏_{i < n} (z - z_i)` where each `z_i` is on the unit circle.
We use 0-indexing: `p z n` is the product of `(w - z i)` for `i` in `{0, ..., n-1}`. -/
noncomputable def unitCirclePoly (z : ℕ → ℂ) (n : ℕ) : ℂ → ℂ :=
    fun w => ∏ i ∈ range n, (w - z i)

/-- `maxModulus z n` is `M_n = sup { |p_n(w)| : |w| = 1 }`, the maximum modulus of
the polynomial on the unit circle. -/
noncomputable def maxModulus (z : ℕ → ℂ) (n : ℕ) : ℝ :=
    sSup { ‖unitCirclePoly z n w‖ | (w : ℂ) (_ : ‖w‖ = 1) }

/-! ## Part 1: limsup M_n = ∞ (Solved by Wagner 1980)

Wagner proved that there exists `c > 0` with `M_n > (log n)^c` infinitely often,
which implies `limsup M_n = ∞`.

Reference: Wagner, G., On a problem of Erdős in Diophantine approximation.
Bull. London Math. Soc. (1980), 81--88. -/

/-- Part 1: For any sequence of points on the unit circle, `limsup M_n = ∞`. -/
axiom erdos119_part1 :
    ∀ (z : ℕ → ℂ), (∀ i : ℕ, ‖z i‖ = 1) →
      atTop.limsup (fun n => (maxModulus z n : EReal)) = ⊤

/-! ## Part 2: M_n > n^c infinitely often (Solved by Beck 1991)

Beck proved that there exists `c > 0` such that `max_{n ≤ N} M_n > N^c`.
This implies that `M_n > n^c` for infinitely many `n`.

Reference: Beck, J., The modulus of polynomials with zeros on the unit circle:
A problem of Erdős. Annals of Math. (1991), 609--651. -/

/-- Part 2: For any unit circle sequence, there exists `c > 0` with `M_n > n^c`
for infinitely many `n`. -/
axiom erdos119_part2 :
    ∀ (z : ℕ → ℂ), (∀ i : ℕ, ‖z i‖ = 1) →
      ∃ (c : ℝ), c > 0 ∧ ∀ N : ℕ, ∃ n : ℕ, n ≤ N ∧ maxModulus z n > (N : ℝ) ^ c

/-! ## Part 3: Partial sums grow like n^{1+c} (Open, $100 prize)

This is the strongest version: does there exist `c > 0` such that for all
sufficiently large `n`, `∑_{k ≤ n} M_k > n^{1+c}`? -/

/-- Part 3 (Open): For any unit circle sequence, there exists `c > 0` such that
`∑_{k < n} M_k > n^{1+c}` for all sufficiently large `n`. -/
def ErdosProblem119 : Prop :=
    ∀ (z : ℕ → ℂ), (∀ i : ℕ, ‖z i‖ = 1) →
      ∃ (c : ℝ), c > 0 ∧ ∀ᶠ n in atTop,
        ∑ k ∈ range n, maxModulus z k > (n : ℝ) ^ (1 + c)

/-! ## Basic properties -/

/-- The polynomial at a single point: `p_1(w) = w - z_0`. -/
theorem unitCirclePoly_one (z : ℕ → ℂ) (w : ℂ) :
    unitCirclePoly z 1 w = w - z 0 := by
  simp [unitCirclePoly]

/-- The empty product is the constant polynomial 1. -/
theorem unitCirclePoly_zero (z : ℕ → ℂ) (w : ℂ) :
    unitCirclePoly z 0 w = 1 := by
  simp [unitCirclePoly]

/-- `M_n ≥ 1` for all `n ≥ 1`: evaluating at any `z_i` gives 0 for that factor,
but we can show `|p_n(z)| ≥ 1` at `z = 1` when all `z_i` are on the unit circle
by the product formula. More generally, the sup of a set containing 1 is ≥ 1. -/
axiom maxModulus_ge_one (z : ℕ → ℂ) (n : ℕ) (hn : 0 < n)
    (hz : ∀ i : ℕ, ‖z i‖ = 1) : 1 ≤ maxModulus z n

/-- Part 2 implies Part 1: polynomial growth implies the limsup is infinite. -/
axiom part2_implies_part1 :
    (∀ (z : ℕ → ℂ), (∀ i : ℕ, ‖z i‖ = 1) →
      ∃ (c : ℝ), c > 0 ∧ ∀ N : ℕ, ∃ n : ℕ, n ≤ N ∧ maxModulus z n > (N : ℝ) ^ c) →
    (∀ (z : ℕ → ℂ), (∀ i : ℕ, ‖z i‖ = 1) →
      atTop.limsup (fun n => (maxModulus z n : EReal)) = ⊤)

/-- Part 3 implies Part 2: if partial sums grow like `n^{1+c}`, then individual
terms must be large infinitely often. -/
axiom part3_implies_part2 :
    ErdosProblem119 →
    ∀ (z : ℕ → ℂ), (∀ i : ℕ, ‖z i‖ = 1) →
      ∃ (c : ℝ), c > 0 ∧ ∀ N : ℕ, ∃ n : ℕ, n ≤ N ∧ maxModulus z n > (N : ℝ) ^ c

/-- The maximum modulus is nonneg since it is the sup of a set of norms. -/
axiom maxModulus_nonneg (z : ℕ → ℂ) (n : ℕ) : 0 ≤ maxModulus z n
