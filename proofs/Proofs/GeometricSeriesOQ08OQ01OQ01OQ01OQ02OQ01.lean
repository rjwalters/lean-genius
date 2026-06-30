import Mathlib
import Proofs.GeometricSeriesOQ08OQ01OQ01OQ01OQ02
import Proofs.GeometricSeriesOQ07OQ01OQ01

/-
# Solving the infinite-limit recurrence (★∞) in closed form

## What This Proves

The parent `geometric-series-oq-08-oq-01-oq-01-oq-01-oq-02` introduces the
**infinite m-th moment**

  infMoment m x  :=  ∑_{k=0}^{∞} kᵐ·xᵏ        (|x| < 1)

and proves the binomial-convolution recurrence

  (1 − x)·infMoment m x  =  0ᵐ  +  x·∑_{i<m} C(m,i)·infMoment i x.   (★∞)

The sibling `geometric-series-oq-07-oq-01-oq-01` defines the Eulerian polynomial
`eulerPoly m` (geometric normalisation, by its differential recurrence
`E₀ = 1`, `E_{m+1} = X(1−X)·E'ₘ + (m+1)·X·Eₘ`) and proves the analytic
Frobenius closed form `HasSum (kᵐ·rᵏ) (Eₘ(r)/(1−r)^{m+1})`.

This entry **closes the loop** between the two lines:

* `infMoment_eq_eulerPoly` — the headline closed form
    `infMoment m x = Eₘ(x)/(1 − x)^{m+1}`,
  identifying the tsum-defined infinite moment with the Eulerian closed form.
* `eulerPoly_recurrence` — the **new polynomial identity** stating that the
  Eulerian polynomials *satisfy the (★∞) binomial-convolution recurrence*:

    (1 − X)·Eₘ  =  0ᵐ·(1 − X)^{m+1}  +  X·∑_{i<m} C(m,i)·Eᵢ·(1 − X)^{m−i}   (over ℝ[X]).

  This is the algebraic shadow of (★∞): it shows the *derivative-free* convolution
  recurrence and the *differential* Eulerian recurrence encode the same sequence
  of polynomials.  It is proved by `eq_of_infinite_eval_eq`: both sides agree at
  every `r ∈ (−1, 1)` (an infinite set) by combining the closed form with (★∞),
  hence agree as polynomials.
* `infMoment_three` — the explicit infinite **third** moment
    `∑ k³·xᵏ = x(1 + 4x + x²)/(1 − x)⁴`,
  a closed form one step beyond the parent's `infMoment_two`, read straight off
  `eulerPoly_three`.

## Honest Scope

The headline closed form is obtained by reusing the gallery's analytic Eulerian
identity (`hasSum_pow_mul_geometric_eulerPoly`), which itself rests on Frobenius'
identity and the Stirling moment formula — it is *not* re-derived from scratch by
strong induction on (★∞).  The genuinely new content is the polynomial recurrence
identity `eulerPoly_recurrence`, an explicit relation among the Eulerian
polynomials and the binomial weights that is not in Mathlib, and the new explicit
third-moment closed form.

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and
`sorry`-free.
-/

namespace GeometricSeriesOQ08OQ01OQ01OQ01OQ02OQ01

open Polynomial Finset
open GeometricSeriesOQ08OQ01OQ01OQ01OQ02 (infMoment infMoment_recurrence)
open GeometricSeriesOQ07OQ01OQ01
  (eulerPoly hasSum_pow_mul_geometric_eulerPoly eulerPoly_one eulerPoly_two eulerPoly_three)

/-! ## Part 1: the headline closed form -/

/-- **The closed-form solution of (★∞).**  For `|x| < 1`, the infinite moment
`infMoment m x = ∑_{k} kᵐ·xᵏ` equals the Eulerian-polynomial closed form
`Eₘ(x)/(1 − x)^{m+1}`.  This identifies the tsum-defined object of the parent
recurrence line with the Frobenius/Eulerian closed form of the sibling. -/
theorem infMoment_eq_eulerPoly (m : ℕ) {x : ℝ} (hx : |x| < 1) :
    infMoment m x = (eulerPoly m : ℝ[X]).eval x / (1 - x) ^ (m + 1) := by
  simpa only [infMoment] using (hasSum_pow_mul_geometric_eulerPoly m hx).tsum_eq

/-! ## Part 2: the Eulerian polynomials satisfy (★∞) -/

/-- **The Eulerian polynomials satisfy the (★∞) binomial-convolution recurrence.**
As an identity in `ℝ[X]`,

  `(1 − X)·Eₘ = 0ᵐ·(1 − X)^{m+1} + X·∑_{i<m} C(m,i)·Eᵢ·(1 − X)^{m−i}`.

This is the polynomial form of the infinite recurrence (★∞): clearing the
denominators `(1 − x)^{i+1}` in the closed form turns the analytic convolution
recurrence into a single polynomial identity, connecting the derivative-free
Pascal recursion to the differential recurrence defining `eulerPoly`.

Proof: both sides are polynomials that agree at every `r ∈ (−1, 1)` — there, by
the closed form `infMoment i r = Eᵢ(r)/(1−r)^{i+1}` and the parent's (★∞), the
two evaluations coincide — and `(−1, 1)` is infinite, so the polynomials are
equal. -/
theorem eulerPoly_recurrence (m : ℕ) :
    (1 - X) * (eulerPoly m : ℝ[X])
      = (0 : ℝ[X]) ^ m * (1 - X) ^ (m + 1)
        + X * ∑ i ∈ range m, (m.choose i : ℝ[X]) * eulerPoly i * (1 - X) ^ (m - i) := by
  apply eq_of_infinite_eval_eq
  refine (Set.Ioo_infinite (show (-1 : ℝ) < 1 by norm_num)).mono ?_
  intro r hr
  rw [Set.mem_Ioo] at hr
  have hr' : |r| < 1 := abs_lt.mpr ⟨hr.1, hr.2⟩
  have h1 : (1 : ℝ) - r ≠ 0 := by have := hr.2; linarith
  -- Express every Eulerian eval through the corresponding infinite moment.
  have hE : ∀ i, (eulerPoly i : ℝ[X]).eval r = infMoment i r * (1 - r) ^ (i + 1) := by
    intro i
    rw [infMoment_eq_eulerPoly i hr', div_mul_cancel₀ _ (pow_ne_zero _ h1)]
  -- Pull the common power out of the binomial sum.
  have hsum :
      (∑ i ∈ range m, (m.choose i : ℝ) * (eulerPoly i : ℝ[X]).eval r * (1 - r) ^ (m - i))
        = (1 - r) ^ (m + 1) * ∑ i ∈ range m, (m.choose i : ℝ) * infMoment i r := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    rw [hE i, show m + 1 = (i + 1) + (m - i) from by omega, pow_add]
    ring
  -- Reduce to the parent's infinite recurrence (★∞).
  have hrec := infMoment_recurrence m hr'
  simp only [Set.mem_setOf_eq, eval_mul, eval_sub, eval_one, eval_X, eval_add, eval_pow,
    eval_zero, eval_finset_sum, eval_natCast]
  rw [hE m, hsum]
  linear_combination (1 - r) ^ (m + 1) * hrec

/-! ## Part 3: low-order closed forms -/

/-- Recovering the infinite first moment from the closed form:
`infMoment 1 x = x/(1 − x)²` (consistency with the parent's `infMoment_one`). -/
theorem infMoment_one {x : ℝ} (hx : |x| < 1) :
    infMoment 1 x = x / (1 - x) ^ 2 := by
  rw [infMoment_eq_eulerPoly 1 hx, eulerPoly_one, eval_X]

/-- Recovering the infinite second moment from the closed form:
`infMoment 2 x = x(1 + x)/(1 − x)³` (consistency with the parent's `infMoment_two`). -/
theorem infMoment_two {x : ℝ} (hx : |x| < 1) :
    infMoment 2 x = (x + x ^ 2) / (1 - x) ^ 3 := by
  rw [infMoment_eq_eulerPoly 2 hx, eulerPoly_two]
  simp [eval_add, eval_pow, eval_X]

/-- **The infinite third moment**, one order beyond the parent's `infMoment_two`:
`∑_{k} k³·xᵏ = (x + 4x² + x³)/(1 − x)⁴`, read off the Eulerian polynomial
`E₃ = X + 4X² + X³`. -/
theorem infMoment_three {x : ℝ} (hx : |x| < 1) :
    infMoment 3 x = (x + 4 * x ^ 2 + x ^ 3) / (1 - x) ^ 4 := by
  rw [infMoment_eq_eulerPoly 3 hx, eulerPoly_three]
  simp [eval_add, eval_mul, eval_pow, eval_X]

end GeometricSeriesOQ08OQ01OQ01OQ01OQ02OQ01
