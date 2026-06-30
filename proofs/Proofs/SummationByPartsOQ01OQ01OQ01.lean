import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic

/-
# The general Abel degree-lowering recursion for geometric-weighted sums

## What This Proves

For **any** commutative ring `R`, **any** sequence `f : ℕ → R`, **any** ring
element `r`, and **any** `n : ℕ`, with no side hypotheses whatsoever,

    (r − 1) · ∑_{k<n} f k · rᵏ
      = f n · rⁿ − f 0 − ∑_{k<n} (f (k+1) − f k) · r^{k+1}.                (★)

Equivalently, factoring `r^{k+1} = r · rᵏ` out of the correction term,

    (r − 1) · ∑_{k<n} f k · rᵏ
      = f n · rⁿ − f 0 − r · ∑_{k<n} (f (k+1) − f k) · rᵏ.                 (★★)

This is **Abel's summation by parts specialised to a geometric weight**: it turns
a sum weighted by an *arbitrary* sequence `f` into the same kind of sum weighted
by the *forward difference* `Δf k = f (k+1) − f k`, plus an explicit boundary
term `f n · rⁿ − f 0`.  Iterating (★★) lowers the "degree" of `f` one step at a
time, so a polynomial weight of degree `d` collapses after `d+1` applications to
the geometric base case `∑ rᵏ` (where `Δ(const) = 0`).

## Why This Is the Right Object

The parent entry `SummationByPartsOQ01OQ01` derives the *single* closed form
`∑_{k<n} k²·rᵏ` (the second rung of the ladder `∑ kᵐ rᵏ`) and its grandparent
`SummationByPartsOQ01` does the first rung `∑ k·rᵏ`.  Each was proved by hand for
one fixed weight.  The open question recorded by that entry asks for the *uniform
mechanism* generating every such formula — the recursion that drops `∑ kᵐ rᵏ` to
`∑ kᵐ⁻¹ rᵏ` and ultimately to `∑ rᵏ`.

Theorem (★) **is** that mechanism, and it is *more* general than the polynomial
case: it holds for every sequence `f`, over every commutative ring, with zero
hypotheses (in particular no `r ≠ 1`, since both sides are polynomial in `r`).
The hypothesis-laden division form `∑ f k rᵏ = (boundary)/(r−1)` is then an
immediate corollary over a field once `r ≠ 1`.

We close the loop by reading the classical specialisations straight off (★):

* `geom_sum_via_recursion` : `f ≡ 1` ⟹ `(r−1)·∑ rᵏ = rⁿ − 1` (Δf ≡ 0; the
  geometric series is the bottom of the ladder).
* `sum_range_id_mul_geom_recursion` : `f k = k` ⟹ the first-order sum `∑ k·rᵏ`
  reduces to a pure geometric sum (Δf ≡ 1).
* `sum_range_sq_mul_geom_recursion` : `f k = k²` ⟹ the second-order sum `∑ k²·rᵏ`
  reduces to a first-order weighted sum (Δf k = 2k+1), exactly the
  degree-lowering step the parent entry performed by hand.

## Method

Theorem (★) is proved by induction on `n`.  The inductive step peels the top term
off both the weighted sum and the difference sum with `Finset.sum_range_succ`,
substitutes the induction hypothesis for `(r−1)·∑_{k<m}`, and the remaining
identity in the atoms `f m`, `f (m+1)`, `f 0`, `rᵐ`, `r` is polynomial and closed
by `ring`.  No summation-by-parts black box is invoked — the recursion is the
elementary content *behind* `Finset.sum_range_by_parts`, here exhibited directly.

## Tags

summation-by-parts, abel-summation, arithmetico-geometric, finite-differences,
geometric-series, recursion, closed-form, commutative-ring
-/

namespace SummationByPartsOQ01OQ01OQ01

open Finset

/-- **The general Abel degree-lowering recursion (★).**
Over any commutative ring, for any sequence `f`, any `r`, and any `n`,
`(r − 1)·∑_{k<n} f k · rᵏ = f n · rⁿ − f 0 − ∑_{k<n} (f (k+1) − f k)·r^{k+1}`.
No hypotheses: both sides are polynomials in `r` and the sequence values. -/
theorem geom_weighted_recursion {R : Type*} [CommRing R] (f : ℕ → R) (r : R)
    (n : ℕ) :
    (r - 1) * ∑ k ∈ range n, f k * r ^ k
      = f n * r ^ n - f 0 - ∑ k ∈ range n, (f (k + 1) - f k) * r ^ (k + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ (fun k => f k * r ^ k), mul_add, ih,
        Finset.sum_range_succ (fun k => (f (k + 1) - f k) * r ^ (k + 1))]
      ring

/-- **Factored form (★★).** Pulling `r` out of the correction term exhibits the
recursion as "weighted sum of `f` ↦ weighted sum of the forward difference `Δf`":
`(r − 1)·∑ f k rᵏ = f n rⁿ − f 0 − r·∑ (f (k+1) − f k) rᵏ`. -/
theorem geom_weighted_recursion_factored {R : Type*} [CommRing R] (f : ℕ → R)
    (r : R) (n : ℕ) :
    (r - 1) * ∑ k ∈ range n, f k * r ^ k
      = f n * r ^ n - f 0 - r * ∑ k ∈ range n, (f (k + 1) - f k) * r ^ k := by
  rw [geom_weighted_recursion f r n, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_succ]
  ring

/-- **Division form (field).** Over a field with `r ≠ 1`, the weighted sum is the
boundary term divided by `r − 1`:
`∑_{k<n} f k rᵏ = (f n rⁿ − f 0 − ∑ (f (k+1) − f k) r^{k+1}) / (r − 1)`. -/
theorem geom_weighted_recursion_div {K : Type*} [Field K] {r : K} (hr : r ≠ 1)
    (f : ℕ → K) (n : ℕ) :
    ∑ k ∈ range n, f k * r ^ k
      = (f n * r ^ n - f 0
          - ∑ k ∈ range n, (f (k + 1) - f k) * r ^ (k + 1)) / (r - 1) := by
  have hr1 : r - 1 ≠ 0 := sub_ne_zero.mpr hr
  rw [eq_div_iff hr1, mul_comm]
  exact geom_weighted_recursion f r n

/-- **Bottom of the ladder: the geometric series.** Taking `f ≡ 1` makes every
forward difference vanish, so (★) collapses to `(r − 1)·∑_{k<n} rᵏ = rⁿ − 1`. -/
theorem geom_sum_via_recursion {R : Type*} [CommRing R] (r : R) (n : ℕ) :
    (r - 1) * ∑ k ∈ range n, r ^ k = r ^ n - 1 := by
  have h := geom_weighted_recursion (fun _ => (1 : R)) r n
  simpa using h

/-- **First rung from the engine.** With weight `f k = k` the forward differences
are constant `Δf ≡ 1`, so (★) reduces the first-order arithmetico-geometric sum
to a pure geometric sum:
`(r − 1)·∑_{k<n} k·rᵏ = n·rⁿ − ∑_{k<n} r^{k+1}`. -/
theorem sum_range_id_mul_geom_recursion {R : Type*} [CommRing R] (r : R) (n : ℕ) :
    (r - 1) * ∑ k ∈ range n, (k : R) * r ^ k
      = (n : R) * r ^ n - ∑ k ∈ range n, r ^ (k + 1) := by
  have h := geom_weighted_recursion (fun k => (k : R)) r n
  rw [h, Nat.cast_zero, sub_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

/-- **Second rung from the engine.** With weight `f k = k²` the forward differences
are the linear sequence `Δf k = 2k + 1`, so (★) reduces the second-order sum to a
first-order weighted sum — precisely the degree-lowering step that the parent
entry `SummationByPartsOQ01OQ01` carried out by hand:
`(r − 1)·∑_{k<n} k²·rᵏ = n²·rⁿ − ∑_{k<n} (2k + 1)·r^{k+1}`. -/
theorem sum_range_sq_mul_geom_recursion {R : Type*} [CommRing R] (r : R) (n : ℕ) :
    (r - 1) * ∑ k ∈ range n, (k : R) ^ 2 * r ^ k
      = (n : R) ^ 2 * r ^ n - ∑ k ∈ range n, (2 * (k : R) + 1) * r ^ (k + 1) := by
  have h := geom_weighted_recursion (fun k => (k : R) ^ 2) r n
  rw [h]
  simp only [Nat.cast_zero]
  ring_nf
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

end SummationByPartsOQ01OQ01OQ01
