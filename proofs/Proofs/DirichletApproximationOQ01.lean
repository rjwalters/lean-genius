/-
# Dirichlet Approximation — OQ-01: Infinitude of Good Rational Approximations

**Open Question (upgrade of the one-shot bound)**: The parent entry
`DirichletApproximation` proves the *finite* pigeonhole statement — for each
`Q` there is one fraction `p/q` with `1 ≤ q ≤ Q` and `|qα − p| < 1/Q`. This
file upgrades that to the **infinitude** statement: for every irrational `α`
there are *infinitely many* fractions in lowest terms with
`|α − p/q| < 1/q²`.

## Status

The infinitude statement itself is already in Mathlib as
`Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`, phrased over the
set of rationals `{q : ℚ | |ξ − q| < 1/q.den²}`. The *original contribution*
here is the bridge from that set-of-rationals form to the **classical
coprime integer-pair statement** found in textbooks:

> there are infinitely many pairs `(p, q) ∈ ℤ × ℕ` with `q > 0`,
> `gcd(|p|, q) = 1`, and `|α − p/q| < 1/q²`.

This reformulation is proved by transporting the infinitude through the
injection `q ↦ (q.num, q.den)`, whose image lands inside the coprime-pair set
because every rational is stored in lowest terms (`Rat.reduced`) with positive
denominator (`Rat.pos`) and `(q.num : ℝ)/(q.den : ℝ) = (q : ℝ)`
(`Rat.cast_def`).

We also record the sharp converse direction (`Real.…_iff_irrational`):
*only* irrationals admit infinitely many such approximations — a rational has
just finitely many — so the hypothesis `Irrational α` is exactly the right one.

## References

* Mathlib: `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean`
* G.H. Hardy & E.M. Wright, *An Introduction to the Theory of Numbers*, Thm 193.
-/
import Mathlib

namespace DirichletApproximationOQ01

open Set

variable {ξ : ℝ}

/-- **Infinitude of good rational approximations.** For every irrational `ξ`
there are infinitely many rationals `q` (automatically in lowest terms) with
`|ξ − q| < 1/q.den²`. This is the headline statement; it delegates to Mathlib's
`Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`. -/
theorem infinite_good_rat_approx (hξ : Irrational ξ) :
    {q : ℚ | |ξ - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2}.Infinite :=
  Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hξ

/-- **Classical coprime integer-pair form (original reformulation).** For every
irrational `ξ` there are infinitely many pairs `(p, q) ∈ ℤ × ℕ` with `q > 0`,
`gcd(|p|, q) = 1`, and `|ξ − p/q| < 1/q²`.

The proof transports `infinite_good_rat_approx` along the injection
`q ↦ (q.num, q.den)`. The image lands in the coprime-pair set because each
rational has positive denominator, is stored in lowest terms, and satisfies
`(q.num : ℝ)/(q.den : ℝ) = (q : ℝ)`. -/
theorem infinite_coprime_approx (hξ : Irrational ξ) :
    {pq : ℤ × ℕ | 0 < pq.2 ∧ Nat.Coprime pq.1.natAbs pq.2 ∧
        |ξ - (pq.1 : ℝ) / (pq.2 : ℝ)| < 1 / (pq.2 : ℝ) ^ 2}.Infinite := by
  have hS : {q : ℚ | |ξ - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2}.Infinite :=
    infinite_good_rat_approx hξ
  -- The numerator/denominator map is injective on the good-approximation set.
  set f : ℚ → ℤ × ℕ := fun q => (q.num, q.den) with hf
  have hinj : Set.InjOn f {q : ℚ | |ξ - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2} := by
    intro a _ b _ hab
    simp only [hf, Prod.mk.injEq] at hab
    rw [← Rat.num_div_den a, ← Rat.num_div_den b, hab.1, hab.2]
  -- Its image lands in the coprime-pair set.
  have hsub : f '' {q : ℚ | |ξ - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2} ⊆
      {pq : ℤ × ℕ | 0 < pq.2 ∧ Nat.Coprime pq.1.natAbs pq.2 ∧
        |ξ - (pq.1 : ℝ) / (pq.2 : ℝ)| < 1 / (pq.2 : ℝ) ^ 2} := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨q.pos, q.reduced, ?_⟩
    -- Reduce the `(q.num, q.den).1 / .2` projections to `q.num / q.den`,
    -- then rewrite `q.num/q.den = q` via `Rat.cast_def`.
    show |ξ - (q.num : ℝ) / (q.den : ℝ)| < 1 / (q.den : ℝ) ^ 2
    have hcast : ((q.num : ℝ) / (q.den : ℝ)) = (q : ℝ) := (Rat.cast_def).symm
    rw [hcast]
    exact hq
  exact ((infinite_image_iff hinj).mpr hS).mono hsub

/-- **Sharp converse (Mathlib).** A real number admits infinitely many good
rational approximations *iff* it is irrational; rationals have only finitely
many. Thus `Irrational ξ` is the exact hypothesis of the two theorems above. -/
theorem infinite_approx_iff_irrational (ξ : ℝ) :
    {q : ℚ | |ξ - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2}.Infinite ↔ Irrational ξ :=
  Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational ξ

/-- **Existence corollary.** Every irrational has at least one good rational
approximation `|ξ − q| < 1/q.den²` (the one-shot Dirichlet bound, recovered as a
consequence of infinitude). -/
theorem exists_good_approx (hξ : Irrational ξ) :
    ∃ q : ℚ, |ξ - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2 := by
  obtain ⟨q, hq⟩ := (infinite_good_rat_approx hξ).nonempty
  exact ⟨q, hq⟩

end DirichletApproximationOQ01
