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
    have hcast : ((q.num : ℝ) / (q.den : ℝ)) = (q : ℝ) := (Rat.cast_def q).symm
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

/-- **Bounded-height finiteness (original infrastructure).** The rationals lying
in a bounded real interval `[a, b]` whose denominator is at most `N` form a
*finite* set. The numerator/denominator map `q ↦ (q.num, q.den)` embeds them
into the finite integer box `[-M, M] × [1, N]`, where `M` bounds the numerators
via `|q.num| = |q|·q.den ≤ max |a| |b| · N`. This is exactly the discreteness
fact that powers the "unbounded denominators" strengthening below; Mathlib has
the analogous statement only for *rational* targets (`finite_rat_abs_sub_…`). -/
theorem finite_bounded_den (a b : ℝ) (N : ℕ) :
    {q : ℚ | a ≤ (q : ℝ) ∧ (q : ℝ) ≤ b ∧ q.den ≤ N}.Finite := by
  obtain ⟨M, hM⟩ := exists_nat_ge (max |a| |b| * N)
  apply Set.Finite.of_finite_image (f := fun q : ℚ => (q.num, q.den))
  · -- The image is contained in a finite integer box, hence finite.
    apply Set.Finite.subset
      ((Finset.Icc (-(M : ℤ)) (M : ℤ) ×ˢ Finset.Icc 1 N).finite_toSet)
    rintro p ⟨q, ⟨ha, hb, hden⟩, rfl⟩
    have hdpos : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
    have hnum : (q.num : ℝ) = (q : ℝ) * (q.den : ℝ) := by
      rw [Rat.cast_def]; field_simp
    have hqle : (q : ℝ) ≤ max |a| |b| :=
      le_trans hb (le_trans (le_abs_self b) (le_max_right _ _))
    have hqge : -max |a| |b| ≤ (q : ℝ) :=
      le_trans (le_trans (neg_le_neg (le_max_left _ _)) (neg_abs_le a)) ha
    have habsq : |(q : ℝ)| ≤ max |a| |b| := abs_le.mpr ⟨hqge, hqle⟩
    have hdenR : (q.den : ℝ) ≤ (N : ℝ) := by exact_mod_cast hden
    have habsnum : |(q.num : ℝ)| ≤ (M : ℝ) := by
      rw [hnum, abs_mul, abs_of_pos hdpos]
      calc |(q : ℝ)| * (q.den : ℝ)
          ≤ max |a| |b| * (N : ℝ) := by gcongr
        _ ≤ (M : ℝ) := hM
    have hb1 : -(M : ℤ) ≤ q.num := by exact_mod_cast (abs_le.mp habsnum).1
    have hb2 : q.num ≤ (M : ℤ) := by exact_mod_cast (abs_le.mp habsnum).2
    simp only [Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc]
    exact ⟨⟨hb1, hb2⟩, q.pos, hden⟩
  · -- The numerator/denominator map is injective.
    intro x _ y _ hxy
    simp only [Prod.mk.injEq] at hxy
    rw [← Rat.num_div_den x, ← Rat.num_div_den y, hxy.1, hxy.2]

/-- **Unbounded denominators (original strengthening).** For every irrational
`ξ` and every bound `N`, there remain *infinitely many* good approximations
`|ξ − q| < 1/q.den²` whose denominator is at least `N`.

Proof: the full good-approximation set is infinite (`infinite_good_rat_approx`),
while its low-denominator part `{q.den < N}` is finite — each such `q` satisfies
`|ξ − q| < 1/q.den² ≤ 1`, so it lies in `[ξ−1, ξ+1]` with `q.den ≤ N`, a finite
set by `finite_bounded_den`. An infinite set minus a finite set is infinite. -/
theorem infinite_good_approx_large_den (hξ : Irrational ξ) (N : ℕ) :
    {q : ℚ | |ξ - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2 ∧ N ≤ q.den}.Infinite := by
  have hSinf : {q : ℚ | |ξ - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2}.Infinite :=
    infinite_good_rat_approx hξ
  have hlow : {q : ℚ | |ξ - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2 ∧ q.den < N}.Finite := by
    apply (finite_bounded_den (ξ - 1) (ξ + 1) N).subset
    rintro q ⟨hq, hqd⟩
    have hden1 : (1 : ℝ) ≤ (q.den : ℝ) := by exact_mod_cast q.pos
    have hbound : 1 / (q.den : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [hden1]
    have h1 : |ξ - (q : ℝ)| < 1 := lt_of_lt_of_le hq hbound
    rw [abs_lt] at h1
    exact ⟨by linarith [h1.1, h1.2], by linarith [h1.1, h1.2], le_of_lt hqd⟩
  apply (hSinf.diff hlow).mono
  rintro q ⟨hq, hqlow⟩
  refine ⟨hq, ?_⟩
  by_contra h
  push_neg at h
  exact hqlow ⟨hq, h⟩

/-- **Existence with large denominator.** A direct corollary: for every
irrational `ξ` and every `N`, there is a good approximation
`|ξ − q| < 1/q.den²` with `q.den ≥ N`. In particular the convergent
denominators are unbounded — there is no single `Q` past which all good
approximations stop. -/
theorem exists_good_approx_large_den (hξ : Irrational ξ) (N : ℕ) :
    ∃ q : ℚ, N ≤ q.den ∧ |ξ - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2 := by
  obtain ⟨q, hq, hqd⟩ := (infinite_good_approx_large_den hξ N).nonempty
  exact ⟨q, hqd, hq⟩

end DirichletApproximationOQ01
