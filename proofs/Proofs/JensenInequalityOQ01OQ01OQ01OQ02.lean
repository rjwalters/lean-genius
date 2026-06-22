/-
# The Generalized (Finite-Family) Minkowski Inequality

The two-vector Minkowski inequality — the triangle inequality for the discrete `ℓᵖ` "norm" —
states that for `1 ≤ p`, a coordinate set `s`, and nonnegative vectors `f, g : ι → ℝ`,

    ‖f + g‖_p ≤ ‖f‖_p + ‖g‖_p,    where ‖h‖_p := (∑ᵢ h(i)ᵖ)^{1/p}.

Mathlib provides exactly this two-vector form (`Real.Lp_add_le_of_nonneg`), but **not** the
generalization to an arbitrary *finite family* of vectors. This file supplies that gap:

    ‖∑ⱼ Fⱼ‖_p ≤ ∑ⱼ ‖Fⱼ‖_p,

i.e. for a finite index set `t` of vectors `Fⱼ : ι → ℝ` (all nonnegative on `s`),

    (∑ᵢ (∑ⱼ Fⱼ(i))ᵖ)^{1/p} ≤ ∑ⱼ (∑ᵢ Fⱼ(i)ᵖ)^{1/p}.

This is the `ℓᵖ`-norm analogue, and the exact sibling, of the parent file's generalization of the
two-term to the `n`-term Young/Hölder inequality (`JensenInequalityOQ01OQ01OQ01`): there the
*two-factor* product inequality was lifted to a *finite family of factors*; here the *two-vector*
triangle inequality is lifted to a *finite family of vectors*. The proof is the textbook one:
induction on the family, using the two-vector case at each step (subadditivity of a seminorm).

While Mathlib's abstract `PiLp`/`WithLp` machinery yields a triangle inequality through the general
normed-space API, the elementary closed-form `Finset.sum` statement below — directly comparable to
`Real.Lp_add_le_of_nonneg` and usable without instantiating any normed-space structure — is not
available in Mathlib.

## Main results

* `Lpnorm`            — the unnormalised discrete `ℓᵖ` "norm" `(∑ᵢ h(i)ᵖ)^{1/p}`.
* `Lpnorm_nonneg`     — the norm of a nonnegative vector is nonnegative.
* `Lpnorm_add_le`     — the two-vector triangle inequality (Mathlib's, in this notation).
* `minkowski_finset`  — **the finite-family Minkowski inequality** `‖∑ⱼ Fⱼ‖_p ≤ ∑ⱼ ‖Fⱼ‖_p`.
* `Lpnorm_add3`       — the three-vector instance, derived from `minkowski_finset` (a case Mathlib
                        does not provide), witnessing that the family form genuinely generalizes.

All results are fully machine-checked: 0 sorries, 0 axioms, no `native_decide`.
-/

import Mathlib

open Finset

namespace JensenMinkowski

variable {ι κ : Type*} {s : Finset ι} {p : ℝ}

/-- The unnormalised discrete `ℓᵖ` "norm" of a vector `g : ι → ℝ` over the coordinate set `s`:
`Lpnorm s p g = (∑ i ∈ s, g i ^ p) ^ (1/p)`. For `1 ≤ p` and nonnegative `g` this is the genuine
`ℓᵖ` norm of the restriction of `g` to `s`. -/
noncomputable def Lpnorm (s : Finset ι) (p : ℝ) (g : ι → ℝ) : ℝ :=
  (∑ i ∈ s, g i ^ p) ^ (1 / p)

/-- The `ℓᵖ` norm of a nonnegative vector is nonnegative. -/
theorem Lpnorm_nonneg {g : ι → ℝ} (hg : ∀ i ∈ s, 0 ≤ g i) : 0 ≤ Lpnorm s p g := by
  refine Real.rpow_nonneg (Finset.sum_nonneg fun i hi => ?_) _
  exact Real.rpow_nonneg (hg i hi) _

/-- **Two-vector Minkowski inequality** in the `Lpnorm` notation: `‖f + g‖_p ≤ ‖f‖_p + ‖g‖_p`.
This is `Real.Lp_add_le_of_nonneg` restated; it is the base step of the finite-family form. -/
theorem Lpnorm_add_le (hp : 1 ≤ p) {f g : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i) :
    Lpnorm s p (fun i => f i + g i) ≤ Lpnorm s p f + Lpnorm s p g :=
  Real.Lp_add_le_of_nonneg (s := s) hp hf hg

/-- **The finite-family Minkowski inequality.** For `1 ≤ p`, a finite family of vectors
`F j : ι → ℝ` (`j ∈ t`) that are nonnegative on the coordinate set `s`, the `ℓᵖ` norm of their sum
is at most the sum of their `ℓᵖ` norms:

    Lpnorm s p (fun i => ∑ j ∈ t, F j i) ≤ ∑ j ∈ t, Lpnorm s p (F j).

The proof is by induction on the family `t`. The empty family gives the zero vector (norm `0`); the
inductive step peels one vector off with `Finset.sum_insert`, applies the two-vector triangle
inequality `Lpnorm_add_le`, and closes with the induction hypothesis. -/
theorem minkowski_finset (hp : 1 ≤ p) (t : Finset κ) (F : κ → ι → ℝ)
    (hF : ∀ j ∈ t, ∀ i ∈ s, 0 ≤ F j i) :
    Lpnorm s p (fun i => ∑ j ∈ t, F j i) ≤ ∑ j ∈ t, Lpnorm s p (F j) := by
  classical
  induction t using Finset.induction with
  | empty =>
      have hp0 : (0 : ℝ) < p := lt_of_lt_of_le one_pos hp
      simp only [Finset.sum_empty, Lpnorm, Real.zero_rpow hp0.ne', Finset.sum_const_zero,
        Real.zero_rpow (one_div_ne_zero hp0.ne'), le_refl]
  | @insert a u ha ih =>
      have hFa : ∀ i ∈ s, 0 ≤ F a i := hF a (Finset.mem_insert_self a u)
      have hFu : ∀ j ∈ u, ∀ i ∈ s, 0 ≤ F j i :=
        fun j hj => hF j (Finset.mem_insert_of_mem hj)
      have hG : ∀ i ∈ s, 0 ≤ ∑ j ∈ u, F j i :=
        fun i hi => Finset.sum_nonneg fun j hj => hFu j hj i hi
      have hstep : (fun i => ∑ j ∈ insert a u, F j i)
          = (fun i => F a i + ∑ j ∈ u, F j i) := by
        funext i; exact Finset.sum_insert ha
      rw [hstep, Finset.sum_insert ha]
      calc Lpnorm s p (fun i => F a i + ∑ j ∈ u, F j i)
          ≤ Lpnorm s p (F a) + Lpnorm s p (fun i => ∑ j ∈ u, F j i) :=
            Lpnorm_add_le hp hFa hG
        _ ≤ Lpnorm s p (F a) + ∑ j ∈ u, Lpnorm s p (F j) := by
            gcongr
            exact ih hFu

/-- The three-vector triangle inequality, obtained as the `m = 3` instance of `minkowski_finset`
(a case Mathlib does not provide): `‖f + g + h‖_p ≤ ‖f‖_p + ‖g‖_p + ‖h‖_p`. -/
theorem Lpnorm_add3 (hp : 1 ≤ p) {f g h : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i) (hh : ∀ i ∈ s, 0 ≤ h i) :
    Lpnorm s p (fun i => f i + g i + h i)
      ≤ Lpnorm s p f + Lpnorm s p g + Lpnorm s p h := by
  have key := minkowski_finset (s := s) hp (Finset.univ : Finset (Fin 3)) ![f, g, h] ?_
  · simpa [Fin.sum_univ_three, add_assoc] using key
  · intro j _ i hi
    fin_cases j
    · simpa using hf i hi
    · simpa using hg i hi
    · simpa using hh i hi

end JensenMinkowski
