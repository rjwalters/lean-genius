import Mathlib

/-
# Lebesgue Measure, oq-03-wip-01 — The Infinite-Dimensional Impossibility Theorem

Parent entry `lebesgue-measure-oq-03` (Infinite-Dimensional Measure Theory) is
*axiomatized*. Its first open question asks:

> Can the impossibility theorem be fully formalized in Lean using Mathlib's
> MeasureTheory infrastructure? The argument is elementary but requires formalizing
> infinite disjoint families of sets with the same measure.

This file does exactly that. The **impossibility theorem** states that an
infinite-dimensional normed space carries no nonzero, translation-invariant,
locally finite Borel measure — there is no "Lebesgue measure" in infinite
dimensions. The classical proof is elementary:

* Take an infinite orthonormal sequence `(eₙ)`; then `dist (eₙ) (eₘ) = √2` for
  `n ≠ m`, so the open balls `B(eₙ, √2/2)` are pairwise disjoint, and all lie in the
  bounded ball `B(0, 1 + √2/2)`.
* Translation invariance makes every `μ B(eₙ, √2/2)` equal to `c := μ B(0, √2/2)`.
* Countable additivity gives `μ B(0, 1+√2/2) ≥ Σₙ c`. If `c > 0` this sum is `∞`,
  contradicting local finiteness. Hence `c = 0`.

The measure-theoretic heart — "infinite disjoint families of sets with the same
measure force that measure to be `0`" — is isolated as
`measure_eq_zero_of_infinite_disjoint`, exactly the ingredient the open question
names. Fully machine-checked; `0` axioms beyond Mathlib's foundations; no
`native_decide`.

Tags: measure-theory, infinite-dimensional, impossibility, translation-invariance,
lebesgue, orthonormal
-/

namespace LebesgueMeasureOQ03WIP01

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

/-
## Part I: The measure-theoretic core

Infinitely many pairwise-disjoint sets of equal measure, all inside a set of finite
measure, must have measure zero. This is the abstract engine of the impossibility
theorem — precisely the "infinite disjoint families of sets with the same measure"
the open question highlights.
-/

/-- **Core lemma.** If `(Aₙ)` are pairwise-disjoint measurable sets, all with the
same measure `c`, all contained in a set `B` of finite measure, then `c = 0`.
Countable additivity forces `μ B ≥ ∑ₙ c`, which is `∞` unless `c = 0`. -/
theorem measure_eq_zero_of_infinite_disjoint {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A : ℕ → Set X) (hmeas : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) (c : ℝ≥0∞)
    (hc : ∀ i, μ (A i) = c)
    (B : Set X) (hsub : ∀ i, A i ⊆ B) (hB : μ B ≠ ∞) : c = 0 := by
  by_contra hc0
  have hunion : μ (⋃ i, A i) = ∑' _ : ℕ, c := by
    rw [measure_iUnion hdisj hmeas]; exact tsum_congr hc
  have htop : (∑' _ : ℕ, c) = ∞ := ENNReal.tsum_const_eq_top_of_ne_zero hc0
  have hle : μ (⋃ i, A i) ≤ μ B := measure_mono (iUnion_subset hsub)
  rw [hunion, htop] at hle
  exact hB (top_le_iff.mp hle)

/-
## Part II: The impossibility mechanism

A translation-invariant measure that is finite on a bounded ball must vanish on any
smaller ball around which infinitely many disjoint translates fit — i.e. whenever the
space contains an infinite family of points pairwise separated by `≥ 2r` yet bounded.
-/

/-- **Impossibility mechanism.** Let `μ` be translation invariant on a normed group
`E`. If there is an infinite family of points `xₙ` pairwise at distance `≥ 2r` and all
within distance `M` of the origin, and `μ` is finite on `B(0, M+r)`, then
`μ B(0, r) = 0`. The balls `B(xₙ, r)` are disjoint, equal-measure (by invariance), and
bounded, so the core lemma applies. -/
theorem ball_measure_zero_of_separated {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    (hinv : ∀ (v : E) (s : Set E), μ (v +ᵥ s) = μ s)
    (x : ℕ → E) (r M : ℝ) (hr : 0 < r)
    (hsep : ∀ i j, i ≠ j → 2 * r ≤ dist (x i) (x j))
    (hbdd : ∀ i, dist (x i) 0 ≤ M)
    (hfin : μ (ball 0 (M + r)) ≠ ∞) :
    μ (ball 0 r) = 0 := by
  refine measure_eq_zero_of_infinite_disjoint μ (fun i => ball (x i) r)
    (fun i => measurableSet_ball) ?_ (μ (ball 0 r)) ?_ (ball 0 (M + r)) ?_ hfin
  · -- pairwise disjoint
    intro i j hij
    exact ball_disjoint_ball (by have := hsep i j hij; linarith)
  · -- equal measure via translation invariance
    intro i
    show μ (ball (x i) r) = μ (ball 0 r)
    have hb : x i +ᵥ ball (0 : E) r = ball (x i) r := by
      rw [Metric.vadd_ball, vadd_eq_add, add_zero]
    rw [← hb]; exact hinv (x i) (ball 0 r)
  · -- contained in the bounded ball
    intro i
    show ball (x i) r ⊆ ball 0 (M + r)
    intro y hy
    rw [mem_ball] at hy
    rw [mem_ball]
    calc dist y 0 ≤ dist y (x i) + dist (x i) 0 := dist_triangle _ _ _
      _ < r + M := by have := hbdd i; linarith
      _ = M + r := by ring

/-
## Part III: The impossibility theorem via an orthonormal sequence

In an infinite-dimensional real inner product space an orthonormal sequence `(eₙ)`
exists (e.g. the standard basis of `ℓ²`); its points are pairwise `√2` apart, giving
the separated bounded family the mechanism needs.
-/

/-- Two distinct vectors of an orthonormal family are exactly `√2` apart:
`‖eᵢ − eⱼ‖² = ‖eᵢ‖² − 2⟪eᵢ,eⱼ⟫ + ‖eⱼ‖² = 1 − 0 + 1 = 2`. -/
theorem orthonormal_dist_eq_sqrt_two {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {x : ℕ → E} (ho : Orthonormal ℝ x) {i j : ℕ} (hij : i ≠ j) :
    dist (x i) (x j) = Real.sqrt 2 := by
  have hnormsq : ‖x i - x j‖ ^ 2 = 2 := by
    rw [norm_sub_sq_real, ho.norm_eq_one i, ho.norm_eq_one j, ho.inner_eq_zero hij]
    norm_num
  rw [dist_eq_norm, ← hnormsq, Real.sqrt_sq (norm_nonneg _)]

/-- **The impossibility theorem.** On an infinite-dimensional real inner product space
carrying an orthonormal sequence `(eₙ)`, any translation-invariant Borel measure that
is finite on the ball `B(0, 1 + √2/2)` assigns measure `0` to the ball `B(0, √2/2)`.
No nonzero, translation-invariant, locally finite measure can exist. -/
theorem ball_measure_zero_of_orthonormal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    (hinv : ∀ (v : E) (s : Set E), μ (v +ᵥ s) = μ s)
    {x : ℕ → E} (ho : Orthonormal ℝ x)
    (hloc : μ (ball 0 (1 + Real.sqrt 2 / 2)) ≠ ∞) :
    μ (ball 0 (Real.sqrt 2 / 2)) = 0 := by
  refine ball_measure_zero_of_separated μ hinv x (Real.sqrt 2 / 2) 1 (by positivity)
    ?_ ?_ hloc
  · intro i j hij
    rw [orthonormal_dist_eq_sqrt_two ho hij]
    exact le_of_eq (by ring)
  · intro i
    simp [dist_zero_right, ho.norm_eq_one i]

/-- **No nonzero locally-finite translation-invariant measure (impossibility).**
Given an orthonormal sequence, a translation-invariant measure that is both finite on
`B(0, 1+√2/2)` and *positive* on `B(0, √2/2)` is a contradiction — the hallmark of an
infinite-dimensional space having no analogue of Lebesgue measure. -/
theorem no_nondegenerate_translation_invariant_measure {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    (hinv : ∀ (v : E) (s : Set E), μ (v +ᵥ s) = μ s)
    {x : ℕ → E} (ho : Orthonormal ℝ x)
    (hloc : μ (ball 0 (1 + Real.sqrt 2 / 2)) ≠ ∞)
    (hpos : μ (ball 0 (Real.sqrt 2 / 2)) ≠ 0) : False :=
  hpos (ball_measure_zero_of_orthonormal μ hinv ho hloc)

end LebesgueMeasureOQ03WIP01
