/-
# Hilbert's 23rd Problem (Calculus of Variations) — OQ-01: Regularity / sufficiency theory

The parent entry `hilbert-23` sketches the calculus of variations as a research
program and lists, as its first open question, *"What is the regularity theory for
general variational problems?"*. The classical first‑order theory answers a clean,
self‑contained slice of this: for a **convex** functional `J` the Euler–Lagrange /
first‑variation condition is not merely *necessary* for a minimizer (the usual
necessary condition) but also *sufficient*, and strict convexity upgrades this to a
**uniqueness** statement.

This file proves that package with **zero axioms**, working over an arbitrary real
vector space `E` (no norm, no measure theory required):

* `firstVariation_le_sub` — the convexity engine: the one‑sided directional
  derivative of `J` at `y₀` toward `y` is at most `J y - J y₀`.
* `firstVariation_nonneg_of_isMinOn` — **necessity**: at a minimizer every first
  variation is `≥ 0`.
* `isMinOn_of_firstVariation_nonneg` — **sufficiency**: if `J` is convex and every
  first variation at `y₀` is `≥ 0`, then `y₀` is a global minimizer.
* `isMinOn_iff_firstVariation_nonneg` — the resulting necessary‑and‑sufficient
  first‑order characterization for convex variational problems.
* `subsingleton_minimizers_of_strictConvex` — strict convexity ⇒ the minimizer is
  unique.
* A concrete instance (`example_*`) on `J y = y^2`.

The "first variation" of `J` at `y₀` in the direction of `y` is the right‑hand
derivative at `t = 0` of the path `t ↦ J(y₀ + t·(y - y₀))`; for a convex `J` this is
the Gateaux derivative restricted to admissible directions.  All proofs go through
Mathlib's convexity slope monotonicity, so the entry is fully machine‑checked.
-/
import Mathlib

open Set Filter Topology

namespace Hilbert23OQ01

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The variational path from `y₀` toward `y`: `φ(t) = J(y₀ + t·(y - y₀))`.
Its right derivative at `0` is the first variation of `J` at `y₀` in direction
`y - y₀`. -/
noncomputable def segPath (J : E → ℝ) (y₀ y : E) : ℝ → ℝ :=
  fun t => J (y₀ + t • (y - y₀))

@[simp] lemma segPath_zero (J : E → ℝ) (y₀ y : E) : segPath J y₀ y 0 = J y₀ := by
  simp [segPath]

/-- The path point is the convex combination `(1 - t)·y₀ + t·y`. -/
lemma segPath_eq_combo (J : E → ℝ) (y₀ y : E) (t : ℝ) :
    segPath J y₀ y t = J ((1 - t) • y₀ + t • y) := by
  unfold segPath
  congr 1
  module

/-- **Convexity engine.** For a convex functional `J`, the first variation `d` of `J`
at `y₀` toward `y` (the right derivative of `segPath J y₀ y` at `0`) is bounded above
by the actual change in value `J y - J y₀`.  This is the quantitative form of "the
tangent line of a convex function lies below it." -/
lemma firstVariation_le_sub {J : E → ℝ} (hJ : ConvexOn ℝ univ J)
    {y₀ y : E} {d : ℝ}
    (hd : HasDerivWithinAt (segPath J y₀ y) d (Ici 0) 0) :
    d ≤ J y - J y₀ := by
  -- Convexity gives, for every `t ∈ (0,1]`, a slope bound.
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      segPath J y₀ y t - J y₀ ≤ t * (J y - J y₀) := by
    intro t ht ht1
    rw [segPath_eq_combo]
    have hc := hJ.2 (mem_univ y₀) (mem_univ y)
      (show (0:ℝ) ≤ 1 - t by linarith) (show (0:ℝ) ≤ t from le_of_lt ht)
      (show (1 - t) + t = 1 by ring)
    simp only [smul_eq_mul] at hc
    nlinarith [hc]
  -- Pass to the limit `t → 0⁺`: the right derivative is `≤` every such slope bound.
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_diff_left] at hd
  refine le_of_tendsto hd ?_
  have hlt1 : ∀ᶠ t in 𝓝[Ioi (0:ℝ)] 0, t < 1 := by
    have hmem : Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) := isOpen_Iio.mem_nhds (by norm_num)
    filter_upwards [nhdsWithin_le_nhds hmem] with t ht using ht
  filter_upwards [hlt1, self_mem_nhdsWithin] with t ht1 ht0
  have ht0' : 0 < t := ht0
  rw [slope_def_field, segPath_zero, sub_zero]
  rw [div_le_iff₀ ht0', mul_comm]
  exact key t ht0' (le_of_lt ht1)

/-- **Necessity (Euler–Lagrange necessary condition).** If `y₀` is a global minimizer
of `J`, then every first variation of `J` at `y₀` is nonnegative. -/
lemma firstVariation_nonneg_of_isMinOn {J : E → ℝ} {y₀ y : E} {d : ℝ}
    (hmin : ∀ z, J y₀ ≤ J z)
    (hd : HasDerivWithinAt (segPath J y₀ y) d (Ici 0) 0) :
    0 ≤ d := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_diff_left] at hd
  refine ge_of_tendsto hd ?_
  filter_upwards [self_mem_nhdsWithin] with t ht0
  have ht0' : 0 < t := ht0
  rw [slope_def_field, segPath_zero, sub_zero]
  apply div_nonneg _ (le_of_lt ht0')
  have h := hmin (y₀ + t • (y - y₀))
  simpa [segPath] using sub_nonneg.mpr h

/-- **Sufficiency.** For a convex functional `J`, if at `y₀` every first variation
exists and is nonnegative, then `y₀` is a global minimizer.  This is the variational
sufficiency theorem: for convex problems the first‑order condition is enough. -/
theorem isMinOn_of_firstVariation_nonneg {J : E → ℝ} (hJ : ConvexOn ℝ univ J) {y₀ : E}
    (hcrit : ∀ y, ∃ d, HasDerivWithinAt (segPath J y₀ y) d (Ici 0) 0 ∧ 0 ≤ d) :
    ∀ y, J y₀ ≤ J y := by
  intro y
  obtain ⟨d, hd, hd0⟩ := hcrit y
  have := firstVariation_le_sub hJ hd
  linarith

/-- **First‑order characterization of minimizers for convex variational problems.**
Assume `J` is convex and Gateaux‑differentiable at `y₀` along every admissible
direction.  Then `y₀` is a global minimizer **iff** every first variation of `J` at
`y₀` is nonnegative — the necessary‑and‑sufficient Euler–Lagrange condition. -/
theorem isMinOn_iff_firstVariation_nonneg {J : E → ℝ} (hJ : ConvexOn ℝ univ J) {y₀ : E}
    (hdiff : ∀ y, ∃ d, HasDerivWithinAt (segPath J y₀ y) d (Ici 0) 0) :
    (∀ y, J y₀ ≤ J y) ↔
      (∀ y d, HasDerivWithinAt (segPath J y₀ y) d (Ici 0) 0 → 0 ≤ d) := by
  constructor
  · intro hmin y d hd
    exact firstVariation_nonneg_of_isMinOn hmin hd
  · intro hcrit y
    obtain ⟨d, hd⟩ := hdiff y
    have hle := firstVariation_le_sub hJ hd
    have hge := hcrit y d hd
    linarith

/-- **Uniqueness (regularity from strict convexity).** A strictly convex functional has
at most one global minimizer.  Combined with the sufficiency theorem above, this is the
classical statement that strictly convex variational problems are well‑posed: any
solution of the Euler–Lagrange equation is *the* minimizer. -/
theorem subsingleton_minimizers_of_strictConvex {J : E → ℝ}
    (hJ : StrictConvexOn ℝ univ J) {a b : E}
    (ha : ∀ z, J a ≤ J z) (hb : ∀ z, J b ≤ J z) : a = b := by
  by_contra hne
  have hlt := hJ.2 (mem_univ a) (mem_univ b) hne
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  simp only [smul_eq_mul] at hlt
  have hmid : J a ≤ J ((1/2 : ℝ) • a + (1/2 : ℝ) • b) := ha _
  have hab : J a = J b := le_antisymm (ha b) (hb a)
  linarith

/-! ## A concrete instance: the energy `J y = y²`

The simplest variational problem: minimize `J y = y²` over `ℝ`.  It is strictly
convex, its unique minimizer is `0`, and the first‑order characterization applies. -/

/-- `J y = y²` is convex on all of `ℝ`. -/
theorem example_convex : ConvexOn ℝ univ (fun y : ℝ => y ^ 2) :=
  (Even.strictConvexOn_pow (n := 2) ⟨1, by ring⟩ (by norm_num)).convexOn

/-- `J y = y²` is strictly convex on all of `ℝ`. -/
theorem example_strictConvex : StrictConvexOn ℝ univ (fun y : ℝ => y ^ 2) :=
  Even.strictConvexOn_pow (n := 2) ⟨1, by ring⟩ (by norm_num)

/-- `0` is a global minimizer of `J y = y²`. -/
theorem example_zero_isMin : ∀ z : ℝ, (fun y : ℝ => y ^ 2) 0 ≤ (fun y : ℝ => y ^ 2) z := by
  intro z; dsimp only; nlinarith [sq_nonneg z]

/-- The minimizer of `J y = y²` is unique: it is exactly `0`. -/
theorem example_unique_minimizer {a : ℝ}
    (ha : ∀ z : ℝ, (fun y : ℝ => y ^ 2) a ≤ (fun y : ℝ => y ^ 2) z) : a = 0 :=
  subsingleton_minimizers_of_strictConvex example_strictConvex ha example_zero_isMin

end Hilbert23OQ01
