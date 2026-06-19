/-
# Simultaneous Dirichlet Approximation (OQ-02 of `dirichlet-approximation-theorem`)

**Open Question.** The parent entry `DirichletApproximation` proves the classical
one-dimensional pigeonhole statement: for every real `α` and every `Q ≥ 1` there is a
fraction `p/q` with `1 ≤ q ≤ Q` and `|qα − p| < 1/Q`. This file proves the
**simultaneous** (higher-dimensional) generalization, which is the form needed in the
geometry of numbers and in the theory of badly approximable systems:

> For real numbers `θ₁, …, θ_d` and every `Q ≥ 1`, there is a single common
> denominator `q` with `1 ≤ q ≤ Q^d` and integers `p₁, …, p_d` such that
> `|q·θᵢ − pᵢ| ≤ 1/Q` for **all** `i` simultaneously.

The one common `q` works for all `d` coordinates at once — that simultaneity is the whole
point, and it costs only an enlargement of the denominator range from `Q` to `Q^d`.

## Strategy — pigeonhole on the `d`-torus, via Mathlib's abstract Dirichlet theorem

The parent file pigeonholes `Q+1` points of `ℝ/ℤ` into `Q` arcs by hand. Here we instead
recognize the simultaneous statement as Mathlib's general
`NormedAddCommGroup.exists_norm_nsmul_le` — Dirichlet's theorem for an arbitrary compact,
connected, normed additive group with a Haar measure — specialized to the `d`-torus
`𝕋^d = (Fin d → AddCircle 1)`:

* Let `ξ : Fin d → AddCircle 1`, `ξ i = θ i mod 1`. The supremum norm of `q • ξ` is the
  largest distance of any `q·θᵢ` to its nearest integer.
* The abstract theorem produces `q ∈ [1, Q^d]` with `‖q • ξ‖ ≤ 1/Q`, provided the
  measure inequality `vol(𝕋^d) ≤ (Q^d + 1) · vol(closedBall 0 (1/2Q))` holds.
* That inequality is the clean product computation `1 ≤ (Q^d + 1)·(1/Q)^d = 1 + 1/Q^d`,
  using `volume_pi_closedBall`, `AddCircle.volume_closedBall` and `UnitAddCircle.measure_univ`.
* Reading off `pᵢ := round (q·θᵢ)` and using `AddCircle.norm_eq` (`‖x‖ = |x − round x|`)
  together with `norm_le_pi_norm` turns `‖q • ξ‖ ≤ 1/Q` into the coordinatewise bound.

Everything is `sorry`-free and `axiom`-free (only the foundational
`propext`/`Classical.choice`/`Quot.sound`; no `Lean.ofReduceBool`).
-/
import Mathlib

namespace DirichletApproximationOQ02

open MeasureTheory Metric Set
open scoped ENNReal

attribute [local instance] Real.fact_zero_lt_one

/-- **Simultaneous Dirichlet approximation.** For real numbers `θ₀, …, θ_{d-1}` and any
`Q ≥ 1`, there is a single denominator `q` with `1 ≤ q ≤ Q^d` and integers `pᵢ` such that
`|q·θᵢ − pᵢ| ≤ 1/Q` for every coordinate `i` at once. -/
theorem simultaneous_dirichlet_approximation
    {d : ℕ} (θ : Fin d → ℝ) {Q : ℕ} (hQ : 0 < Q) :
    ∃ (p : Fin d → ℤ) (q : ℕ), 1 ≤ q ∧ q ≤ Q ^ d ∧
      ∀ i, |(q : ℝ) * θ i - (p i : ℝ)| ≤ 1 / Q := by
  classical
  -- The point of the `d`-torus whose coordinates are the `θ i` reduced mod 1.
  set ξ : Fin d → AddCircle (1 : ℝ) := fun i => ((θ i : ℝ) : AddCircle (1 : ℝ)) with hξ
  set δ : ℝ := 1 / Q with hδdef
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hδpos : 0 < δ := by positivity
  have hδle1 : δ ≤ 1 := by
    rw [hδdef, div_le_one hQR]; exact_mod_cast hQ
  have hn : 0 < Q ^ d := pow_pos hQ d
  -- The measure hypothesis of the abstract Dirichlet theorem on the `d`-torus.
  have hmeas : volume (univ : Set (Fin d → AddCircle (1 : ℝ)))
      ≤ (Q ^ d + 1) • volume (closedBall (0 : Fin d → AddCircle (1 : ℝ)) (δ / 2)) := by
    -- Total mass of the torus is `1`.
    have huniv : volume (univ : Set (Fin d → AddCircle (1 : ℝ))) = 1 := by
      rw [volume_pi, Measure.pi_univ]
      simp [UnitAddCircle.measure_univ]
    -- Volume of the sup-norm closed ball of radius `δ/2` is `(ofReal δ)^d`.
    have hc : volume (closedBall (0 : AddCircle (1 : ℝ)) (δ / 2)) = ENNReal.ofReal δ := by
      rw [AddCircle.volume_closedBall]
      congr 1
      have h2 : (2 : ℝ) * (δ / 2) = δ := by ring
      rw [h2, min_eq_right hδle1]
    have hball : volume (closedBall (0 : Fin d → AddCircle (1 : ℝ)) (δ / 2))
        = ENNReal.ofReal δ ^ d := by
      rw [volume_pi_closedBall _ (by positivity)]
      simp [Pi.zero_apply, hc]
    rw [huniv, hball]
    -- `1 ≤ (Q^d + 1) • (ofReal δ)^d = ofReal ((Q^d+1)/Q^d) = ofReal (1 + 1/Q^d)`.
    rw [← ENNReal.ofReal_pow hδpos.le, nsmul_eq_mul]
    have hδpow : δ ^ d = 1 / (Q : ℝ) ^ d := by rw [hδdef, div_pow, one_pow]
    rw [hδpow, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.one_le_ofReal, Nat.cast_add, Nat.cast_pow, Nat.cast_one, mul_one_div,
      le_div_iff₀ (by positivity : (0 : ℝ) < (Q : ℝ) ^ d), one_mul]
    linarith
  -- Apply the abstract Dirichlet theorem.
  obtain ⟨q, hq_mem, hq_norm⟩ :=
    NormedAddCommGroup.exists_norm_nsmul_le (μ := volume) ξ hn δ hmeas
  rw [Set.mem_Icc] at hq_mem
  refine ⟨fun i => round ((q : ℝ) * θ i), q, hq_mem.1, hq_mem.2, fun i => ?_⟩
  -- The `i`-th coordinate of `q • ξ` is `↑(q·θᵢ)` in `AddCircle 1`.
  have h1 : (q • ξ) i = (((q : ℝ) * θ i : ℝ) : AddCircle (1 : ℝ)) := by
    show q • (ξ i) = _
    simp only [hξ]
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  -- Its norm is the distance of `q·θᵢ` to the nearest integer, witnessed by `round`.
  have h2 : ‖(q • ξ) i‖ = |(q : ℝ) * θ i - (round ((q : ℝ) * θ i) : ℝ)| := by
    rw [h1, AddCircle.norm_eq]
    simp only [inv_one, one_mul, mul_one]
  calc |(q : ℝ) * θ i - (round ((q : ℝ) * θ i) : ℝ)|
      = ‖(q • ξ) i‖ := h2.symm
    _ ≤ ‖q • ξ‖ := norm_le_pi_norm _ i
    _ ≤ δ := hq_norm

end DirichletApproximationOQ02
