/-
Uniform Dirichlet-kernel bounds away from the singularities

Source: Open question from the de-moivre gallery family (de-moivre-oq-06-oq-02)
Status: VERIFIED (0 axioms, 0 sorries)

The parent file `DeMoivreOQ06` establishes the *pointwise* Dirichlet-kernel
estimates

      |∑_{k=0}^{n} cos(kθ) − 1/2| ≤ 1/(2|sin(θ/2)|)          (`dirichlet_kernel_bound`)
      |∑_{k=0}^{n} sin(kθ)|       ≤ 1/|sin(θ/2)|             (`dirichlet_conjugate_bound`)

valid for each fixed `θ` with `sin(θ/2) ≠ 0`.  These bounds blow up as `θ → 0`
(mod `2π`).  The *classical* form used in Fourier analysis — the one that powers
Dirichlet's test for the uniform convergence of Fourier series — is the estimate
made **uniform in both `n` and `θ`** on a compact interval bounded away from the
singularities `θ ∈ 2πℤ`.

This file supplies that uniform estimate.  The geometric heart is the elementary
monotonicity fact that, on the arc `θ ∈ [δ, 2π − δ]` (with `0 < δ ≤ π`), the
half-angle sine is bounded below by its endpoint value:

      sin(θ/2) ≥ sin(δ/2) > 0.

Feeding this into the pointwise bounds removes the `θ`-dependence and yields a
single constant `C = 1/sin(δ/2)` controlling *all* partial sums simultaneously.

## Main results

* `sin_half_ge_of_mem_arc` — the endpoint lower bound `sin(δ/2) ≤ sin(θ/2)`.
* `dirichlet_kernel_uniform_bound` — cosine partial sums bounded by `1/(2 sin(δ/2))`,
  uniformly in `n` and in `θ ∈ [δ, 2π − δ]`.
* `dirichlet_conjugate_uniform_bound` — sine partial sums bounded by `1/sin(δ/2)`.
* `dirichlet_partial_sums_uniformly_bounded` — the packaged `∃ C, ∀ n θ` statement:
  a single constant simultaneously bounds every cosine and sine partial sum on the arc.
-/

import Proofs.DeMoivreOQ06
import Mathlib.Tactic

open Finset

namespace DeMoivreOQ06OQ02

/-- **Half-angle sine is bounded below by its endpoint value on the arc.**
For `0 < δ ≤ π` and `θ ∈ [δ, 2π − δ]` we have `sin(δ/2) ≤ sin(θ/2)`.

The half-angle `θ/2` ranges over `[δ/2, π − δ/2]`, on which `sin` attains its
minimum `sin(δ/2)` at both endpoints.  The proof clears the difference through
the product identity `sin x − sin y = 2 sin((x−y)/2) cos((x+y)/2)`; both factors
are nonnegative because their arguments lie in `[0, π/2]`. -/
theorem sin_half_ge_of_mem_arc (δ θ : ℝ) (hδ0 : 0 < δ) (hδπ : δ ≤ Real.pi)
    (hθ1 : δ ≤ θ) (hθ2 : θ ≤ 2 * Real.pi - δ) :
    Real.sin (δ / 2) ≤ Real.sin (θ / 2) := by
  have hpi := Real.pi_pos
  -- Difference of sines as a product.
  have hkey : Real.sin (θ / 2) - Real.sin (δ / 2)
      = 2 * Real.sin ((θ / 2 - δ / 2) / 2) * Real.cos ((θ / 2 + δ / 2) / 2) :=
    Real.sin_sub_sin (θ / 2) (δ / 2)
  -- First factor: sin of an argument in [0, π/2] ⊆ [0, π].
  have hsin : 0 ≤ Real.sin ((θ / 2 - δ / 2) / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;> [linarith; nlinarith]
  -- Second factor: cos of an argument in [-π/2, π/2].
  have hcos : 0 ≤ Real.cos ((θ / 2 + δ / 2) / 2) := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> nlinarith
  nlinarith [hkey, hsin, hcos, mul_nonneg hsin hcos]

/-- `sin(δ/2) > 0` for `0 < δ ≤ π`, recorded once for reuse. -/
private theorem sin_half_pos (δ : ℝ) (hδ0 : 0 < δ) (hδπ : δ ≤ Real.pi) :
    0 < Real.sin (δ / 2) := by
  have hpi := Real.pi_pos
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

/-- **Uniform Dirichlet-kernel bound (cosine form).**
On the arc `θ ∈ [δ, 2π − δ]` the cosine partial sums are bounded by the single
constant `1/(2 sin(δ/2))`, uniformly in `n` and `θ`.  This is the estimate that
makes Dirichlet's kernel a *uniformly bounded* approximate identity away from the
origin. -/
theorem dirichlet_kernel_uniform_bound (δ θ : ℝ) (hδ0 : 0 < δ) (hδπ : δ ≤ Real.pi)
    (hθ1 : δ ≤ θ) (hθ2 : θ ≤ 2 * Real.pi - δ) (n : ℕ) :
    |(∑ k ∈ Finset.range (n + 1), Real.cos ((k : ℝ) * θ)) - 1 / 2|
      ≤ 1 / (2 * Real.sin (δ / 2)) := by
  have hδpos : 0 < Real.sin (δ / 2) := sin_half_pos δ hδ0 hδπ
  have hθge : Real.sin (δ / 2) ≤ Real.sin (θ / 2) := sin_half_ge_of_mem_arc δ θ hδ0 hδπ hθ1 hθ2
  have hθpos : 0 < Real.sin (θ / 2) := lt_of_lt_of_le hδpos hθge
  -- Pointwise bound from the parent file.
  have hbound := DeMoivreOQ06.dirichlet_kernel_bound θ (ne_of_gt hθpos) n
  -- The pointwise denominator dominates the uniform one.
  have habs : |Real.sin (θ / 2)| = Real.sin (θ / 2) := abs_of_pos hθpos
  rw [habs] at hbound
  have hmono : 1 / (2 * Real.sin (θ / 2)) ≤ 1 / (2 * Real.sin (δ / 2)) := by
    apply one_div_le_one_div_of_le
    · positivity
    · linarith
  exact le_trans hbound hmono

/-- **Uniform conjugate Dirichlet-kernel bound (sine form).**
On the arc `θ ∈ [δ, 2π − δ]` the sine partial sums are bounded by `1/sin(δ/2)`,
uniformly in `n` and `θ`. -/
theorem dirichlet_conjugate_uniform_bound (δ θ : ℝ) (hδ0 : 0 < δ) (hδπ : δ ≤ Real.pi)
    (hθ1 : δ ≤ θ) (hθ2 : θ ≤ 2 * Real.pi - δ) (n : ℕ) :
    |∑ k ∈ Finset.range (n + 1), Real.sin ((k : ℝ) * θ)|
      ≤ 1 / Real.sin (δ / 2) := by
  have hδpos : 0 < Real.sin (δ / 2) := sin_half_pos δ hδ0 hδπ
  have hθge : Real.sin (δ / 2) ≤ Real.sin (θ / 2) := sin_half_ge_of_mem_arc δ θ hδ0 hδπ hθ1 hθ2
  have hθpos : 0 < Real.sin (θ / 2) := lt_of_lt_of_le hδpos hθge
  have hbound := DeMoivreOQ06.dirichlet_conjugate_bound θ (ne_of_gt hθpos) n
  have habs : |Real.sin (θ / 2)| = Real.sin (θ / 2) := abs_of_pos hθpos
  rw [habs] at hbound
  have hmono : 1 / Real.sin (θ / 2) ≤ 1 / Real.sin (δ / 2) :=
    one_div_le_one_div_of_le hδpos hθge
  exact le_trans hbound hmono

/-- **Packaged uniform boundedness of Dirichlet partial sums.**
There is a *single* positive constant `C` (depending only on `δ`) that
simultaneously bounds every cosine partial sum (centred at `1/2`) and every sine
partial sum, for all `n` and all `θ ∈ [δ, 2π − δ]`.  This is the quantitative
input to Dirichlet's convergence test.  We take `C = 1/sin(δ/2)`, which dominates
the cosine constant `1/(2 sin(δ/2))`. -/
theorem dirichlet_partial_sums_uniformly_bounded (δ : ℝ) (hδ0 : 0 < δ) (hδπ : δ ≤ Real.pi) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (θ : ℝ), δ ≤ θ → θ ≤ 2 * Real.pi - δ →
      |(∑ k ∈ Finset.range (n + 1), Real.cos ((k : ℝ) * θ)) - 1 / 2| ≤ C ∧
      |∑ k ∈ Finset.range (n + 1), Real.sin ((k : ℝ) * θ)| ≤ C := by
  have hδpos : 0 < Real.sin (δ / 2) := sin_half_pos δ hδ0 hδπ
  refine ⟨1 / Real.sin (δ / 2), by positivity, ?_⟩
  intro n θ hθ1 hθ2
  constructor
  · -- cosine bound: 1/(2 sin) ≤ 1/sin
    have hcos := dirichlet_kernel_uniform_bound δ θ hδ0 hδπ hθ1 hθ2 n
    have hle : 1 / (2 * Real.sin (δ / 2)) ≤ 1 / Real.sin (δ / 2) :=
      one_div_le_one_div_of_le hδpos (by linarith)
    exact le_trans hcos hle
  · exact dirichlet_conjugate_uniform_bound δ θ hδ0 hδπ hθ1 hθ2 n

end DeMoivreOQ06OQ02
