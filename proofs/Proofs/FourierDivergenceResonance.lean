import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Resonance Principle for Fourier Series Divergence (functional-analysis core)

## The Target

A classical application of the Banach–Steinhaus theorem (uniform boundedness
principle): **there exists a continuous `2π`-periodic function whose Fourier series
diverges at a point.** The standard proof considers the partial-sum-at-`0`
functionals `Sₙ : C(𝕋) → ℂ`, `Sₙ f = (Sₙf)(0) = ∫ f · Dₙ` (`Dₙ` the Dirichlet
kernel), observes that `‖Sₙ‖ = ‖Dₙ‖_{L¹}` (the *Lebesgue constants*) and that
`‖Dₙ‖_{L¹} → ∞`, and then invokes uniform boundedness in its contrapositive form: a
sequence of bounded functionals whose operator norms are unbounded must have a point
of **resonance** — a function `f` whose orbit `‖Sₙ f‖` is unbounded, i.e. whose
Fourier series diverges at `0`.

## What This File Provides (fully verified, no `sorry`, no `axiom`)

Mathlib has the Banach–Steinhaus theorem (`banach_steinhaus`) but **not** the
Dirichlet kernel, the Lebesgue constants, or their divergence. This file isolates and
verifies the **functional-analysis core** of the divergence argument — the resonance
principle — in a form ready to be applied once the analytic input `‖Dₙ‖_{L¹} → ∞`
is available:

* `exists_unbounded_orbit_of_not_bddAbove_norm` — the **contrapositive of uniform
  boundedness**: for continuous linear maps `g i : E →L[𝕜] F` on a Banach space `E`,
  if the operator norms `{‖g i‖}` are not bounded above, then there is a point `x`
  whose orbit `{‖g i x‖}` is not bounded above.
* `exists_unbounded_orbit_of_tendsto_norm_atTop` — the sequential corollary used in
  the Fourier application: if `‖g n‖ → ∞`, then some `x` has unbounded orbit.

Applying the second result with `E = C(𝕋)`, `g n = Sₙ`, and the (still-missing in
Mathlib) fact `‖Sₙ‖ = ‖Dₙ‖_{L¹} → ∞` immediately yields a continuous function with
divergent Fourier series at `0`. The only gap is the analytic estimate on the
Lebesgue constants; the functional-analysis half is complete and machine-checked.

## Mathlib Dependencies

- `banach_steinhaus` : pointwise-bounded family of CLMs on a Banach space is
  uniformly norm-bounded (`Mathlib.Analysis.Normed.Operator.BanachSteinhaus`)
- `Filter.Tendsto.eventually_gt_atTop` : `f → ∞` eventually exceeds any constant

## Status

`verified` — every declaration is machine-checked with no `sorry` and no `axiom`.
The full Fourier-divergence theorem is *not* claimed; see
`research/problems/banach-steinhaus-theorem-oq-01-oq-01/knowledge.md`.
-/

open Filter Topology Set

namespace FourierDivergenceResonance

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Resonance principle** (contrapositive of the uniform boundedness principle).

If a family of continuous linear maps `g i : E →L[𝕜] F` out of a Banach space `E` has
operator norms `{‖g i‖}` that are *not* bounded above, then there exists a single
point `x : E` whose orbit `{‖g i x‖}` is *not* bounded above.

This is exactly the form of Banach–Steinhaus used to produce a continuous function
with divergent Fourier series: unbounded Lebesgue constants force a resonating `f`. -/
theorem exists_unbounded_orbit_of_not_bddAbove_norm {ι : Type*}
    {g : ι → E →L[𝕜] F} (h : ¬ BddAbove (range fun i => ‖g i‖)) :
    ∃ x, ¬ BddAbove (range fun i => ‖g i x‖) := by
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ x, BddAbove (range fun i => ‖g i x‖)` — the family is pointwise bounded.
  apply h
  -- Repackage pointwise boundedness in the shape `banach_steinhaus` expects.
  have hpt : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C := by
    intro x
    obtain ⟨C, hC⟩ := hcon x
    exact ⟨C, fun i => hC (mem_range_self i)⟩
  -- Uniform boundedness then bounds the operator norms.
  obtain ⟨C', hC'⟩ := banach_steinhaus hpt
  exact ⟨C', by rintro _ ⟨i, rfl⟩; exact hC' i⟩

/-- Sequential form of the resonance principle, as used for Fourier divergence: if the
operator norms of `g n : E →L[𝕜] F` tend to infinity, some point `x` has an unbounded
orbit `{‖g n x‖}`. -/
theorem exists_unbounded_orbit_of_tendsto_norm_atTop
    {g : ℕ → E →L[𝕜] F} (h : Tendsto (fun n => ‖g n‖) atTop atTop) :
    ∃ x, ¬ BddAbove (range fun n => ‖g n x‖) := by
  refine exists_unbounded_orbit_of_not_bddAbove_norm ?_
  rintro ⟨C, hC⟩
  -- `hC` bounds every `‖g n‖` by `C`, contradicting `‖g n‖ → ∞`.
  obtain ⟨n, hn⟩ := (h.eventually_gt_atTop C).exists
  exact absurd (hC (mem_range_self n)) (not_le.2 hn)

end FourierDivergenceResonance
