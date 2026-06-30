import Mathlib
import Proofs.FourierDivergenceResonance

/-!
# Fourier Divergence via a Harmonic Lower Bound on the Lebesgue Constants

This file tightens the documented analytic gap for
`banach-steinhaus-theorem-oq-01-oq-01` (a continuous `2π`-periodic function with
Fourier series diverging at a point).

`Proofs/FourierDivergenceResonance.lean` already verifies the functional-analysis
core (the resonance principle: operator norms `‖Sₙ‖ → ∞` produce a resonating point).
That leaves the *asymptotic* analytic input `‖Sₙ‖ = ‖Dₙ‖_{L¹} → ∞` as the gap.

Here we reduce that asymptotic to a single **concrete inequality**: it suffices to
bound the operator norms below by a positive multiple of the harmonic partial sum
`Hₙ = ∑_{i<n} 1/(i+1)`. Mathlib already proves the harmonic series diverges
(`Real.tendsto_sum_range_one_div_nat_succ_atTop`), so

    (∃ c > 0, ∀ n, c · Hₙ ≤ ‖Sₙ‖)   ⟹   Fourier series of some `f ∈ C(𝕋)` diverges at 0.

This is exactly the shape the classical Lebesgue-constant estimate produces: the
standard lower bound is `‖Dₙ‖_{L¹} ≥ 4 ∑_{k=1}^{n} 1/(k+1) ≍ log n`, i.e. precisely
a positive multiple of `Hₙ`.  The remaining Mathlib gap is thus narrowed from "prove
an asymptotic limit" to "prove one harmonic lower bound on the Dirichlet `L¹` norm".

Everything here is fully verified — no `sorry`, no `axiom`.
-/

open Filter Topology Set

namespace FourierDivergenceLebesgueReduction

/-- The harmonic partial sum `Hₙ = ∑_{i < n} 1/(i+1)`, the elementary quantity that the
classical Lebesgue-constant lower bound `‖Dₙ‖_{L¹} ≥ c·Hₙ` is phrased against. -/
noncomputable def harmonic (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, (1 / (i + 1) : ℝ)

/-- The harmonic partial sums diverge to `+∞` (Mathlib's divergence of the harmonic
series, packaged under our local name). -/
theorem harmonic_tendsto_atTop : Tendsto harmonic atTop atTop :=
  Real.tendsto_sum_range_one_div_nat_succ_atTop

/-- **Harmonic bridge.** A real sequence bounded below by a positive multiple of the
harmonic partial sums tends to `+∞`. This is the elementary step that converts the
classical lower bound `c·Hₙ ≤ ‖Sₙ‖` into the hypothesis `‖Sₙ‖ → ∞` consumed by the
resonance principle. -/
theorem tendsto_atTop_of_harmonic_lower_bound {L : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hL : ∀ n, c * harmonic n ≤ L n) : Tendsto L atTop atTop :=
  tendsto_atTop_mono hL (Tendsto.const_mul_atTop hc harmonic_tendsto_atTop)

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Reduction of Fourier divergence to one harmonic lower bound.**

If the operator norms of `g n : E →L[𝕜] F` are bounded below by a positive multiple of
the harmonic partial sums, then some point `x : E` has an unbounded orbit
`{‖g n x‖}`.

Instantiating `E = C(𝕋)`, `g n = Sₙ` (the partial-sum-at-`0` functionals) and the
classical Lebesgue-constant lower bound `c·Hₙ ≤ ‖Sₙ‖` yields a continuous function
whose Fourier series diverges at `0`.  Combined with the verified resonance core, the
*only* remaining analytic obligation is the single inequality `c·Hₙ ≤ ‖Sₙ‖`. -/
theorem exists_unbounded_orbit_of_harmonic_lower_bound
    {g : ℕ → E →L[𝕜] F} {c : ℝ} (hc : 0 < c)
    (hlb : ∀ n, c * harmonic n ≤ ‖g n‖) :
    ∃ x, ¬ BddAbove (range fun n => ‖g n x‖) :=
  FourierDivergenceResonance.exists_unbounded_orbit_of_tendsto_norm_atTop
    (tendsto_atTop_of_harmonic_lower_bound hc hlb)

end FourierDivergenceLebesgueReduction
