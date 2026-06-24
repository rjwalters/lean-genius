/-
# Banach–Steinhaus Divergence Principle — the abstract engine of du Bois-Reymond

Open question: baire-category-theorem-oq-01-oq-01-oq-02
("Divergent Fourier Series via Banach–Steinhaus Resonance")

## What is proved here (fully verified, 0 axioms)

The parent file `BaireCategoryTheoremOQ01OQ01.lean` derives the Uniform
Boundedness Principle from the gallery Baire category theorem and packages its
contrapositive as
  `exists_resonance_of_not_uniformly_bounded`:
    a family of bounded operators with *unbounded operator norms* has a point of
    resonance `x` at which `sup_i ‖g i x‖ = ∞`.

This file turns *resonance* into *divergence*. The key observation is that a
convergent sequence in a normed space has bounded range, so a point of resonance
is automatically a point where the orbit `n ↦ T n x` **fails to converge**:

  `exists_divergent_orbit_of_unbounded_opNorm`:
    if `T : ℕ → E →L[𝕜] F` has unbounded operator norms, then there is `x` with
    `¬ ∃ L, Tendsto (fun n => T n x) atTop (𝓝 L)`.

Specialised to scalar functionals `S : ℕ → V →L[ℂ] ℂ` this is exactly the
abstract form of du Bois-Reymond's theorem:

  `exists_divergent_partialSums`:
    if the functionals `S n` have unbounded operator norms, there is a vector `f`
    at which the scalars `S n f` do not converge.

## The Fourier instantiation (du Bois-Reymond, 1873)

Take `V = C(𝕋)` (continuous functions on the circle, a Banach space under the
sup norm) and `S n f = (∑_{|k| ≤ n} \hat f(k))`, the `n`-th symmetric Fourier
partial sum evaluated at `0`. Each `S n` is a continuous linear functional, and
its operator norm equals the **Lebesgue constant**

  ‖S n‖ = L_n = (1 / 2π) ∫_{-π}^{π} |D_n(t)| dt,   D_n = Dirichlet kernel,

which grows like `L_n ∼ (4/π²) log n → ∞`. Feeding this unboundedness into
`exists_divergent_partialSums` yields a continuous function whose Fourier series
diverges at `0` — du Bois-Reymond's classical counterexample to the naive hope
that continuity forces pointwise Fourier convergence.

**Honesty note.** This file proves the Banach–Steinhaus *reduction* in full: the
hypothesis "the partial-sum functionals have unbounded operator norms" is taken
as an explicit hypothesis of `exists_divergent_partialSums`. The remaining
analytic input — that the Lebesgue constants `L_n` are unbounded, equivalently
that `∫ |D_n| → ∞` — is the classical fact that discharges that hypothesis. It is
**not** currently available in Mathlib (there is no Dirichlet kernel / Lebesgue
constant development), so the *unconditional* existence of a divergent-Fourier
continuous function is **not** claimed here. What is established is the abstract
divergence mechanism and the precise conditional statement; the unproved pieces
(Dirichlet kernel, `∫ |D_n| ≳ log n`, and the `C(𝕋) → ℂ` continuous-linear-functional
packaging of the partial sums) are recorded as the open follow-up.

## Main results
- `exists_bound_of_tendsto`                  : a convergent sequence is norm-bounded
- `exists_divergent_orbit_of_unbounded_opNorm`: unbounded op-norms ⟹ a non-convergent orbit
- `exists_divergent_orbit_unbounded`          : the same orbit is in fact unbounded
- `exists_divergent_partialSums`              : scalar (Fourier-shaped) form of the reduction

All results are fully machine-checked: no `sorry`, no extra axioms beyond
`propext`/`Classical.choice`/`Quot.sound`.
-/
import Mathlib
import Proofs.BaireCategoryTheoremOQ01OQ01

namespace BaireCategoryTheoremOQ01OQ01OQ02

open Filter Topology BaireCategoryTheoremOQ01OQ01

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A convergent sequence in a normed space has a uniform norm bound: if
`y n → L`, then `‖y n‖ ≤ C` for some `C` and all `n`. This is the elementary
fact that converts *resonance* (unbounded orbit) into *divergence* (no limit). -/
lemma exists_bound_of_tendsto {y : ℕ → F} {L : F}
    (h : Tendsto y atTop (𝓝 L)) : ∃ C, ∀ n, ‖y n‖ ≤ C := by
  have hb : Bornology.IsBounded (Set.range y) := Metric.isBounded_range_of_tendsto y h
  rw [isBounded_iff_forall_norm_le] at hb
  obtain ⟨C, hC⟩ := hb
  exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩

/-- **Banach–Steinhaus divergence principle.** If a sequence of bounded operators
`T : ℕ → E →L[𝕜] F` from a Banach space `E` has *unbounded* operator norms, then
there is a single point `x` at which the orbit `n ↦ T n x` does **not** converge.

This upgrades the parent's resonance statement: resonance only says the orbit is
unbounded, but unboundedness rules out convergence, which is the form needed for
divergence statements (such as divergent Fourier series). -/
theorem exists_divergent_orbit_of_unbounded_opNorm {T : ℕ → E →L[𝕜] F}
    (h : ¬ ∃ C, ∀ n, ‖T n‖ ≤ C) :
    ∃ x : E, ¬ ∃ L, Tendsto (fun n => T n x) atTop (𝓝 L) := by
  obtain ⟨x, hx⟩ := exists_resonance_of_not_uniformly_bounded h
  refine ⟨x, ?_⟩
  rintro ⟨L, hL⟩
  exact hx (exists_bound_of_tendsto hL)

/-- The resonance point of `exists_divergent_orbit_of_unbounded_opNorm` has, in
fact, an *unbounded* orbit: for every bound `C` some term `T n x` exceeds it.
This is the strong "divergence" witness (the orbit has no finite envelope). -/
theorem exists_divergent_orbit_unbounded {T : ℕ → E →L[𝕜] F}
    (h : ¬ ∃ C, ∀ n, ‖T n‖ ≤ C) :
    ∃ x : E, ∀ C : ℝ, ∃ n, C < ‖T n x‖ := by
  obtain ⟨x, hx⟩ := exists_resonance_of_not_uniformly_bounded h
  refine ⟨x, fun C => ?_⟩
  by_contra hcon
  push_neg at hcon
  exact hx ⟨C, hcon⟩

/-- **du Bois-Reymond reduction (abstract / conditional form).** For *any* family
of continuous linear functionals `S : ℕ → V →L[ℂ] ℂ` on a complex Banach space
`V` whose operator norms are unbounded, there is a vector `f` at which the
scalars `S n f` do not converge.

Reading `V = C(𝕋)` and `S n f = ∑_{|k| ≤ n} \hat f(k)` (the `n`-th Fourier
partial sum at `0`), the operator norms `‖S n‖` are the Lebesgue constants
`L_n ∼ (4/π²) log n → ∞`; the hypothesis `hUnbdd` is therefore the classical
fact that the Lebesgue constants are unbounded, and the conclusion is that some
continuous function has a divergent Fourier series at `0`. The Lebesgue-constant
growth is not yet formalised in Mathlib, so this conditional statement is the
faithful Banach–Steinhaus half of du Bois-Reymond's theorem. -/
theorem exists_divergent_partialSums {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (S : ℕ → V →L[ℂ] ℂ) (hUnbdd : ¬ ∃ C, ∀ n, ‖S n‖ ≤ C) :
    ∃ f : V, ¬ ∃ L, Tendsto (fun n => S n f) atTop (𝓝 L) :=
  exists_divergent_orbit_of_unbounded_opNorm hUnbdd

end BaireCategoryTheoremOQ01OQ01OQ02
