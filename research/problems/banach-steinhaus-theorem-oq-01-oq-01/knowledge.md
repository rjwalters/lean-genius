# Fourier Series Divergence via Uniform Boundedness (banach-steinhaus-theorem-oq-01-oq-01)

## Problem Summary

Formalize the classical application of the Banach–Steinhaus (uniform boundedness)
theorem: **there exists a continuous `2π`-periodic function whose Fourier series
diverges at a point.** The route is the resonance form of uniform boundedness applied
to the partial-sum-at-`0` functionals `Sₙ : C(𝕋) → ℂ`, using that their operator norms
— the Lebesgue constants `‖Sₙ‖ = ‖Dₙ‖_{L¹}` — tend to infinity.

## The Standard Proof (4 steps)

1. **Functionals.** For `f ∈ C(𝕋)` (continuous `2π`-periodic, sup norm), the `n`-th
   symmetric partial sum at `0` is `Sₙ f = ∑_{|k|≤n} f̂(k) = (1/2π)∫_{-π}^{π} f(t) Dₙ(t) dt`,
   where `Dₙ(t) = ∑_{|k|≤n} e^{ikt} = sin((n+½)t)/sin(t/2)` is the Dirichlet kernel.
   Each `Sₙ` is a bounded linear functional on the Banach space `C(𝕋)`.
2. **Operator norm = Lebesgue constant.** `‖Sₙ‖ = (1/2π)‖Dₙ‖_{L¹([-π,π])} =: Lₙ`
   (the supremum is attained in the limit by functions approximating `sgn Dₙ`).
3. **Lebesgue constants diverge.** `Lₙ = (4/π²) log n + O(1) → ∞`. The clean lower
   bound `Lₙ ≥ c·log n` comes from `∫|sin((n+½)t)/sin(t/2)| dt ≥ ∑_{k} (1/kπ)∫|sin| ≍ log n`.
4. **Resonance.** `C(𝕋)` is complete, so by the contrapositive of Banach–Steinhaus a
   family of functionals with `sup_n ‖Sₙ‖ = ∞` cannot be pointwise bounded: there is
   `f ∈ C(𝕋)` with `sup_n |Sₙ f| = ∞`, i.e. the Fourier series of `f` diverges at `0`.

## Mathlib Status (v4.26.0) — Gap Analysis

**Has:**
- `banach_steinhaus` — uniform boundedness principle for CLMs out of a complete space
  (`Mathlib.Analysis.Normed.Operator.BanachSteinhaus`).
- `fourierCoeff`, Fourier series on `AddCircle T`, `L²` convergence, Parseval
  (`Mathlib.Analysis.Fourier.AddCircle`).
- `C(X, ℂ)` / `BoundedContinuousFunction` as a Banach space (sup norm, complete).

**Lacks (the analytic core — the genuine blocker):**
- The **Dirichlet kernel** `Dₙ` and its closed form.
- The **partial-sum functionals `Sₙ` as bounded operators** on `C(𝕋)`, and the identity
  `‖Sₙ‖ = ‖Dₙ‖_{L¹}`.
- **Divergence of the Lebesgue constants** `‖Dₙ‖_{L¹} → ∞` (the `log n` lower bound).

Steps 1–3 are a real formalization project (estimating the `L¹` norm of `Dₙ` from
below by a logarithm is the crux). Step 4 is pure functional analysis and is the part
done here.

## Approach Taken — Verified Functional-Analysis Core (step 4)

`proofs/Proofs/FourierDivergenceResonance.lean` isolates and proves the resonance
principle that step 4 needs, in reusable abstract form:

- `exists_unbounded_orbit_of_not_bddAbove_norm` — contrapositive of `banach_steinhaus`:
  CLMs `g i : E →L[𝕜] F` on a Banach space `E` with `{‖g i‖}` unbounded above ⟹ some
  `x` has `{‖g i x‖}` unbounded above.
- `exists_unbounded_orbit_of_tendsto_norm_atTop` — sequential corollary: `‖g n‖ → ∞`
  ⟹ some `x` has unbounded orbit. This is exactly what consumes the Lebesgue-constant
  divergence: instantiate `E = C(𝕋)`, `g n = Sₙ`, `‖g n‖ = Lₙ → ∞` to get a continuous
  `f` with divergent Fourier series at `0`.

Mirrors the "reduce to an explicit hypothesis, don't axiomatize" pattern: the verified
core is the resonance principle; the missing analysis (`Lₙ → ∞`) is documented, not
assumed inside an axiom.

### Lean notes
- Contrapositive via `by_contra` + `push_neg` turns the goal into the pointwise-bounded
  hypothesis of `banach_steinhaus`; repackage `BddAbove (range …)` ↔ `∃ C, ∀ i, … ≤ C`
  with `mem_range_self` / `rintro ⟨i, rfl⟩`.
- Sequential corollary: `‖g n‖ → ∞` contradicts any bound `C` via
  `(h.eventually_gt_atTop C).exists`.

## Session 2026-06-26 (Session 1)

**Mode:** FRESH (EMPTY tier; prior `problem.md`/`state.md` present but phase NEW, 0 attempts).
**Outcome:** progress — verified resonance core drafted; analytic core (Lebesgue
constants) BLOCKED on missing Mathlib infrastructure.

**BUILD STATUS:** VERIFIED — `./proofs/scripts/docker-build.sh
Proofs.FourierDivergenceResonance` → Build succeeded (1787 jobs), 0 sorries, 0 axioms.
(The build host was transiently unstable mid-session — Docker Desktop OOM-killed
containers when its VM dropped to 7.65 GiB; resolved after a clean restart returned the
VM to 23 GiB.) Gallery `meta.json` added (status `verified`, scoped to the
functional-analysis core only).

### Next Steps
1. Build the analytic core in Mathlib/local file: Dirichlet kernel `Dₙ`, the operator
   `Sₙ` on `C(𝕋)`, `‖Sₙ‖ = ‖Dₙ‖_{L¹}`, and the `log n` lower bound `Lₙ → ∞`.
3. Compose: `exists_unbounded_orbit_of_tendsto_norm_atTop` + `Lₙ → ∞` ⟹ continuous
   function with Fourier series diverging at `0`.
4. Candidate Aristotle target: the Lebesgue-constant lower bound
   `∫_{-π}^{π} |sin((n+½)t)/sin(t/2)| dt ≥ c·log n`.
