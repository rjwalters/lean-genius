# Research State: shapley-folkman-oq-01

## Current State
**Phase**: OBSERVE (S1 doc-only survey complete; shortlist of 1
viable + 2 deferred S2 ACT targets in
`sessions/2026-05-12-s01-observe.md`)
**Path**: full
**Since**: 2026-05-12
**Last Updated**: 2026-05-12 (Session 1, researcher-1)
**Iteration**: 1

## Session 1 — S1 OBSERVE: literal extension fails; Aumann/Lyapunov are the correct infinite-dim analogs (researcher-1, 2026-05-12)

**Mode.** Doc-only (no `.lean` changes).

**Outcome.** Filled the seeker-init template. The seeker note
suggested "finrank → suitable dimension"; this session establishes
that **no drop-in replacement exists**, and that the correct
infinite-dim analogs are Aumann's set-valued integral (1965) and
Lyapunov's convexity theorem (1940) — neither of which is in
Mathlib.

**Key findings:**

1. **`Module.finrank ℝ ℓ² = 0` collapses the bound.**
   In Lean's convention, `Module.finrank` of any non-finite-dim
   module is `0`. The literal extension `at most finrank ℝ E
   excess indices` becomes `at most 0 excess indices`, which is
   vacuously false for any Minkowski sum with non-convex
   summands.

2. **The Carathéodory step inside `shapley_folkman` is genuinely
   finite-dim.** The proof at `ShapleyFolkman.lean:151–199`
   uses `excess_vertices_affine_dependent` which depends
   essentially on `Module.finrank ℝ E + 1 < n ⟹ AffineDependent`.
   In infinite-dim, `AffineIndependent` can hold for arbitrarily
   large index sets, so the affine-dependent extraction step
   has no analog.

3. **The CORRECT infinite-dim analog is Aumann's theorem
   (1965)**:
   For an atomless measure space `(Ω, μ)` and a measurable
   set-valued map `F : Ω → Set H` (`H` separable Hilbert /
   Banach), the integral `∫ F dμ` is convex. The proof goes via
   **Lyapunov's convexity theorem (1940)**: the range of an
   atomless ℝⁿ-valued vector measure is convex and compact.

4. **Mathlib status of the upstream theorems:**
   - `MeasureTheory.Measure.IsAtom` is present.
   - Vector-valued integration into Banach spaces is present
     (`MeasureTheory.integral` for Banach codomains).
   - **`Lyapunov`-named theorem** is NOT present
     (`grep -rn 'Lyapunov\|lyapunov' mathlib_path/Mathlib/` returns
     zero hits inside `Mathlib.MeasureTheory.*`).
   - **`Aumann`-named theorem on set-valued integrals** is NOT
     present.

5. **Approach C — explicit `ℓ²` counter-example.** A concrete
   construction `S : ℕ → Set ℓ²` with `S i = {0, eᵢ}` and the
   point `x = (1/2) ∑ᵢ eᵢ ∈ convexHull ℝ (∑ᵢ Sᵢ)` requires
   **every** index `i` to contribute non-trivially (since each
   `e i` axis is non-overlapping). This refutes any bounded
   excess-index count and is the narrowest formalization of
   the negative result.

**Files modified.**
* `research/problems/shapley-folkman-oq-01/problem.md` — full
  problem statement, three approaches, references.
* `research/problems/shapley-folkman-oq-01/state.md` — this entry.
* `research/problems/shapley-folkman-oq-01/knowledge.md` —
  Mathlib API map (present + missing), three viable approaches.
* `research/problems/shapley-folkman-oq-01/sessions/2026-05-12-s01-observe.md` —
  full S1 OBSERVE report: vacuity argument for `finrank=0`,
  Aumann/Lyapunov chain, concrete `ℓ²` counter-example sketch.

**Build status.** No `.lean` changes; no build attempted.

## Current Focus
S1 OBSERVE doc-only deliverable complete. Approach C
(`ℓ²` counter-example) is the narrowest viable S2 ACT target.
Approaches A/B require formalizing Lyapunov's theorem first
(8+ sessions of upstream work, deferred).

## Active Approach
**Approach C — explicit `ℓ²` counter-example** as the narrowest
S2 ACT seed. Formalize `shapley_folkman_fails_in_infinite_dim`
with `E = EuclideanSpace ℝ ℕ` (separable Hilbert; in Mathlib
as `EuclideanSpace`) or `lp.PiLp 2` if that is more ergonomic.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (Approach A/B/C all considered; C selected)

## Blockers
None for Approach C. Approaches A/B are blocked on
Lyapunov's convexity theorem (multi-session prerequisite,
not in Mathlib).

## Next Action

**S2 ACT — explicit `ℓ²` counter-example to literal Shapley–Folkman
extension**:

1. Create `proofs/Proofs/ShapleyFolkmanOQ01.lean` with imports
   `Mathlib.Analysis.InnerProductSpace.l2Space` and namespace
   `ShapleyFolkmanInfiniteDim`.
2. Define `S : ℕ → Set (EuclideanSpace ℝ (Fin n))` for the
   `n`-th truncation (parameterize in `n` since `EuclideanSpace
   ℝ ℕ` is the infinite-dim case but Mathlib's
   `lp` API may be cleaner).
3. State and prove `shapley_folkman_fails_in_finrank_zero`
   (~30 lines): if `Module.finrank ℝ E = 0` but `E` has a
   non-zero element, then no Shapley–Folkman-style decomposition
   with `excessIndices.card ≤ Module.finrank ℝ E` can exist
   for a generic Minkowski sum.
4. State `shapley_folkman_no_uniform_bound` (~30 lines):
   formalize the `eᵢ` counter-example sketch from this session.

After S2:
- **S3 ACT**: Aumann set-valued integral *statement* (no proof,
  just `def AumannIntegral` and a `theorem aumann_integral_convex
  := sorry` placeholder, with the sorry classified `OPEN` for
  Aristotle to skip).
- **S4 ACT (multi-session, deferred)**: Lyapunov's convexity
  theorem upstream.
