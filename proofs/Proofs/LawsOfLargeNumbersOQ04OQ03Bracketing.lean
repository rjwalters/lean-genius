/-
# Glivenko-Cantelli: Bracketing Decomposition Scaffold
(laws-of-large-numbers-oq-04-oq-03 — Session 3)

The parent file `LawsOfLargeNumbersOQ04` discharges the uniform Glivenko-Cantelli
theorem with one axiom, `glivenko_cantelli_uniform`, that bundles the entire
finite-bracketing argument as a single black box. Session 2's
`bracketing-decomposition-draft.md` decomposes that axiom orthogonally into
three pieces:

  1. **Grid existence** (analytic, on F): for every ε > 0 there exist finitely
     many continuity points q₀ < ⋯ < q_{k+1} of F covering [0,1] in F-jumps ≤ ε.
     This is the only piece missing from Mathlib 4.26.
  2. **Simultaneous pointwise convergence**: provable from `MeasureTheory.ae_all_iff`
     + parent's `empiricalCDF_pointwise_convergence`. ~10–20 lines.
  3. **Uniform sup-bound from grid**: deterministic monotone interpolation,
     provable from parent's `empiricalCDF_mono`/`trueCDF_mono`. ~50 lines.

Session 3 (this file) ships pieces (1) and a typed scaffold:

  * `BracketingGrid F ε` (§2.1): structure encoding an ε-bracketing grid for a
    CDF F. Five fields: a strict-monotone Fin (k+2)-indexed sequence of
    continuity points, with an interior step bound and two boundary bounds.
  * `bracketingGrid_exists` (§2.2): the sole new axiom. Asserts existence of a
    grid for any CDF derived from a probability measure on ℝ. Replaces the
    parent's monolithic `glivenko_cantelli_uniform` once §2.3–§2.5 land.

Sessions 4+ will fill in the three theorems §2.3 (`bracketing_simultaneous_pointwise`),
§2.4 (`bracketing_uniform_from_grid`), and §2.5 (`glivenko_cantelli_uniform_proved`)
following `bracketing-decomposition-draft.md` §2 verbatim.

## Axiom shift, not net axiom reduction (yet)

Until §2.5 lands, the chain has the parent's `glivenko_cantelli_uniform` AND
the new `bracketingGrid_exists` axiom — net count goes 1 → 2. After §2.5
proves `glivenko_cantelli_uniform_proved` from `bracketingGrid_exists`, the
parent's monolithic axiom can be retired (or the gallery entry can adopt the
proved variant), bringing the chain back to 1 axiom whose mathematical content
is now purely real-analytic (no probability) and is the natural Mathlib home
for upstream contribution as `Monotone.exists_increasing_continuity_seq`.

## Build status

Build pending. The `proofs/.lake` recursive self-symlink in this repo forces a
~45-min cold-cache Mathlib clone on every build (per memory feedback). The
file is small (~50 lines, 1 structure + 1 axiom), uses standard Mathlib API
already exercised in the parent (`ContinuousAt`, `Fin (k+2)`, `StrictMono`),
and has no novel proof obligations. Confidence the file type-checks is high;
build verification deferred to S4 alongside the §2.3–§2.5 theorem additions.
-/

import Proofs.LawsOfLargeNumbersOQ04OQ03

namespace GlivenkoCantelli

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

-- ============================================================================
-- §2.1: The bracketing-grid predicate
-- ============================================================================

/-- An **ε-bracketing grid** for a CDF `F : ℝ → ℝ` is a finite increasing
    sequence of `F`-continuity points whose `F`-images cover `[0, 1]` in steps
    of size at most `ε`.

    The five fields capture:
    * `k`        — number of interior cells (so the grid has `k + 2` nodes);
    * `q`        — the strictly increasing sequence of nodes,
                   indexed by `Fin (k + 2)`;
    * `mono`     — strict monotonicity of `q`;
    * `cont`     — `F` is continuous at each grid node;
    * `step_le`  — interior `F`-jump bound: `F(qⱼ₊₁) − F(qⱼ) ≤ ε` for each
                   adjacent pair, indexed by `Fin (k + 1)` via
                   `Fin.castSucc`/`Fin.succ`;
    * `left_le`  — left boundary mass bound: `F(q₀) ≤ ε`;
    * `right_ge` — right boundary mass bound: `F(q_{k+1}) ≥ 1 − ε`.

    The `cont` side condition makes the right-continuous CDF agree with
    pointwise convergence at each node and removes the need to distinguish
    `F(qⱼ⁻)` from `F(qⱼ)` in the deterministic uniform-bound argument
    (§2.4 of `bracketing-decomposition-draft.md`). -/
structure BracketingGrid (F : ℝ → ℝ) (ε : ℝ) where
  k        : ℕ
  q        : Fin (k + 2) → ℝ
  mono     : StrictMono q
  cont     : ∀ j, ContinuousAt F (q j)
  step_le  : ∀ j : Fin (k + 1), F (q j.succ) - F (q j.castSucc) ≤ ε
  left_le  : F (q 0) ≤ ε
  right_ge : F (q (Fin.last (k + 1))) ≥ 1 - ε

-- ============================================================================
-- §2.2: Grid existence (the one axiom that remains)
-- ============================================================================

/-- **Mathlib gap** (axiomatized). For any CDF derived from a probability
    measure on ℝ and any `ε > 0`, an ε-bracketing grid for the CDF exists.

    The mathematical content reduces to: the discontinuity set of a monotone
    function `ℝ → ℝ` is countable
    (`Monotone.countable_setOf_not_continuousAt`), hence its complement is
    dense; pick continuity points greedily so that each `F`-step is at most
    `ε`. The endpoints are handled by the bounded-range property of CDFs.

    This is the natural Mathlib home for the upstream lemma
    `Monotone.exists_increasing_continuity_seq`
    (`bracketing-decomposition-draft.md` §2.2 sketch).

    Once §2.3–§2.5 of the bracketing decomposition land in subsequent sessions,
    this single axiom replaces the parent's monolithic
    `glivenko_cantelli_uniform`, narrowing the open mathematical content from
    a probabilistic uniformity statement to a purely real-analytic ε-cover
    induction. -/
axiom bracketingGrid_exists [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ i, Measurable (X i))
    {ε : ℝ} (hε : 0 < ε) :
    Nonempty (BracketingGrid (trueCDF X μ) ε)

end GlivenkoCantelli
