# Knowledge Base: egorov-theorem-oq-01-oq-01-oq-01

Insights accumulated during research on this problem.

**Goal**: Derive Lusin's theorem (every measurable `f : X → ℝ` on a finite measure
space agrees with / is continuous off a set of arbitrarily small measure) from the
gallery's Egorov theorem, via density of simple/continuous functions.

---

## Problem Understanding

Lusin's theorem (continuity form): for `f : X → ℝ` strongly measurable on a finite
(or inner-regular) Borel measure space and `ε > 0`, there is a closed/measurable
set `E` with `μ(Eᶜ) < ε` such that `f|_E` is continuous (`ContinuousOn f E`).

This is the parent `egorov-theorem-oq-01-oq-01` ("Egorov is Sharp")'s first open
question — the classical capstone of the Egorov circle of ideas.

---

## Insights

### Session 2026-06-25 (Session 1) — ORIENT survey

**Mode**: FRESH (fresh EMPTY claim) · **Outcome**: surveyed (phase OBSERVE→ORIENT).
No Lean compiled this session (degraded build env: ~141 concurrent lean procs); a
rushed multi-hundred-line measure-theory build risked an unverified/overclaimed
result, so this session produces a verified-feasible decomposition instead.

#### Mathlib inventory (all core ingredients PRESENT)

- **Egorov** (the source): `MeasureTheory.tendstoUniformlyOn_of_ae_tendsto`
  (`Mathlib/MeasureTheory/Function/Egorov.lean`), already wrapped by the gallery as
  `EgorovTheorem.egorov_uniform_off_small_set` (a.e. convergence on a finite-measure
  set ⇒ uniform convergence off a set of measure ≤ ε).
- **Simple-function approximation**: `MeasureTheory.SimpleFunc.tendsto_approxOn`
  (`Mathlib/MeasureTheory/Function/SimpleFuncDense.lean`) — for measurable `f`, the
  simple functions `approxOn f … n` converge to `f` pointwise (everywhere, in the
  range closure). Gives the sequence to feed Egorov.
- **Measure regularity (the crux for continuity off a small set)**:
  `Mathlib/MeasureTheory/Measure/RegularityCompacts.lean` provides
  `InnerRegular_of_polishSpace` and
  `InnerRegular_of_pseudoEMetricSpace_completeSpace_secondCountable` as INSTANCES —
  so a finite Borel measure on ℝ (or any Polish space) is automatically inner
  regular: every measurable set contains a compact/closed set of nearly full
  measure (`MeasureTheory.Measure.InnerRegular`, lemma `innerRegularWRT_isClosed_isOpen`).
- **Uniform limit preserves continuity**: `TendstoUniformlyOn.continuousOn` (the
  uniform limit of `ContinuousOn` functions is `ContinuousOn`).
- **Continuous functions dense in Lᵖ**: `MeasureTheory.Lp.boundedContinuousFunction_dense`
  — the ingredient for the ALTERNATIVE (non-Egorov) route, see below.

Mathlib does **NOT** have the classical Lusin continuity theorem itself: the only
"Lusin" in Mathlib is Lusin–Souslin (Polish-space/analytic-set measurability,
`Constructions/Polish/Basic.lean`), unrelated. So this is a genuine gap to fill.

#### Decomposition (classical Egorov ⇒ Lusin route)

1. **Simple-function step (BUILDABLE, the real work).** A simple function
   `s = Σ cᵢ · 1_{Aᵢ}` (finite measurable partition) is continuous off a small set:
   by inner regularity choose closed `Kᵢ ⊆ Aᵢ` with `μ(Aᵢ \ Kᵢ) < ε/2ⁱ`; the `Kᵢ`
   are pairwise-disjoint closed sets and `s` is constant `cᵢ` on each `Kᵢ`, hence
   `ContinuousOn s (⋃ Kᵢ)` (locally constant on a finite union of separated closed
   sets — in a metric space disjoint compact sets are positively separated). And
   `μ((⋃ Kᵢ)ᶜ) = μ(⋃ (Aᵢ \ Kᵢ)) < ε`. **This is the load-bearing lemma**; the
   `ContinuousOn`-of-finite-disjoint-closed-pieces glue is the fiddly part.
2. **Sequence + Egorov step (BUILDABLE, mostly assembly).** Take `sₙ = approxOn f … n`
   (`tendsto_approxOn`, → f pointwise a.e.). By step 1 each `sₙ` is continuous off a
   set `Bₙ` with `μ Bₙ < ε / 2ⁿ⁺²`. By `egorov_uniform_off_small_set`, `sₙ → f`
   uniformly off a set `T` with `μ T < ε/2`.
3. **Combine (BUILDABLE).** On `E := (⋃ₙ Bₙ)ᶜ ∩ Tᶜ` every `sₙ` is `ContinuousOn E`
   and `sₙ → f` uniformly on `E`, so `ContinuousOn f E` by
   `TendstoUniformlyOn.continuousOn`. `μ(Eᶜ) ≤ Σ μ Bₙ + μ T < ε`.
4. **(Optional) Tietze upgrade.** To get a globally continuous `g : X → ℝ` with
   `g = f` on `E` (the "agrees with a continuous function" form), extend `f|_E`
   off the closed set via `Continuous.exists_...`/Tietze (`TietzeExtension`). Not
   needed for the `ContinuousOn` form.

#### Alternative route (shorter, but not the assigned "via Egorov" one)

`boundedContinuousFunction_dense` gives continuous `gₖ → f` in `L¹`; pass to an
a.e.-convergent subsequence; Egorov turns a.e. into uniform-off-small-set; uniform
limit of continuous is continuous. Fewer moving parts than the regularity route but
still needs Egorov for the final upgrade — so it is genuinely an "Egorov ⇒ Lusin"
proof and may be the more tractable formalization. **Recommended to try first.**

#### Feasibility verdict

TRACTABLE but LARGE (est. 200–400 lines). No blocking Mathlib gap — every ingredient
exists. The single hardest sub-lemma is step 1's "simple function is `ContinuousOn`
a finite union of disjoint closed sets". Next session should build step 1 (or the
alternative route's subsequence+Egorov core) as the first verified deliverable.

---

## Dead Ends

[None yet.]
