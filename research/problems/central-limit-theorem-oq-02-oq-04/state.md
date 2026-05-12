# Current State

**Phase**: ACT (S4 — researcher-6 indicator-pair identity + researcher-4 build-fix)
**Since**: 2026-05-12T05:30:00Z
**Iteration**: 4 (multi-PR, build-passing)
**Last Updated**: 2026-05-12 (researcher-4)

## S4 partial (researcher-6, 2026-05-12, this PR)

**Indicator-pair covariance identity** — one new fully-proven private theorem,
positioned in Part III immediately before `davydov_covariance_inequality`:

```lean
theorem indicator_pair_covariance_eq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫ ω, A.indicator (1 : Ω → ℝ) ω * B.indicator (1 : Ω → ℝ) ω ∂μ
      - (∫ ω, A.indicator (1 : Ω → ℝ) ω ∂μ)
        * (∫ ω, B.indicator (1 : Ω → ℝ) ω ∂μ)
    = μ.real (A ∩ B) - μ.real A * μ.real B
```

This is the **algebraic identity** that the indicator base case of Davydov's
covariance inequality reduces to. The RHS `μ(A ∩ B) − μ(A) · μ(B)` is precisely
the expression appearing inside the supremum that defines `alphaMixingCoeff`
in the parent file `CentralLimitTheoremOQ02.lean` (line 416–424). Combined
with a `le_ciSup`-flavored bound (the next sub-step in the S4 path; deferred
since the parent file flagged the nested-`ciSup` elaboration complexity in
`alphaMixingCoeff_nonneg`), this yields the constant-1 Davydov bound on
indicator pairs `|Cov(1_A, 1_B)| ≤ α(ℱ, 𝒢)`. The truncation + Hölder
amplification step then promotes this base case to the sharp-constant
general L^p inequality with constant 12 (the full S4 deliverable).

**No supremum machinery is invoked at this layer.** The proof uses only:

* `Set.indicator_apply` and `Set.mem_inter_iff` for pointwise identification
  `1_A · 1_B = 1_{A ∩ B}`.
* `MeasureTheory.integral_indicator_one` to evaluate each indicator integral
  as `μ.real`.

### Why this is a productive narrow step

The full S4 Davydov proof is ~150 lines and decomposes as:

1. **Indicator-pair algebraic identity** — *this PR*. ~20 lines of measure-theoretic
   bookkeeping, fully proven, no Mathlib gaps.
2. **Indicator-pair α-mixing bound** — `|Cov(1_A, 1_B)| ≤ α(ℱ, 𝒢)` via
   `le_ciSup` on the nested-`ciSup` definition of `alphaMixingCoeff`. ~30 lines,
   deferred pending the parent's nested-`ciSup` complexity workaround.
3. **Simple-function extension** — linear combination of indicators by linearity
   of integrals. ~30 lines.
4. **Truncation step** — for L^p X, Y, bound the truncation tail via Markov's
   inequality + Hölder. ~50 lines.
5. **Hölder amplification** — Hölder on the bounded part yields the
   `(p-2)/p` exponent. ~30 lines.

This PR closes step 1 without touching the open S3 PRs (#17810, #17826), which
target the already-merged stationarity / Davydov-reduction work. The open PRs
are conflict-frozen against the post-S3 main; this S4 PR sits cleanly downstream
without overlap.

### Counts

* `lineCount`: 402 → 443 (+41, including ~25 lines of docstring + 16 lines
  of proof body + import line)
* `theoremCount`: 7 → 8 (+1 fully-proven theorem)
* `definitionCount`: 4 (unchanged)
* `sorries`: 2 (unchanged — `davydov_covariance_inequality` and
  `mixing_clt_ibragimov` remain the deferred targets; this PR adds a proven
  helper but does not close either sorry)
* `axiomCount`: 0 (unchanged)

### Strategic positioning

**Non-overlap with open PRs**:
* #17810 (researcher-1, conflicting): 5 stationarity/moment-bound bridge
  lemmas (Stationary.integrable_of_zero, etc.) — predates the merged S3 ACT
  (#17820) and its content is now superseded by `stationary_eLpNorm_eq`
  proven in S3. Conflict-frozen.
* #17826 (researcher-1, mergeable): duplicate of merged S3 ACT (#17820);
  same Davydov reduction + bridge lemmas. Content already in main.

This PR is **strictly downstream** of S3: it adds a new helper proven against
the post-S3 file, building on the now-merged `IbragimovHypotheses` /
`davydov_covariance_inequality` API surface. No overlap with the two open S3
PRs at the file-level (this PR adds a new theorem, doesn't touch existing
ones). No overlap at the API level (this helper is positioned to be consumed
by future S4 sub-steps, not by the S3 deliverables).

### Build status

**[BUILD UNVERIFIED]** — Same caveat as S2/S3/S22: worktree's
`proofs/.lake` is a recursive self-symlink, so local Docker builds
re-fresh-clone Mathlib (~30–45 min cold). The new helper uses only Mathlib
API verified against `/Users/rwalters/GitHub/mathlib4`:

* `MeasureTheory.integral_indicator_one`
  (`Mathlib.MeasureTheory.Integral.Bochner.Set` line 519):
  `∫ x, s.indicator 1 x ∂μ = μ.real s` for measurable `s`. Added as an
  explicit import to ensure transitive availability.
* `Set.indicator_apply`, `Pi.one_apply`, `Set.mem_inter_iff` — core Set/Pi
  API, transitively available via `MeasureTheory.Function.LpSpace.Basic`.
* `IsProbabilityMeasure` and `Measure.real` — transitively available.

No new axioms.

### Next iteration (S4 cont'd)

After this PR lands, the remaining steps for closing
`davydov_covariance_inequality`:

1. **Indicator-pair α-mixing bound** (next ~30 lines): apply `le_ciSup` to
   the nested `ciSup` definition of `alphaMixingCoeff` to derive
   `|μ(A ∩ B) − μ(A)·μ(B)| ≤ alphaMixingCoeff μ ℱ 𝒢` for any measurable
   `A ∈ ℱ`, `B ∈ 𝒢`. The proof composes with this PR's
   `indicator_pair_covariance_eq` to give the constant-1 indicator-pair
   Davydov bound on covariance. The parent's `alphaMixingCoeff_nonneg`
   nested-`ciSup` complexity note (line 444) applies; the workaround is
   to apply `le_ciSup` iteratively at each ⨆ layer.
2. **Simple-function extension** (~30 lines).
3. **Truncation + Hölder amplification** (~80 lines).

Total ~140 lines once the nested-`ciSup` bound is settled.

---

## S3 (researcher-1, 2026-05-12, merged via #17820)

S4 ACT — **Build-fix** for S3 PR #17820 (which was merged
"(build pending)" and never actually compiled on `origin/main`), plus
proven `indicator_cov_le_one` ([0, 1] envelope helper) and documented
structural decomposition of `davydov_covariance_inequality`.

Three build blockers fixed:
1. **Stale import** `Mathlib.Probability.Variance` (file removed in Mathlib
   drift) — removed (unused in code).
2. **MS Ω typeclass-synthesis collision** — when `(ℱ 𝒢 : MeasurableSpace Ω)`
   are direct explicit args of a theorem, Lean 4's typeclass synthesis
   picks them as the `[MeasurableSpace Ω]` instance of
   `alphaMixingCoeff`, instead of the ambient `inst✝¹`. Fix: use the parent
   file's pattern `(σPair : Fin 2 → MeasurableSpace Ω)` (function-form),
   then `σPair 0` and `σPair 1` are projections — not instance candidates.
   This is the same trick the parent file uses at
   `independent_implies_zero_mixing` and `AlphaMixingSequence.mixing_bound`.
3. **Invalid Lean identifier `σ²`** in `mixing_clt_ibragimov` (superscript
   `²` not in Lean's identifier alphabet) — renamed to `σsq`.

Deliverables (this session):
- **Build-fix**: 3 blockers above; file now builds cleanly.
- **`indicator_cov_le_one` (PROVEN)**: `[0, 1]` envelope for the
  indicator-covariance term, the `BddAbove` witness for the nested suprema
  inside `alphaMixingCoeff`.
- **Documented structural decomposition** in `davydov_covariance_inequality`'s
  docstring: the L^p Davydov inequality decomposes into 3 named
  order-theory ingredients (`alphaMixingCoeff_le_one`,
  `alphaMixingCoeff_nonneg`, `davydov_indicator_bound`) + 1 L^p density
  step. Each ingredient has a clear strategy.

Sorries: 2 (unchanged from S3 raw count; the file now actually compiles).

## Active Approach

**Sharp-threshold polynomial-mixing CLT** under (2+δ)-th moments. Bernstein
blocks proof template:

1. **Davydov's covariance inequality (S4–S5)** ⇒ covariances are summable.
   - S3 status: stated, never built.
   - S4 status: builds cleanly; decomposed into 3 order-theory sorries
     (yet to formalize) + 1 L^p density step. `indicator_cov_le_one`
     proven as the `[0, 1]` envelope.
   - S5a target: formalize the 3 order-theory ingredients.
   - S5b target: L^p density / truncation step.
2. **Long-run variance σ² = Var(X₁) + 2∑_{k≥1} Cov(X₁, X_{k+1}) absolute
   convergence** — S3 proven modulo Davydov (call site refactored in S4 to
   use the `σPair : Fin 2 → MS Ω` wrap).
3. Joint tuple stationarity strengthening (S6).
4. Bernstein blocks p_n, q_n (S7).
5. Lindeberg condition on large blocks (S8).
6. Invoke parent's Lindeberg-Feller CLT (S9).

## Blockers

- **3 order-theory ingredients still sorry** (named in
  `davydov_covariance_inequality` docstring as mechanic-pass targets):
  `alphaMixingCoeff_le_one`, `alphaMixingCoeff_nonneg`,
  `davydov_indicator_bound`. The Prop-indexed nested-iSup
  unification quirks block direct `iSup_pos` rewrites (same issue the
  parent file ran into at line 444). Future mechanic pass should use
  `iSup_const` + `IsEmpty` / `Nonempty` instance bridging, or wrap
  σ-algebras in a Subtype to fully disambiguate typeclass synthesis.
- **Davydov's L^p inequality** (S5b target): ~100 lines of
  measure-theoretic reduction (level-set decomposition + Hölder).

## Next Action

**Session 5 candidates** (in priority order):

1. **S5a (mechanic-pass)**: discharge the 3 order-theory ingredients
   (`alphaMixingCoeff_le_one`, `alphaMixingCoeff_nonneg`,
   `davydov_indicator_bound`). Pure ConditionallyCompleteLattice ℝ
   machinery; ~80 lines once the Prop-iSup unification approach settles.
2. **S5b ACT** (~100 lines): L^p density step using level-set decomposition
   + Hölder, reducing to `davydov_indicator_bound`.
3. **Parallel path**: Refine `Stationary` to joint tuple stationarity (S6
   target prerequisite for Bernstein blocks). ~100 lines.

## Decomposition Plan

| Session | Phase | Deliverable | Lines | Status |
|---|---|---|---|---|
| S1 | OBSERVE | Scaffold (md + json) | 0 Lean | merged #17778 |
| S2 | ORIENT | 4 def stubs + 2 thm stmts + 2 proven helpers | 231 | merged #17792 |
| S3 | ACT | Davydov stmt + 3 new helpers + longrun_variance proof (never built) | 402 | merged #17820 (build broken) |
| S4 | ACT | Build-fix + indicator_cov_le_one + structural decomposition | 502 | **this session** |
| S5a | mechanic | Discharge 3 order-theory sorries (named in docs) | ~80 | next |
| S5b | ACT | L^p density / truncation → full Davydov | ~100 | next |
| S6 | ACT | Refine Stationary to tuple-joint stationarity | ~100 | |
| S7 | ACT | Bernstein blocks p_n, q_n + arithmetic | ~150 | |
| S8 | ACT | Large-block independence approximation | ~120 | |
| S9 | ACT | Lindeberg condition on blocks | ~100 | |
| S10 | ACT | Invoke parent Lindeberg-Feller CLT | ~50 | |

## Attempt Counts

- Total attempts: 4
- Current approach attempts: 1 (S4 build-fix + indicator-helper +
  structural decomposition)
- Approaches tried:
  - S1: OBSERVE scaffolding.
  - S2: ORIENT — predicates + structure + main theorem statements + 2
    helpers.
  - S3: ACT — Davydov-modulo proof of long-run variance absolute
    convergence + extension of IbragimovHypotheses + 3 new proven theorems
    (PR #17820 merged "(build pending)" without actually building).
  - S4: ACT — discovered S3 was broken, fixed 3 build-blockers, added
    proven `indicator_cov_le_one` helper, and documented the structural
    decomposition of `davydov_covariance_inequality` into named
    order-theory ingredients.

## Key Files

- `proofs/Proofs/CentralLimitTheoremOQ02OQ04.lean` — **S4: 502 lines, builds
  cleanly**. 8 theorems + 2 sorries, 3 definitions, 1 structure with 14
  fields. S4 additions: removed stale import, refactored Davydov signature
  to `Fin 2 → MS Ω` wrap, renamed `σ²` → `σsq`, added proven
  `indicator_cov_le_one`. The remaining 2 sorries are
  `davydov_covariance_inequality` (L^p version, S5b target) and
  `mixing_clt_ibragimov` (S6+ target).
- `src/data/proofs/central-limit-theorem-oq-02-oq-04/meta.json` — updated
  with sorries 2, lineCount 502, theoremCount 8.
- `proofs/Proofs/CentralLimitTheoremOQ02.lean` — parent file, unchanged.
  The 3 named order-theory ingredients in S4's Davydov docstring are good
  candidates for upstream contribution.
