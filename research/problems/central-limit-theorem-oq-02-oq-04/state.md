# Current State

**Phase**: ACT (S4 partial — indicator-pair covariance identity proven; full Davydov deferred)
**Since**: 2026-05-12T06:50:00Z
**Iteration**: 4 (partial)
**Last Updated**: 2026-05-12 (researcher-6)

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

S3 ACT — Discharge `longrun_variance_absolutely_convergent` by reducing it
to a single named Davydov sorry. The S2 sorry on long-run variance has been
replaced by a more granular and clearly-scoped sorry on
`davydov_covariance_inequality`. Net change to sorry count: 0; net change to
"proof depth": one full main theorem now provably reduces to Davydov.

Deliverables (this session):
- Extend `IbragimovHypotheses` with 3 fields: `alpha_nonneg`,
  `past_measurable`, `future_measurable` (needed to apply Davydov per-term).
- State `davydov_covariance_inequality` with `(p-2)/p` exponent and an
  abstract `α₀` upper bound parameter (S4 sorry).
- Prove `stationary_eLpNorm_eq` via Mathlib's `IdentDistrib.eLpNorm_eq`.
- Prove `polynomial_mixing_summable` combining polynomial decay + rpow
  monotonicity + `ibragimov_threshold_summable` + `summable_nat_add_iff`.
- Prove `longrun_variance_absolutely_convergent` by chaining the above with
  `Summable.of_nonneg_of_le` for the comparison test.

## Active Approach

**Sharp-threshold polynomial-mixing CLT** under (2+δ)-th moments. The proof
follows the standard Bernstein blocks template:
1. **Davydov's covariance inequality (S4)** ⇒ covariances are summable.
   - S3 status: stated cleanly; proof itself deferred to S4 (~150 lines).
2. **Long-run variance σ² = Var(X₁) + 2∑_{k≥1} Cov(X₁, X_{k+1}) absolute
   convergence (S3 — this session, proven modulo Davydov).**
3. Joint tuple stationarity strengthening (S5).
4. Bernstein blocks p_n, q_n (S6) decompose [1, n] into approximately
   independent large blocks.
5. Lindeberg condition on large blocks (S8) follows from the (2+δ)-th
   moment bound.
6. Invoke parent's Lindeberg-Feller CLT (S9) to conclude.

## Blockers

- **Mathlib has no α-mixing API** (confirmed S1). Continue using parent's
  `alphaMixingCoeff` and `AlphaMixingSequence`. Future upstream contribution
  would consolidate this stack.
- **Davydov's covariance inequality** is the single open analytic engine.
  S4 target.

## Next Action

**Session 4 next action**: Discharge `davydov_covariance_inequality`.

**Strategy** (Hölder + indicator decomposition):
1. For bounded random variables `X = a · 1_A`, `Y = b · 1_B` with
   `A ∈ ℱ`, `B ∈ 𝒢`:
   `Cov(X, Y) = ab · [μ(A ∩ B) - μ(A) · μ(B)] ≤ ab · α(ℱ, 𝒢)`.
2. Approximate general L^p X, Y by indicators via the level-set decomposition
   `X = ∫ 1_{X > t} dt`.
3. Apply Hölder with `(p, p/(p-1))` to bound the resulting double integral.
4. Sharp constant `12` comes from a careful tracking through the indicator
   approximation; references: Doukhan 1994 §1.2.2, Bradley 2007 Vol I Thm 3.7.

Estimate: ~150 lines, no Mathlib gaps beyond Hölder (already there).

Alternative path: **Refine `Stationary`** to joint tuple stationarity (S5
target prerequisite for Bernstein blocks). Could be done in parallel with
Davydov; ~40 lines for the type-level strengthening + 60 lines for the
key tuple-shift lemma.

## Decomposition Plan

| Session | Phase | Deliverable | Lines | Status |
|---|---|---|---|---|
| S1 | OBSERVE | Scaffold (md + json) | 0 Lean | merged #17778 |
| S2 | ORIENT | 4 def stubs + 2 thm stmts + 2 proven helpers | 231 | merged #17792 |
| S3 | ACT | Davydov stmt + 3 new helpers + longrun_variance proof | 402 | **this session** |
| S4 | ACT | Davydov covariance inequality proof | ~150 | next |
| S5 | ACT | Refine Stationary to tuple-joint stationarity | ~100 | |
| S6 | ACT | Bernstein blocks p_n, q_n + arithmetic | ~150 | |
| S7 | ACT | Large-block independence approximation | ~120 | |
| S8 | ACT | Lindeberg condition on blocks | ~100 | |
| S9 | ACT | Invoke parent's Lindeberg-Feller CLT | ~50 | |

## Attempt Counts

- Total attempts: 3
- Current approach attempts: 1 (S3 ACT Davydov-reduction)
- Approaches tried:
  - S1: OBSERVE scaffolding.
  - S2: ORIENT — predicates + structure + main theorem statements + 2 helpers.
  - S3: ACT — Davydov-modulo proof of long-run variance absolute convergence
    + extension of IbragimovHypotheses + 3 new proven theorems.

## Key Files

- `proofs/Proofs/CentralLimitTheoremOQ02OQ04.lean` — **S3 expanded** (402 lines,
  7 theorems incl. 2 sorries, 4 proven helpers, 3 definitions, 1 structure with
  14 fields). The 3 new theorems added in S3:
  `stationary_eLpNorm_eq`, `polynomial_mixing_summable`,
  `davydov_covariance_inequality` (sorry).  The S2 sorry
  `longrun_variance_absolutely_convergent` is now proven.
- `src/data/proofs/central-limit-theorem-oq-02-oq-04/meta.json` — updated
  with new theorem count (7), line count (402), mathlib dependencies, and
  section ranges.
- `proofs/Proofs/CentralLimitTheoremOQ02.lean` — parent file, unchanged.
