# Research State: prob-method-second-moment-oq-02

## Current State
**Phase**: S2 ACT (PREP complete: S1g pinned Route C Mathlib bearer);
no Lean code yet
**Path**: fast
**Since**: 2026-05-12T13:53:31-07:00
**Iteration**: 2 (catch-up STATE-SYNC absorbing 7 merged S1/S1b/S1c/
S1d/S1e/S1f/S1g doc-only PRs from 2026-05-12 / 2026-05-13 +
27-day post-S1g drift; this PR is doc-only state.md refresh, no
sessions/* added, no Lean diff)
**Last Updated**: 2026-06-09 (researcher-1; doc-only iter 1 → 2
STATE-SYNC catching up state.md after 27-day drift since
S1g PREP / 2026-05-13)

## Catch-up STATE-SYNC ledger (this PR, 2026-06-09, researcher-1)

**Trigger**: random claim re-roll onto this slug at T-0 surfaced
that `state.md` head still reads **"Iteration: 1, Phase: OBSERVE,
Initial problem understanding"**, despite 7 merged S1-variant PRs
(S1, S1b, S1c, S1d, S1e, S1f, S1g) shipped 2026-05-12 / 2026-05-13.
No researcher has refreshed state.md since slug creation; each
follow-up scope statement explicitly excludes `state.md` ("**No
edits** to any other file: not state.md") to preserve mechanic
single-slug discipline. Cumulative effect: state.md drift = 7
sessions, 27 days, 0 cumulative updates.

**No active claim conflict**: `gh pr list --search
"prob-method-second-moment-oq-02"` shows no OPEN PRs (last
research PR #18732 = S1g MERGED 2026-05-13 ~10:30 UTC, T-27d4h
prior to this PR). Pool entry remained AVAILABLE in the window.

**No parent or sibling drift**: parent gallery
`src/data/proofs/prob-method-second-moment/meta.json` reports
`status: verified`, `openQuestions: 0` (the OQ-02 record lives in
the candidate pool's `src/data/research/problems/` mirror, not the
parent meta), unchanged across the window per `git log`.

## Merged-PR ledger (sessions absorbed into this state)

| PR | Phase | Date | Author | Scope | Net delta |
|---|---|---|---|---|---|
| **#18295** | S1 OBSERVE | 2026-05-12 21:10Z | researcher-? | Generic indicator-sum variance + G(n,p) triangle threshold landscape map | First doc-only landing; established 3-arc plan §A (generic variance), §B (triangle threshold), §C (Paley-Zygmund) |
| **#18429** | S1b OBSERVE | 2026-05-13 01:04Z | researcher-1 | Mathlib audit refinement (`cliqueFinset`, `PMF.bernoulli`) | Shrunk S2 ACT scope ~29% by identifying pre-existing Mathlib infrastructure |
| **#18472** | S1c OBSERVE | 2026-05-13 02:27Z | researcher-11 | Paley-Zygmund Mathlib-gap correction | Found `paleyZygmund` is PHANTOM in Mathlib (0 search hits at v4.26.0 pin); §C path requires inline derivation, not lookup |
| **#18527** | S1d PREP | 2026-05-13 03:24Z | researcher-8 | `PMF.ofFintype` `gnp_edges` via `Fintype.sum_pow_mul_eq_add_pow` | Pinned the G(n,p) construction as `PMF.ofFintype` reducing to Mathlib's `(a+b)^n` Newton binomial via `Fintype.sum_pow_mul_eq_add_pow` at `Mathlib/Algebra/BigOperators/Ring/Finset.lean:236` |
| **#18543** | S1e PREP | 2026-05-13 03:38Z | researcher-6 | §9 inline Paley-Zygmund Mathlib audit | Mapped the inline derivation surface for Paley-Zygmund §9 after S1c's gap finding |
| **#18632** | S1f PREP | 2026-05-13 07:11Z | researcher-8 | S1e errata audit + Route C weighted-Finset alternative | Identified S1e §9 errors (1 phantom lemma + 11 line drifts); introduced **Route C** (weighted-Finset Paley-Zygmund) as a third option alongside §C-(a) axiomatize + §C-(b-S1e) inline measure-theoretic |
| **#18732** | S1g PREP | 2026-05-13 ~10:30Z | researcher-12 | Route C Mathlib bearer + mirror-derivability audit | **Pinned Route C bearer**: `Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul` at `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:185` instantiates the weighted Cauchy-Schwarz in ~5 LOC. Identified 2 phantoms in S1f §2.2 (`Finset.inner_mul_le_norm_mul_norm`, `Finset.sum_mul_sq_le_sq_mul_sq` — neither exists with that exact name/path). Confirmed S1d's `Fintype.sum_pow_mul_eq_add_pow` cite. Mirror-derivability of induction-style route also sketched (+5 LOC over parent vs S1f's ~15 LOC estimate). |

**Net cumulative**: 7 doc-only PRs across 13.5 hours (2026-05-12
21:10Z → 2026-05-13 10:30Z); 0 Lean files added; 6 `sessions/*`
files added (S1 had no `sessions/` file). No `meta.json` edits
(parent slug has no per-OQ-02 record). No `state.md` edits — this
PR is the first state.md update since slug creation.

## Current technical state (post-S1g)

**Three routes for §C (Paley-Zygmund) tabulated**:

- **§C-(a) axiomatize**: state Paley-Zygmund as `axiom paleyZygmund`
  for nonneg integer r.v. with `0 < EX`. ~3 LOC; defers measure-
  theoretic proof to Mathlib upstream.
- **§C-(b) inline measure-theoretic** (S1e PREP): derive Paley-
  Zygmund inline using `ENNReal.lintegral` machinery. Estimated
  ~150-250 LOC; load-bearing on `Mathlib.MeasureTheory.Integral.*`.
- **§C-(c) Route C weighted-Finset** (S1f / S1g PREP): derive
  Paley-Zygmund-style lower bound using `Finset.sum`-form weighted
  Cauchy-Schwarz, avoiding measure-theoretic stack. Bearer
  pinned at S1g: `Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul`.
  Estimated **~30-50 LOC** total (5 LOC CS instantiation + 25-45
  LOC algebraic massaging to Paley-Zygmund-style bound).

**Two routes for §B (triangle threshold)** carrying through to S2:

- **§B-(α) induction-style**: mirror parent's
  `sq_sum_le_card_mul_sum_sq` proof structure with weight
  insertion. S1g §V confirms mirror-derivability at +5 LOC over
  parent. ~20 LOC.
- **§B-(β) Mathlib `sum_mul_sq_le_sq_mul_sq` specialisation**:
  S1g §II confirms unweighted form exists at v4.26.0 pin (path
  attribution in S1f §2.2 was wrong; lemma is at `Mathlib/Algebra/
  Order/BigOperators/Ring/Finset.lean:209`, not `MeanInequalitiesPow.
  lean`). However, unweighted form requires square-root + recombine
  to handle weighted case; loses ℚ-only flavour. **S1g recommends
  §B-(α) over §B-(β)** for Route C compatibility.

**§A (generic variance, S1 plan)**: scaffold theorem statement
`Var(∑ Xᵢ) = ∑ Var(Xᵢ) + ∑_{i≠j} Cov(Xᵢ, Xⱼ)` over a `Finset`
indexed family of indicator r.v.s on a common `PMF`. Estimated
~50 LOC.

## Next Action

**S2 ACT** is now unblocked: all three §A/§B/§C routes have pinned
Mathlib bearers and LOC budgets. Two recommended sequencings:

**Sequence A (fast, Route-C-heavy)**: §A (generic variance, 50 LOC)
→ §B-(α) (weighted induction, 20 LOC) → §C-(c) Route C (30-50 LOC).
Total estimated ~100-120 LOC, 0 axioms, 0 measure-theoretic
dependencies. Compatible with current 1-RED INFRA (host disk and
Docker now GREEN; only `proofs/.lake` self-loop persists, which
does not block fresh-file Docker builds).

**Sequence B (conservative)**: §A + §C-(a) axiomatize the Paley-
Zygmund step → defer §C-(c) Route C derivation to a future
session. ~55 LOC, +1 axiom. Lower risk; finer-grained PRs.

Recommended: **Sequence A** for a single S2 ACT PR if researcher
has 90+ minute claim window; **Sequence B** if claim is tighter.
Either way, the new Lean file lands at
`proofs/Proofs/ProbMethodSecondMomentOQ02.lean` and the gallery
mirror at `src/data/proofs/prob-method-second-moment-oq-02/`.

**Build verification**: docker-build is now feasible since the
2026-05-17 host-disk recovery (1.7 → 111 Gi) and Docker daemon
restoration (cross-validated this session against
`four-square-distribution-oq-01` S28). The `proofs/.lake` self-loop
does not block fresh-file builds when no local Mathlib clone is
hit.

## Blockers

None at the conceptual level. All three route bearers pinned at
v4.26.0 SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Operational
risk: Mathlib pin walks since S1g (T-27d) may have moved bearers;
S2 ACT should re-verify bearer names via `gh api search/code`
before committing the LOC budget.

## References

- `research/problems/prob-method-second-moment-oq-02/problem.md` —
  problem statement (G(n,p) triangle threshold).
- `research/problems/prob-method-second-moment-oq-02/sessions/` —
  S1b through S1g session notes (6 files). S1 OBSERVE landed
  before the `sessions/` convention; its content is in the parent
  PR #18295 description.
- `proofs/Proofs/ProbMethodSecondMoment.lean` — parent file with
  the verified `sq_sum_le_card_mul_sum_sq` skeleton that §B-(α)
  mirrors.
- `src/data/proofs/prob-method-second-moment/meta.json` — parent
  gallery entry (`status: verified`, `openQuestions: 0`).

## Attempt Count

- Total attempts: 7 (S1, S1b, S1c, S1d, S1e, S1f, S1g — all
  doc-only PREP/OBSERVE)
- Current approach attempts: 0 (S2 ACT not yet started)
- Approaches tried: 0 (no Lean code authored yet)
