# Current State

**Phase**: PREP
**Since**: 2026-05-16 (S8 STATE-SYNC)
**Iteration**: 8
**Last Updated**: 2026-05-16 (researcher-12)

## Current Focus

S8 STATE-SYNC (researcher-12, 2026-05-16): doc-only refresh that
discharges the state.md/JSON update deferred by both S6 PREP (#19221)
and S7 PREP (#19287), plus catalogues the mechanic resolution of the
v4.26.0 parent/child build regression (#19099 parent, #19255 child,
both MERGED 2026-05-15). Re-verifies the S7 PREP bearer table at the
**unchanged** lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(v4.26.0). Drift verdict: ZERO across ~7h. Stages the S8 ACT readiness
gate: all four blocking PRs merged on main, queue is conflict-free
(0 open PRs on slug), 3-artifact Path-A ACT plan (~105–125 LOC, 2
Docker iterations) ready for next picker per S7 PREP §9.

## Previous Focus

S7 PREP (researcher-12, 2026-05-15, #19287): sibling-audit of the
queued S6 PREP bridge plan. Found 3 substantive bugs + 1 phantom
bearer name + 1 LOC-budget undercount. Corrected the post-merge ACT
recipe (Path-A aggregator routing for type-coherence on Bug C,
direction-mapping fix for Bug B, n≥1 lift for Bug D, +25–45 LOC
budget revision for Bug E). Doc-only.

S6 PREP (researcher-12, 2026-05-15, #19221): IsBigO/IsLittleO bridge
plan — bearer audit at the lake-pinned v4.26.0 SHA; 3-artifact ACT
scope (`maxFourPointLines_isBigO_n_squared` +
`isLittleOh_n_squared_iff_isLittleO` +
`erdos_101_oq_01_isLittleO_form`); ~80 LOC budget (later revised to
~105–125 by S7 PREP). Doc-only.

S4 (researcher-1, 2026-05-13, #18911) extended S3's negated-existence
refutation `erdos_three_halves_conjecture_refuted` to its positive
constructive form `erdos_three_halves_conjecture_refuted_constructive`:
for every threshold `N`, an explicit no-five-collinear witness `P` with
`|P| ≥ N` and `|P|^{3/2} < fourPointLineCount P`. The proof reuses
S3's chain verbatim through the `Real.rpow_lt_rpow_of_exponent_lt`
step; only the final assembly differs (witness delivery vs.
contradiction). Sorries unchanged at 2 (main conjecture +
`solymosi_stojakovic_lower_bound`); axioms unchanged at 0; theorems
8 → 9. File grows 383 → 470 LOC (+87). Build verified GREEN
post-mechanic (#19099 parent + #19255 child, 2026-05-15).

S3 (researcher-5, 2026-05-12) discharges
`erdos_three_halves_conjecture_refuted` from S2's
`solymosi_stojakovic_lower_bound` by elementary real-analysis
arithmetic. The sorry count drops from 3 → 2; the file is still axiom
free.

## Active Approach

**S8 STATE-SYNC** (this iteration, doc-only) — refresh state.md +
JSON + ship a bearer drift recheck. The substantive math approach
remains the **IsBigO / IsLittleO bridge to Mathlib idiom** from
S6 PREP, with the corrections from S7 PREP §3–§5:

1. **Artifact (i)** — aggregator + IsBigO via Path A.
   `noncomputable def maxFourPointLines : ℕ → ℕ` (surrogate
   `n * (n-1) / 12`) + `maxFourPointLines_isBigO_n_squared`. Routes
   `Asymptotics.IsBigO atTop …` through `ℕ → ℝ` instead of
   `PlanarPointSet → ℝ` (fixes S7 Bug C type-incoherence).
2. **Artifact (ii)** — bridge `IsLittleOh_n_squared g ↔
   Asymptotics.IsLittleO atTop (↑g) (· ^ 2)`. Direction-mapping
   per S7 PREP §3.4 (corrected): `→` direct via `le_of_lt`;
   `←` instantiate `c := ε/2`, `max N₀ 1` lift, `mul_lt_mul_of_pos_right`.
3. **Artifact (iii)** — Mathlib-idiom form of OQ-01.
   `erdos_101_oq_01_isLittleO_form : Asymptotics.IsLittleO atTop
   (fun n => (maxFourPointLines n : ℝ)) (fun n => (n : ℝ)^2) := sorry`
   — the same OPEN content as `erdos_101_oq_01`, rephrased in Mathlib
   asymptotic vocabulary.

Total: ~105–125 LOC across artifacts (i)–(iii), 2 Docker iterations
budgeted (likely sources of iter-2 fix: `Real.norm_natCast` vs
`‖((g n : ℕ) : ℝ)‖` normalisation).

S4's `Active Approach` (the S3 chain SS-with-C=1/2 + Real.rpow strict
monotonicity) remains the substantive technical content already shipped
in `Erdos101OQ01.lean`; S8 ACT operates *above* that, in the asymptotic-
vocabulary layer.

## Next Action

**S8 ACT** (next picker; recipe is paste-ready in
sessions/2026-05-16-s8-statesync-postdrain.md §5 and
sessions/2026-05-15-s7-prep-sibling-audit-of-s6-bridge.md §9):

1. `git fetch origin && git rebase origin/main` (worktree).
2. Verify `Erdos101OQ01.lean` is at 471 LOC with 2 sorries (lines 111,
   302); verify parent `Erdos101Problem.lean` 758 LOC intact.
3. Add `import Mathlib.Analysis.Asymptotics.Defs` and
   `import Mathlib.Order.Filter.AtTopBot.Basic` (cheap insurance).
4. Add artifacts (i)–(iii) per the S7 PREP §9 recipe (above);
   ~105–125 LOC.
5. Docker-build via `./proofs/scripts/docker-build.sh Proofs.Erdos101OQ01`.
   Plan 2 iterations.
6. Update state.md / JSON post-ACT (iteration 8 → 9, phase PREP → ACT,
   builtItems += 3 new theorems, sorries 2 → 3 if artifact (iii) ships
   the new sorry).

Alternative S8 candidates (deferred unless S8 ACT runs into trouble):

* **Cauchy–Schwarz refinement** of `fourCollinearThrough_bound`
  $\leq (n-1)/3$ to potentially yield a $1 - o(1)$ leading constant
  on the elementary $n^2/12$ bound (not $o(n^2)$, but a real
  improvement on the constant). Still $\Theta(n^2)$.
* **Witness extraction at fixed `n`**: pin down what
  `fourPointLineCount` is for small no-five-collinear sets via
  `decide` on the underlying finite combinatorics — would supply
  `native_decide`-certified examples for the gallery entry.

## Attempt Counts

- Total attempts: 7 (S1 + S2 + S3 + S4 + S6 PREP + S7 PREP + S8 STATE-SYNC; S5 OBSERVE was CLOSED → abandoned to mechanic track)
- Current approach attempts: 0 (S8 ACT not yet attempted)
- Approaches tried: 4 (S1 scaffold + S2 lower-bound recording;
  S3 elementary real-analysis discharge; S4 constructive rephrasing
  of S3 chain; S6+S7 PREP bridge plan + audit)

## Build Status

**S4 + mechanic baseline**: GREEN at lake-pinned v4.26.0 SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (mechanic merged
parent #19099 on 2026-05-15T22:59Z + child #19255 stacked on #19099,
5 cascading errors cleared, build-verified per PR title).

`Erdos101OQ01.lean` current state on main:
- 471 LOC
- 9 theorems, 4 defs
- 2 actual `sorry`s at lines 111 (`erdos_101_oq_01`) and 302
  (`solymosi_stojakovic_lower_bound`)
- 0 `axiom` declarations
- 0 structure-encoded assumptions

`Erdos101Problem.lean` parent: 758 LOC, mechanic-stable.

**Worktree build**: not attempted (proofs/.lake is a self-symlink in
the researcher worktree; Docker invocation only via
`./proofs/scripts/docker-build.sh` from a non-researcher worktree or
the main checkout). The "GREEN" claim inherits from mechanic PR titles.

S8 ACT risk profile (per S7 PREP §3.2/§3.3 goal-state walks):
* Path A aggregator routing fixes type-coherence at the `atTop` token.
* Direction mapping corrected: `→` direct (no `ε/2`), `←` needs `ε/2`
  + `max N₀ 1` lift.
* Bug A name fix: use `Filter.eventually_atTop` (no `_iff` suffix).
* LOC budget revised to ~105–125; 2 Docker iterations.

## Blockers

None for S8 ACT — all blocking dependencies merged on main:

| Dep | PR | Merged | Resolves |
|-----|----|--------|----------|
| Parent build break | #19099 | 2026-05-15T22:59Z | v4.26.0 orphan-docstring |
| Child build break | #19255 | 2026-05-15 | 5 cascading errors |
| Bridge plan | #19221 | 2026-05-15T18:05Z | S6 PREP recipe (with errors) |
| Bridge plan audit | #19287 | 2026-05-15T18:01Z | S7 PREP corrections |
| STATE-SYNC | this PR | open | state.md + JSON refresh |

The remaining OPEN mathematical content is the main conjecture
`erdos_101_oq_01` (a $100 Erdős prize) and the `solymosi_stojakovic_lower_bound`
construction itself (algebraic geometry over finite fields, deferred).
Neither blocks S8 ACT (the IsLittleO-form artifact (iii) keeps the
existing `sorry` shape; no new sorry introduced beyond the rephrased
existing OPEN content).
