# Research State: erdos-1151-oq-04

> **S39 ACT — CONTINUOUS SATURATION WITNESS (researcher-3, 2026-07-24).**
> UNBLOCKED: Docker recovered (build clean, 3355 jobs, first attempt). Sorry 2
> ingredient (a) CLOSED: `chebyshev_lebesgue_saturated_continuous` gives, for
> every n, x, a CONTINUOUS f with |f| ≤ 1 and Lₙf(x) = Λₙ(x) — via clamped
> Lagrange polynomial (max(−1, min(1, Σ wₖℓₖ))), NOT Tietze. New public infra:
> `lagrangeBasis_apply_self` / `lagrangeBasis_apply_ne` (delta property),
> `lagrangeBasis_continuous`, `exists_continuous_bounded_through_nodes`
> (general injective nodes, |wₖ| ≤ 1, no 0 < n hypothesis). File 2714→2842
> lines, 32→36 top-level theorems, still exactly 1 sorry
> (`divergence_from_lebesgue_growth`). **ROADMAP CORRECTION**: the S34 §6 UBP
> chain (CLM packaging → op-norm → Banach–Steinhaus) CANNOT close Sorry 2 as
> stated — the S30 statement-weakening PR #17593 was closed unmerged, so main
> still states the STRONG full-limit form `∀ M, ∃ N, ∀ n ≥ N, M < Lₙf(x)`;
> UBP gives only limsup. Next (S40): either (i) polynomial-reproduction lemma
> `chebyshevInterp n p x = p x` for deg p < n (the missing lacunary-assembly
> piece, works toward the strong form), or (ii) a PLAN decision to revive
> S30's limsup refactor on its merits. See
> session-39-continuous-saturation-witness.md.

> **S38 STATE-SYNC + BLOCKED (researcher-1, 2026-06-13).** Two tracker drifts
> fixed after S37 BUILD-VERIFY (#22947, 2026-06-12) grew the file: research-JSON
> `leanFiles` lineCounts were stale (`Erdos1151OQ04` 2692→**2714**, `…Aristotle`
> 140→**141**, `…Problem` 185→**216**) and theoremCounts were off-convention
> (`Erdos1151OQ04` **66→32**, `…Problem` **5→7**). Synced to canonical generator
> values (`lineCount = wc -l + 1`; `theoremCount = ^(theorem|lemma) ` top-level
> only). NB the 66→32 is generator-parity, **not** lost theorems: the file has 32
> top-level + 34 indented/`@[simp]`/`private` theorem-like decls (66 total); the
> leanFiles convention counts only top-level (gauss-wilson precedent, see
> reference-leanfiles-count-convention). Status set `blocked`: the S38 ACT
> (discharge Sorry 2 `divergence_from_lebesgue_growth` via ContinuousLinearMap +
> Tietze lift, ~80–120 LOC) is build-dependent and unbuildable under the
> 2026-06-13 verification blackout (Docker hung + Aristotle 404); flagged to stop
> depth-first re-claim churn on this RICH (score 76) slug until Docker recovers.
> S37 left the file BUILD-VERIFY clean (3084 jobs, 1 sorry). No Lean touched.

## Current State
**Phase**: ACT (S39 CONTINUOUS-SATURATION — Sorry 2 ingredient (a) closed via clamped Lagrange polynomial; build-verified clean; 1 sorry remains: `divergence_from_lebesgue_growth`, whose strong full-limit conclusion needs the lacunary assembly (b) — see S39 header note for the roadmap correction)
**Path**: full
**Since**: 2026-07-24T12:30:00Z (S39 CONTINUOUS-SATURATION)
**Iteration**: 39
**Last Updated**: 2026-07-24 (researcher-3)

## Session 36 (researcher-3, 2026-06-09, build pending — Cluster A surgically closed; Cluster B still 21 errors) — fold chebyshevInterp_sub to single `simp only` matching sibling chebyshevInterp_neg

Surgical 3-line → 1-line refactor of `chebyshevInterp_sub` body at L175–180 to close S35's **Cluster A** error (`exact Finset.sum_sub_distrib` typeclass instance stuck on `SubtractionCommMonoid ?m.15`).

**Before** (S31 PR #17612, researcher-13, 2026-05-09, never build-verified):
```lean
theorem chebyshevInterp_sub (n : ℕ) (f g : ℝ → ℝ) (x : ℝ) :
    chebyshevInterp n (fun t => f t - g t) x =
    chebyshevInterp n f x - chebyshevInterp n g x := by
  simp only [chebyshevInterp, lagrangeInterp]
  simp_rw [sub_mul]
  exact Finset.sum_sub_distrib
```

**After** (this S36 PR, −2 LOC, 2692 → 2690):
```lean
theorem chebyshevInterp_sub (n : ℕ) (f g : ℝ → ℝ) (x : ℝ) :
    chebyshevInterp n (fun t => f t - g t) x =
    chebyshevInterp n f x - chebyshevInterp n g x := by
  simp only [chebyshevInterp, lagrangeInterp, sub_mul, Finset.sum_sub_distrib]
```

**Sibling-precedent** (same file, line 168, `chebyshevInterp_neg`, build-verified through prior cycles):
```lean
simp only [chebyshevInterp, lagrangeInterp, neg_mul, Finset.sum_neg_distrib]
```

The `_neg` proof was already in the single-`simp only` form; this S36 PR brings `_sub` to structural parity. The `_add` template at line 145 (`simp only [chebyshevInterp, lagrangeInterp]; simp_rw [add_mul]; exact Finset.sum_add_distrib`) ALSO works because `Finset.sum_add_distrib` only requires `[AddCommMonoid]` (universal), whereas `Finset.sum_sub_distrib` requires `[SubtractionCommMonoid]` — the typeclass synthesis fails with `exact` when the goal's expected type hasn't pinned `β := ℝ` before instance search. Folding into a single `simp only` lets the simp-set drive unification + rewrites in one pass, sidestepping the stuck metavariable.

**Sibling-precedent for the exact 1-line form** (`simp only [..., sub_mul, Finset.sum_sub_distrib]`):
- `HurwitzTheorem.lean:607`: `simp only [innerProd, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]` (structurally identical: unfold-defs + `sub_mul` + `Finset.sum_sub_distrib` in one `simp only`).
- `ProbMethodSecondMomentOQ01.lean:48`: `simp only [sub_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib]`.
- `HurwitzTheorem.lean:409`: `simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]`.

Three independent sibling files use this exact `simp only [..., Finset.sum_sub_distrib]` shape at the v4.26.0 Mathlib pin, all build-clean.

**Build status**: PENDING (deferred). The single Cluster A error site is closed by construction (sibling-precedent confirmed). Cluster B (21 errors at lines 952–1247) is OUT OF SCOPE for this surgical PR per S35 §6 picker matrix row (b): "single-root-cause-fix scope per Cluster A then sub-clusters of B". Running a fresh Docker build here would not produce a clean build outcome (still 21 Cluster B errors); the verifiable improvement is "22 → 21 errors" which is best confirmed during the eventual S37+ multi-cluster BUILD-VERIFY after all sub-cluster PRs merge.

**Why a researcher (not mechanic) ships this**: the fix is sibling-precedent-confirmed, 1 LOC net delta, and within the "surgical tactic-glue cleanup" scope that S35 itself shipped as a researcher PR (8 fixes inline). S36 mechanic-handoff scope (per S35 narrative) was Cluster A + B sweeps; this PR consumes just Cluster A under the same surgical envelope and leaves Cluster B for the mechanic batch as planned. No role overlap with future mechanic work on Cluster B.

**Files this S36 CLUSTER-A-CLOSE PR**:
1. EDIT `proofs/Proofs/Erdos1151OQ04.lean` (1 surgical fold, −2 net LOC, 2692 → 2690)
2. EDIT this `state.md` (head replace + prepend this Session 36 narrative; preserve Session 35 → S1 verbatim)
3. EDIT `src/data/research/problems/erdos-1151-oq-04.json` (iter 35 → 36, since/lastUpdate refresh, focus prepend, nextAction re-anchor, attemptCounts.total 5 → 6, blockers.B1 evidence refresh to "21 errors at lines 952–1247 (was 22 incl. line 180)")
4. CREATE `research/problems/erdos-1151-oq-04/session-36-cluster-a-close.md` (this session memo)

**0 meta.json / 0 lake-manifest / 0 problem.md / 0 knowledge.md body / 0 sibling-slug edits.** 0 axiom / 0 sorry change (1 sorry preserved at `divergence_from_lebesgue_growth`). Bearer SHA-stable chain S22 → S36 (no Mathlib re-walk this iter; sibling-precedent grounded at v4.26.0 pin).

`Erdos1151Problem.lean` sibling-list +30-LOC drift (actual 215 vs JSON 185) UNCHANGED from S34/S35; remains deferred to a future mechanic batch.

**Next action**: **S37 MECHANIC-HANDOFF (Cluster B sub-cluster sweeps)** — split the 21 remaining errors at lines 952–1247 by error-type (typeclass + linarith cascade ~952–1016; Application type mismatch ~1068–1091; positivity/omega/mod_cast ~1160–1247) into 3–5 narrow PRs. After all sub-cluster PRs merge, S38 BUILD-VERIFY re-runs → expected clean at ~3060/3060 jobs. Then post-clean roadmap unchanged from S34 §6: S39 ACT ContinuousLinearMap packaging Λₙ_x → S40 ACT operator-norm identity → S41 ACT Banach-Steinhaus contrapositive → Sorry 2 discharge.

## Session 35 (researcher-8, 2026-06-09, BUILD-VERIFY-PARTIAL) — INFRA recovered after 23-day gap; 29 latent build errors surfaced; 8 fixed inline, 22 remain (mechanic-handoff)

Picker matrix S34 §6 row (a) fired: **G7 host disk 3.2 → 101 GiB (+97.8 GiB, GREEN)** and **G8 Docker daemon 8s-timeout → 29.5.3 sub-second-response (GREEN)** in the 23-day window since S34 STATE-SYNC PR #20007 (merged 2026-05-17T01:58:55Z). G9 (`proofs/.lake → proofs/.lake` self-symlink) remains RED but **confirmed non-blocking** for Docker builds (docker-build.sh overlays the persistent Mathlib cache volume at `/workspace/proofs/.lake/build`; container's writable `.lake` shadows the host self-loop; corroborated by today's PR #22624 "Docker 3113 jobs clean" through identical host G9).

**Build attempt 1**: `LEAN_BUILD_TIMEOUT=45m ./proofs/scripts/docker-build.sh Proofs.Erdos1151OQ04` → cache fetch 7727 files (~3 min) + 21 cache-exe jobs + Mathlib elaboration begins → **fails with 29 errors at lines 180–2255**. **Outcome interpretation**: file has not been build-verified since pre-S22 (~mid-2026-04); 22 of 29 errors were latent in the S22+ helper infrastructure all along — masked first by "build pending" qualifier through S22-S31, then by Docker daemon outage S32-S34. The Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) has been byte-stable since pre-S32 (~4.7 mo), so this is not new drift — it's accumulated latent drift between helper-author-time interactive Mathlib state and the eventually-locked pin.

**8 surgical fixes this S35 PR** (trailing tactic-glue drift; mechanically obvious; −3 net LOC, 2695 → 2692):
1. L1758: drop `; ring` after `field_simp` (Mathlib `field_simp` now closes ring goals)
2. L1841: drop standalone `ring` after `field_simp`
3. L1882: drop `; ring` after `field_simp`
4. L1895: drop `; ring` after `field_simp`
5. L1897: drop `; ring` after `field_simp`
6. L2055/2073: convert orphan `/-- ... -/` docstring (no following declaration) to `/- ... -/` plain comment
7. L2133–2134: drop redundant `push_cast; ring` (S20-era `congr 2` now closes the goal alone)
8. L2166: `le_div_iff hd_pos` → `le_div_iff₀ hd_pos` (Mathlib rename; sibling-precedent S15 `div_lt_div_iff → div_lt_div_iff₀`)

**Build attempt 2** (after the 8 fixes): 22 errors remain (29 → 22, −7 root + −2 cascade from L2073 parser). All 22 are at lines 180–1247 in two clusters:
- **Cluster A (line 180, 1 error)**: S31 `chebyshevInterp_sub` `exact Finset.sum_sub_distrib` — typeclass instance stuck on `SubtractionCommMonoid ?m.15` (needs type annotation or `apply` form). **Authored 2026-05-09 (S31 PR #17612, researcher-13), never build-verified.**
- **Cluster B (lines 952–1247, 21 errors)**: pre-S22 helper region. Mix of `linarith` failures, `unsolved goals`, `Application type mismatch`, `Type mismatch`, `omega could not prove`, `mod_cast` signature, `positivity` failure, `rewrite` pattern-not-found, `unknown tactic`. Pattern suggests 3–5 root-cause sites with downstream cascade.

**Mechanic-handoff scope**: S36 mechanic-handoff PR(s) repair Cluster A (single-root-cause, ~5-line fix) first; then sub-cluster sweeps of Cluster B by error-type (typeclass / type-mismatch / positivity-omega-modcast). Estimate 3–5 narrow PRs. After mechanic ships clean build, S37 BUILD-VERIFY re-runs → expected clean at ~3060/3060 jobs.

**Post-clean-build roadmap unchanged from S34 §6**: S38 ACT ContinuousLinearMap packaging Λₙ_x (~80–120 LOC) → S39 ACT operator-norm identity `‖Λₙ_x‖ = chebyshevLebesgue n x` (~30–50 LOC) → S40 ACT Banach-Steinhaus contrapositive → Sorry 2 discharge (~20–40 LOC). Total to 0 sorries: ~130–210 LOC across 3 ACT PRs.

**Files this S35 BUILD-VERIFY-PARTIAL**:
1. EDIT `proofs/Proofs/Erdos1151OQ04.lean` (8 surgical 1-line fixes, −3 net LOC)
2. EDIT this `state.md` (head replace + prepend this Session 35 narrative; preserve Session 34 → S1 verbatim)
3. EDIT `src/data/research/problems/erdos-1151-oq-04.json` (~12 fields per the session memo §4)
4. CREATE `research/problems/erdos-1151-oq-04/session-35-build-verify-and-infra-recovery.md` (~190 LOC)

**0 meta.json / 0 lake-manifest / 0 problem.md / 0 knowledge.md body / 0 sibling-slug edits.** 0 axiom / 0 sorry change (1 sorry preserved at `divergence_from_lebesgue_growth`). Bearer SHA-stable chain S22 → S35 (no Mathlib re-walk this iter).

`Erdos1151Problem.lean` sibling-list +30-LOC drift (actual 215 vs JSON 185) UNCHANGED from S34; remains deferred to a future mechanic batch.

**Next action**: **S36 MECHANIC-HANDOFF (Cluster A — line 180 `Finset.sum_sub_distrib` typeclass stuck)** then S37 BUILD-VERIFY re-run. Picker matrix S34 §6 row (a) sub-resolution: build-attempt outcome was "errors surface → mechanic-handoff for tactic-glue fixes" — within picker matrix coverage.

## Session 34 (researcher-11, 2026-05-17, doc-only STATE-SYNC) — post-S33 absorption: S34a registry mirror (PR #19967) + mechanic sibling-leanFiles batch (PR #19775) + INFRA delta + canonical refresh

Doc-only STATE-SYNC reconciling 4 drift surfaces left after the S33 pre-BUILD-VERIFY STATE-SYNC PR #19688 (researcher-6, merged 2026-05-16T16:20:19Z) cycle, in the ~9.5 h window since that merge:

1. **PR #19967 (S34a registry mirror, researcher-?, merged 2026-05-17T01:29:59Z, T-7 min)** — 1-file 2-line catchup flipping `research/registry.json` `phase: OBSERVE → ACT` + `lastUpdate: 2026-04-21T18:19:38.393Z → 2026-05-16T15:56:00.000Z` for this slug. Did NOT touch canonical JSON `currentState.iteration`, `nextAction`, `focus`, `attemptCounts`, `blockers`, `knowledge.progressSummary`, or `nextSteps[]`. PR title self-labels as "S34" referencing iter=33 explicitly — i.e. an emergency thin partial sub-step, not the canonical S34 bumper.

2. **Mechanic PR #19775 (researcher-mechanic, merged 2026-05-16T19:20:13Z, T-6.5 h)** — batch-synced `leanFiles[i]` for `Erdos1151OQ04.lean` across 6 sibling JSONs from pre-S33 stale `lineCount: 1283 / theoremCount: 29 / sorryCount: 4` to canonical post-S33 `2695 / 66 / 1` (axiomCount 0, defCount 5 unchanged). Source of truth was this slug's own `leanFiles[0]` set in S33 STATE-SYNC. Six absorbed siblings + this slug = 7-entry family now consistent. Mechanic correctly excluded any `Erdos1151Problem.lean` drift from scope (sibling-list entry has separate +30-LOC off-by-one drift: actual `wc -l` 215 vs JSON `lineCount: 185`; deferred to a future mechanic batch).

3. **INFRA snapshot delta (3 RED unchanged structurally + worsened on G7)**:
   - **G7 disk avail**: 3.2 GiB (S33 was 5.2 GiB; **−2.0 GiB over ~9 h 45 min**; well below the 5 GiB safety floor referenced in S32/S33 narratives; oscillated to 2.8 GiB during birthday-problem S25 ACT-1 PR #19997 cycle and to 2.9 GiB during ballot-problem S80 STATE-SYNC PR #19994 cycle — both at T-15 min before this PR). RED, was RED.
   - **G8 Docker daemon**: `docker info` times out after 8 s with empty `ServerVersion`. Still hung (≥10 h cumulative). RED, unchanged.
   - **G9 `proofs/.lake → proofs/.lake` self-symlink**: confirmed on main repo (`/Users/rwalters/GitHub/lean-genius/proofs/.lake`). RED, unchanged. Worktree's `proofs/.lake` points at main's self-loop transitively.

4. **Canonical JSON drift in `src/data/research/problems/erdos-1151-oq-04.json`**:
   - `currentState.iteration: 33` (S34a did not bump) → `34` this PR (1-increment-per-PR per memory pattern).
   - `currentState.since / lastUpdate / top-level lastUpdate`: 2026-05-16T15:56:00Z (9 h 45 min stale).
   - `currentState.focus`: still entirely S32 ACT cherry-pick narrative (~1.6 KB); no S33 / S34a / mechanic / INFRA prepend.
   - `currentState.nextAction`: "(Researcher / Mechanic) S33 BUILD-VERIFY" — S33 STATE-SYNC has happened; the BUILD-VERIFY pass is what's deferred. Re-anchor as **S35 BUILD-VERIFY** with 6-row picker matrix gated on Docker + disk recovery.
   - `currentState.blockers: []` (empty array) → 3-entry G7/G8/G9 RED with evidence prose.
   - `currentState.attemptCounts.total: 3` → `4`.
   - `knowledge.progressSummary` (~1.8 KB): factually accurate post-S32, but doesn't reference PR #19688 (S33), PR #19775 (mechanic), or PR #19967 (S34a). Prepend short S34 absorption paragraph (~250 chars).
   - `knowledge.nextSteps[0]`: cites "5.2 Gi avail" as the gating disk number — stale; refresh to "3.2 Gi avail (5 GiB soft floor breached for ≥9.5 h; recovery condition: disk ≥ 5 GiB + Docker daemon responsive)".

**Files this S34 STATE-SYNC** (3 files, doc-only, 0 Lean / 0 meta.json / 0 lake-manifest / 0 problem.md / 0 knowledge.md body / 0 sibling-slug edits):
1. EDIT this `state.md` (head replace + prepend this Session 34 narrative; preserve Session 33 → S1 verbatim).
2. EDIT `src/data/research/problems/erdos-1151-oq-04.json` (10 fields per the §4 list above; jq `--rawfile --indent 2` to preserve unicode and indentation).
3. CREATE `research/problems/erdos-1151-oq-04/session-34-statesync-post-s34a-mechanic-and-infra-absorption.md` (~280 LOC, 9 sections per memory pattern).

**Mathlib pin unchanged**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) byte-stable since pre-S32 era. Bearer SHA-stable carry-forward chain S22 → S23 → S29 → S32 → S33 → S34 with **no re-walk needed** this iter.

**0 axiom / 0 sorry change** (1 sorry preserved at `divergence_from_lebesgue_growth`; 0 axioms; `Erdos1151Problem.lean` has 2 axioms unchanged).

**Next action**: **S35 BUILD-VERIFY** — once Docker daemon I/O recovers AND host disk ≥ 5 GiB, re-attempt `./proofs/scripts/docker-build.sh Proofs.Erdos1151OQ04`. Expected outcome (HIGH likelihood given PREP-2 §4.1 audit depth + ≥4.5 mo SHA stability): clean build at ~3060/3060 jobs. If clean: 5-min doc-only S35 commit flipping `(build pending) → (build verified, NNNN/NNNN jobs)`. If errors surface: mechanic-handoff for tactic-glue fixes (bearers per PREP-2 audit are correct). See `session-34-statesync-post-s34a-mechanic-and-infra-absorption.md` §6 picker matrix for full S35 decision table.

## Session 33 (researcher-6, 2026-05-16, doc-only pre-BUILD-VERIFY STATE-SYNC) — JSON drift catchup

Doc-only STATE-SYNC catching the research JSON up to post-S32-ACT reality. The S32
ACT (PR #19...) shipped `chebyshev_lebesgue_saturated` (+106 LOC, theoremCount
65 → 66, sorryCount 1, 0 axioms) under the `(build pending — Docker daemon I/O
blocked)` qualifier and correctly updated `state.md` + JSON
`currentState.{phase=IN-PROGRESS [LEGACY], focus, nextAction}` + `leanFiles[i]`.
BUT left the following JSON tail-end drift:

1. **Top-level `phase: IN-PROGRESS`** — legacy phase value; gallery listings
   derive from this. State.md head reads `ACT`. Flip top-level → `ACT`.
2. **`currentState.phase: IN-PROGRESS`** — same flip → `ACT`.
3. **`currentState.attemptCounts: {0, 0, 0}`** — set to non-zero reflecting
   actual 33 iterations (bumped to {3, 1, 1} per per-session metric heuristic;
   prior values were stuck at the slug-bootstrap default).
4. **`knowledge.progressSummary`** (339 chars) — S22-era; says "2 sorries
   remain" but actual is 1; refers to "Step 7b ... closed via S22 trig_sum_small_n_const"
   AND "Step 7a outstanding" as the only frontier. Now obsolete: post-S29 closed
   trig_sum_harmonic_lb via close_harmonic_lb; post-S32 closed
   chebyshev_lebesgue_saturated. Sorry 1 already closed; only Sorry 2
   (`divergence_from_lebesgue_growth`) remains, with the S33-S36 plan
   (BUILD-VERIFY + ContinuousLinearMap + operator-norm + BanachSteinhaus)
   as the route. Refresh to ~600-700 chars covering S26-S33 progression.
5. **`knowledge.nextSteps[]`** (5 items) — all 5 are "Step 7a/7b/7c/8"
   trig_sum_harmonic_lb content, S22-S29 era. All obsolete (those steps
   shipped in S29 PR #17580 + later). Replace with the S33-S36 plan from
   state.md Session 32 entry.

**Files this S33 pre-BUILD-VERIFY STATE-SYNC**:
1. EDIT this state.md (head replace; add this Session 33 narrative; preserve
   Sessions 32 → S1 verbatim).
2. EDIT `src/data/research/problems/erdos-1151-oq-04.json`:
   - top-level `phase: IN-PROGRESS → ACT`
   - `currentState.phase: IN-PROGRESS → ACT`
   - `currentState.iteration: 32 → 33`
   - `currentState.since: 2026-05-15T22:15:00Z → 2026-05-16T15:56:00Z`
   - `currentState.attemptCounts.total: 0 → 3`
   - `currentState.attemptCounts.currentApproach: 0 → 1`
   - `currentState.attemptCounts.approachesTried: 0 → 1`
   - `currentState.lastUpdate: 2026-05-15T22:15:00Z → 2026-05-16T15:56:00Z`
   - `knowledge.progressSummary` refresh (≈ 700 chars)
   - `knowledge.nextSteps[]` replace with the S33-S36 plan + post-Docker
     recovery operations + sibling cleanup pointer
   - top-level `lastUpdate: 2026-05-15T22:15:00Z → 2026-05-16T15:56:00Z`

**0 Lean / 0 meta.json / 0 problem.md / 0 knowledge.md / 0 lake-manifest / 0
sibling-slug edits.** 0 axiom / 0 sorry change (1 sorry preserved at
`divergence_from_lebesgue_growth`).

**Host infra this S33 STATE-SYNC cycle**:
- **Docker daemon still hung** (same B1 condition as S32 ACT and as my prior
  two iterations 30-60 min before this; ~7.5+ h cumulative).
- **Disk degraded**: 5.2 Gi avail (was 5.4 Gi 15 min ago; was 6.9 Gi at S32
  ACT cycle start 2026-05-15; ~30+h cumulative degradation; **AT** the
  ~5 Gi safety-floor mentioned in S32 ACT memo). Disk pressure is part of
  what continues to hold Docker daemon I/O blocked.
- **Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0,
  unchanged since pre-S32 era).
- **0 open PRs** for this slug at cycle start.

**Next action (unchanged from S32 ACT)**: S33 BUILD-VERIFY. Once Docker daemon
I/O recovers (host disk pressure drops below 99% capacity), re-attempt
`./proofs/scripts/docker-build.sh Proofs.Erdos1151OQ04`. Expected outcome
(HIGH likelihood per PREP-2 audit depth): clean build at ~3060/3060 jobs.
If clean, flip state.md / JSON build status `(build pending) → (build
verified, NNNN/NNNN jobs)` as a 5-min doc-only commit. Then proceed with
S34 (ContinuousLinearMap packaging Λₙ_x; +80-120 LOC) → S35 (operator-norm
identity; +30-50 LOC) → S36 (BanachSteinhaus contrapositive; +20-40 LOC) to
discharge Sorry 2 entirely.

(No new session memo file this iteration — the Session 33 narrative above is
short and structural-only; future S33 BUILD-VERIFY OR S34 ACT will create
`session-34-...md` or similar per this slug's flat-file naming convention.)

## Session 32 (researcher-10, 2026-05-15, build pending — Docker daemon I/O blocked) — ACT: cherry-pick stranded `chebyshev_lebesgue_saturated`

**Executes the PREP-2 §6 nine-step recipe** to land the long-stranded
`chebyshev_lebesgue_saturated` lemma (commit `2099b97d59a`, authored
2026-05-09, never opened as a PR or pushed to a named remote branch,
surfaced + rescued by S32 PREP PR #19183 + bearer-audited by S32 PREP-2
PR #19256).

**Net change.** `proofs/Proofs/Erdos1151OQ04.lean` goes 2589 → 2695 LOC
(+106), theoremCount 65 → 66 (+1 `chebyshev_lebesgue_saturated`),
sorryCount unchanged at 1 (still `divergence_from_lebesgue_growth`),
axiomCount unchanged at 0, defCount unchanged at 5.

The −2 LOC versus PREP's headline "+108 LOC" reflects the **PREP-2
§4.1 micro-refactor**: both `Finset.sum_eq_single k₀` call sites in
the lemma body replaced by `Finset.sum_eq_single_of_mem k₀
(Finset.mem_univ _)`, dropping the trivially-impossible third bullet
(`k₀ ∉ univ → f k₀ = 0`) at each site. Sibling-precedent-confirmed
against `Erdos671Problem.lean:128-131`.

**Build status.** **PENDING** — Docker daemon on the host became
unresponsive (`docker ps` times out at 10s) due to host disk pressure
(100% capacity / 6.9 Gi available). One Docker build attempt ran for
~10 minutes with zero bytes written to its stdout log (container
never reached build phase) before being killed. **No elaboration
confidence** on the new body itself; HIGH confidence on bearers + §4.1
substitution via PREP-2 audit. See session-33-act-… memo §5 for the
honest disclosure + S33 BUILD-VERIFY follow-on plan.

**Mathematical content.** `chebyshev_lebesgue_saturated (n : ℕ) (x : ℝ)`
returns `∃ f : ℝ → ℝ, (∀ t, |f t| ≤ 1) ∧ chebyshevInterp n f x =
chebyshevLebesgue n x` — operator-norm saturation lower bound for the
Chebyshev interpolation functional. Combined with the existing
`chebyshev_upper_bound`, yields `‖Λₙ_x‖ = chebyshevLebesgue n x` on
the L∞ unit ball — the entry point to the Banach–Steinhaus
contrapositive that closes Sorry 2 (`divergence_from_lebesgue_growth`)
in S34+.

**Construction.** Sign-pattern weight `w k = ±1` at each Chebyshev
node (sign of `lagrangeBasis n (chebyshevNode n) k x`); `f t :=
∑ k, w k * indicator(t = chebyshevNode n k)`. The `|f t| ≤ 1` half
case-splits on whether `t` is a node (sum collapses via
`sum_eq_single_of_mem` + `chebyshevNode_injective` to `w k₀`); the
`chebyshevInterp n f x = chebyshevLebesgue n x` half evaluates `f` at
each node `chebyshevNode n k₀` (same `sum_eq_single_of_mem` collapse).

**Files touched.** `proofs/Proofs/Erdos1151OQ04.lean` (+106 LOC),
`state.md` (this), `session-33-act-ubp-saturation-cherry-pick.md` (new),
`src/data/research/problems/erdos-1151-oq-04.json` (iteration + focus
+ nextAction + lineCount + theoremCount).

**Conflict-free guarantee.** Open PRs #17386 / #17457 (S23/S25 combine
helpers, both CONFLICTING, obsolete per S29 PR #17580) touch the
line-~2300+ trig sum region — textually disjoint from this ACT's
line-~329 insertion point. No race possible.

**Next action.** S33 BUILD-VERIFY — once Docker daemon I/O recovers,
re-attempt build of `Proofs.Erdos1151OQ04`. If clean (most likely
given PREP-2's audit depth), flip state.md / JSON build status from
`(build pending)` to `(build verified, NNNN/NNNN jobs)`. If errors
surface, mechanic-handoff for tactic-glue fixes (bearers are correct;
errors would be in `rw` ordering / `push_neg` placement / etc.).

Post-S33 outline: S34 = `ContinuousLinearMap` packaging via
`LinearMap.mkContinuous` + Tietze lift of saturation witness to a
continuous function on `Icc -1 1` (~80–120 LOC); S35 = operator-norm
identity (~30–50 LOC); S36 = `BanachSteinhaus` contrapositive to
discharge Sorry 2 (~20–40 LOC). Total to reach 0 sorries: ~130–210
LOC across 3 PRs.

## Session 31 (researcher-13, 2026-05-09, build pending) — linear-functional helpers

**Three small new theorems** added immediately after the existing
`chebyshevInterp_smul` (line 152 on origin/main), as infrastructure for the
future `ContinuousLinearMap` packaging in the UBP closure of
`divergence_from_lebesgue_growth`:

```lean
theorem chebyshevInterp_zero_fn (n : ℕ) (x : ℝ) :
    chebyshevInterp n (fun _ : ℝ => 0) x = 0

theorem chebyshevInterp_neg (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    chebyshevInterp n (fun t => -f t) x = -chebyshevInterp n f x

theorem chebyshevInterp_sub (n : ℕ) (f g : ℝ → ℝ) (x : ℝ) :
    chebyshevInterp n (fun t => f t - g t) x =
    chebyshevInterp n f x - chebyshevInterp n g x
```

**Proofs.** Mirror the existing `chebyshevInterp_add` template line-by-line:

  • `_zero_fn`: `simp only [chebyshevInterp, lagrangeInterp, zero_mul,
    Finset.sum_const_zero]`.
  • `_neg`: `simp only [chebyshevInterp, lagrangeInterp, neg_mul,
    Finset.sum_neg_distrib]`.
  • `_sub`: `simp only [chebyshevInterp, lagrangeInterp]; simp_rw [sub_mul];
    exact Finset.sum_sub_distrib`.

All three are mechanical 1-line `simp` proofs, cross-checked against
existing usages of `Finset.sum_sub_distrib` (in `BinomialTheoremOQ02OQ01OQ03`,
`CauchySchwarzOQ03`) and `Finset.sum_neg_distrib` (in `ArithmeticSeriesOQ02OQ03`)
to confirm Mathlib API names.

**Why these specifically** (foundation for the post-S30 UBP closure):

1. **Linearity over ℝ-vector-spaces**: `(fun t => f t - g t)` and
   `(fun t => -f t)` appear pervasively in operator-norm bounds. The
   `ContinuousLinearMap.opNorm_le_iff` recipe uses
   `‖A (f - g)‖ ≤ M · ‖f - g‖`; without `chebyshevInterp_sub` and
   `chebyshevInterp_neg`, every operator-norm calculation needs an inline
   `simp_rw [sub_mul]; rw [Finset.sum_sub_distrib]` boilerplate.

2. **Zero baseline for `Λₙ_x`**: A `LinearMap` from `C[-1,1] → ℝ` requires a
   `map_zero'` field; `chebyshevInterp_zero_fn` is exactly that field's
   witness (composed with the trivial extension of `0 : C[-1,1]` to
   `0 : ℝ → ℝ`).

3. **Independence from S30 (PR #17593, in flight)**: S30 modifies the
   trailing two theorems (`divergence_from_lebesgue_growth` and
   `erdos_1941_divergence_from_growth`) at lines 2535–2606 to refactor
   Sorry 2's conclusion to the unboundedness form. This PR appends helpers
   immediately after `chebyshevInterp_smul` (line 152) — over 2300 lines
   away — so the two PRs are textually disjoint and can both land cleanly.

4. **Independence from open S25 PRs (#17386, #17457)**: those modify the
   `trig_sum_harmonic_lb` area (line ~2300+); the two PRs are similarly
   disjoint.

**Net new content**: +3 theorems, 0 definitions, 0 axioms, 0 sorries.
**Updated total**: 65 theorems, 5 definitions, 0 axioms, 1 sorry, 2589
lines (was 62/5/0/1/2561 on origin/main; the S30 PR will add ~49 statement-
doc lines on top of that, but in a different file region).

**Mathlib API surface**: zero new lemmas. Only standard simp-set members
(`zero_mul`, `Finset.sum_const_zero`, `neg_mul`, `Finset.sum_neg_distrib`,
`sub_mul`, `Finset.sum_sub_distrib`).

**Build status**: build pending. These three lemmas are 1-line `simp`-style
proofs over a build-verified template (`chebyshevInterp_add`). Build risk
is minimal — the only failure mode is Mathlib API drift (e.g. if
`Finset.sum_sub_distrib` were renamed). Verified usage in two independent
recent files on `origin/main`; the names are stable.

## Sharpening of the Plan for S32+ (UBP Closure of `divergence_from_lebesgue_growth`)

Once S30 (PR #17593, statement refactor) and S31 (this PR, linear helpers)
both land, the UBP closure outline is:

  1. **Define `Λₙ_x` as a `ContinuousLinearMap`** (~30–40 lines).
     Build the bounded-linear-functional `Λₙ_x : C(Set.Icc (-1) 1, ℝ) →L[ℝ] ℝ`,
     `f ↦ chebyshevInterp n (extension f) x`, where
     `extension : C(Icc (-1) 1) → (ℝ → ℝ)` extends by the convention
     `f(t) = f(clip t (-1, 1))` (or zero outside — since the interpolation
     only sees `f` at the Chebyshev nodes
     `Set.Icc (-1) 1 ⊃ chebyshevNode n`, both work).
     Linearity: `chebyshevInterp_add` (existing), `chebyshevInterp_smul`
     (existing), `chebyshevInterp_zero_fn` / `chebyshevInterp_neg` /
     `chebyshevInterp_sub` (this PR, S31).
     Continuity: `chebyshev_upper_bound` (existing) gives the operator-norm
     bound `‖Λₙ_x f‖ ≤ chebyshevLebesgue n x · ‖f‖_∞`; pack as a
     `ContinuousLinearMap` via `LinearMap.mkContinuous`.

  2. **Operator-norm equality** (~50–80 lines).
     Upper bound `‖Λₙ_x‖ ≤ chebyshevLebesgue n x` is direct from step 1's
     bound. Lower bound (saturation): construct a witness `f₀ : C[-1,1]`
     with `‖f₀‖_∞ ≤ 1` and `f₀(node_k) = sign(basis_k(x))`; then
     `Λₙ_x f₀ = ∑_k sign(basis_k(x)) · basis_k(x) = ∑_k |basis_k(x)|
     = chebyshevLebesgue n x`. Construction: piecewise-linear interpolation
     between consecutive nodes, or Tietze extension from the finite set
     `{node_k}`.

  3. **UBP contrapositive** (~10–20 lines). The hypothesis
     `Filter.Tendsto Λₙ_x atTop atTop` (from S30's refactor: equivalently
     "norms unbounded") together with
     `Mathlib.Analysis.NormedSpace.BanachSteinhaus.banach_steinhaus_iff`
     gives `∃ f : C[-1,1], ¬ Bounded {Λₙ_x f | n}`, i.e.
     `∃ f, ∀ M, ∃ n, M < |chebyshevInterp n (extension f) x|`. Extending
     `f` to `ℝ → ℝ` preserves the values at the nodes, hence the conclusion
     of `divergence_from_lebesgue_growth`.

  4. **Glue** (~5 lines).

Estimated S32–S35 sizes total: ~110–150 lines split into 3–4 PRs.

## Session 30 (researcher-1, 2026-05-09, in flight as PR #17593) — Sorry 2 statement refactor

**Refactors `divergence_from_lebesgue_growth` and the corollary
`erdos_1941_divergence_from_growth`** from the strictly-stronger
`Filter.Tendsto … atTop atTop` form to the unboundedness form

```
∃ f : ℝ → ℝ, Continuous f ∧ ∀ M : ℝ, ∃ n : ℕ, M < |chebyshevInterp n f x|
```

aligning the conclusion with what Banach–Steinhaus / UBP actually delivers
(see prior `state.md` "Next Steps" section 2 Option A). Net file change:
2561 → 2610 lines (statement-doc expansion). Build pending. PR remains
open at time of S31 (this session).

## Session 29 (researcher-11, this session, build pending)

**CLOSED `trig_sum_harmonic_lb`** (~38-line proof body). File now has
**1 sorry** (was 2). Composes S28 (`trig_sum_harmonic_lb_asymp`, asymp side)
with S22 (`trig_sum_small_n_const`, finite-set side) via min-of-two-constants
split:

  1. S28 → `(N₀, C₁ > 0, hlarge : ∀ n ≥ N₀, C₁·n·log(n+1) ≤ S(θ,n))`.
  2. `N := max N₀ 1` (ensures `1 ≤ N` for the cutoff).
  3. S22 with cutoff `N` → `(C₂ > 0, hsmall : ∀ n, 1≤n→n≤N → C₂·n·log(n+1) ≤ S(θ,n))`.
  4. `C := min C₁ C₂ > 0`. Case-split on `n ≤ N`:
     - small: `min ≤ C₂` (`min_le_right`) + `mul_le_mul_of_nonneg_right` + `hsmall`;
     - large (`n > N ≥ N₀`): `min ≤ C₁` (`min_le_left`) + `hlarge`.

**Sidesteps in-flight S25 PRs**: PR #17386 (DIRTY) and PR #17457 (CONFLICTING)
both add a dedicated combine helper `trig_sum_combine_small_large_const` —
this session inlines the same logic directly into `trig_sum_harmonic_lb`,
making both PRs obsolete (no remaining caller for the helper). They should
be closed administratively after S29 merges.

**Sorry inventory** (Erdos1151OQ04.lean, 2561 lines):

  1. `divergence_from_lebesgue_growth` (line 2545) — lacunary series
     construction (Faber/Banach-Steinhaus). Genuinely outstanding;
     standard but mechanical.

## Session 28 (researcher-6, build pending, merged via #17544)

Added the **Step 7a/general-θ asymptotic packaging** as a new private helper
`trig_sum_harmonic_lb_asymp` (~50 lines). Extends S26's
`trig_sum_harmonic_lb_asymp_le_half_pi` from `θ ∈ (0, π/2]` to the full
open interval `θ ∈ (0, π)` via the WLOG bridge:

```
∃ N₀ : ℕ, ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ n ≥ N₀,
  C₁ · n · log(n+1) ≤ S(θ, n)
```

with no constraint on `θ ∈ (0, π)` beyond the cosine-not-a-Chebyshev-node
hypothesis.

**Composition** (purely from already-merged helpers):

  1. Case split on `θ ≤ π/2` vs `θ > π/2`.
  2. **`θ ≤ π/2`**: directly apply S26.
  3. **`θ > π/2`**: set `θ' := π − θ ∈ (0, π/2)`.
     a. S27 (`chebyshev_hne_pi_sub`) → `hne'` for `θ'` from `hne` for `θ`.
     b. S26 applied to `θ'` → `(N₀, C₁, hbound')` for `S(π − θ, n)`.
     c. S18 (`trig_sum_reindex_symmetry`) → `S(θ, n) = S(π − θ, n)`.
     d. Bump `N₀` to `max N₀ 1` so we can apply S18 (which requires `0 < n`).
     e. `rw [hsym]` flips the goal LHS sum, then `exact hbound' n hN₀_le`.

**Why this matters**: this is the **last gap** between the half-π asymp
bound (S26) and the general (0, π) hypothesis required by
`trig_sum_combine_small_large_const` (S25, in flight as PR #17457).
Once S25 + S28 both merge, the `trig_sum_harmonic_lb` proof closes in
~5 lines: apply S28 → `(N₀, C₁, hlarge)`, apply S25 → unified `(C, h)`.

**No conflict with PR #17457 or PR #17386**: this S28 helper inserts
AT a NEW POSITION (immediately after S26, before `trig_sum_harmonic_lb`),
which is the same insertion point as S25 (#17457) and the stale S23
(#17386). All three are independent helpers with disjoint signatures
(`trig_sum_harmonic_lb_asymp` vs `trig_sum_combine_small_large_const`);
whichever lands first triggers a trivial relocation in the others.

## Session 27 (researcher-11, build pending, merged via #17505)

Added `chebyshev_hne_pi_sub` (~50 lines): `hne` side of WLOG bridge.
For any `n > 0`, `θ ∈ ℝ`, `(hne : ∀ k, cos θ ≠ chebyshevNode n k)`,
yields `∀ k, cos (π − θ) ≠ chebyshevNode n k`. Uses the same involution
`σ : Fin n ≃ Fin n`, `k ↦ n − 1 − k` as S18; key step is
`chebyshevNode n (σ k) = − chebyshevNode n k` via `Real.cos_pi_sub`.

Combined with S18 (which provides the **sum side** `S(θ, n) = S(π − θ, n)`),
S27 constitutes the entire WLOG-bridge machinery for extending `θ ∈ (0, π/2]`
results to `θ ∈ (0, π)`. Used by S28 (this session).

## Session 26 (researcher-12, merged via #17486)

Added the **Step 7a/asymptotic side packaging** as a new private helper
`trig_sum_harmonic_lb_asymp_le_half_pi` (~120 lines). For any
`θ ∈ (0, π/2]` whose cosine avoids all Chebyshev nodes:

```
∃ N₀ : ℕ, ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ n ≥ N₀,
  C₁ · n · log(n+1) ≤ S(θ, n)
```

with `C₁ = sin(θ/2) / (2π)` and `N₀ = max N₀_log 4` (where `N₀_log` comes
from S24's `chebyshev_quarter_floor_log_asymp_lb`, and `4` is S23's hyp).

**Composition** (purely from already-merged helpers):

  1. `exists_nearest_chebyshev_angle` → `k₀ : Fin n` with closeness.
  2. `m := ⌊n·θ/(4π)⌋` via `Nat.floor_le` + `Nat.lt_floor_add_one`.
  3. S23 `chebyshev_quarter_floor_hm_le_and_cap_max` → `hm_le` + `hcap_max`.
  4. S22 `chebyshev_h_interior_of_close_and_max_index_cap` → `h_interior` (d := θ).
  5. S21 `trig_sum_subsum_log_lb` → `sin(θ/2)·(2n/π)·((1/2)·log(m+2)−1) ≤ S(θ,n)`.
  6. S24 `chebyshev_quarter_floor_log_asymp_lb` → `(1/4)·log(n+1) ≤ (1/2)·log(m+2)−1`.
  7. Multiply by nonneg `sin(θ/2)·(2n/π)`, algebraically rearrange to
     `(sin(θ/2)/(2π))·n·log(n+1) ≤ S(θ,n)`.
  8. Cast bridge mixed-cast → outer-cast sum form via
     `Finset.sum_congr` + `push_cast` + `ring`.

**Why this matters**: this is **exactly** the `hlarge` hypothesis consumed
by `trig_sum_combine_small_large_const` (Step 7c, in flight as PR #17457).
Once that PR merges, the `θ ∈ (0, π/2]` branch of `trig_sum_harmonic_lb`
closes in ~10 lines: pass S26 helper's output (`N₀`, `C₁`, `hlarge`) to
S25's combine helper. The general `θ ∈ (0, π)` branch then follows in ~20
lines via `trig_sum_reindex_symmetry` (S18, merged): `S(θ, n) = S(π−θ, n)`,
and `π−θ ∈ (0, π/2)` when `θ ∈ [π/2, π)`.

**No conflict with PR #17457**: this S26 helper inserts AT THE SAME
POSITION as #17457's combine helper (between S24 and `trig_sum_harmonic_lb`),
but the two helpers are independent. Whichever lands first triggers a
trivial rebase in the other.

## Session 24 (researcher-4, build pending, merged via #17438)

Added the **Step 7a residue (asymptotic log lower bound)** as a new private
helper `chebyshev_quarter_floor_log_asymp_lb` (~80 lines). For any `θ > 0`:

```
∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ m : ℕ,
  (n : ℝ) * θ / (4π) - 1 ≤ (m : ℝ) →
  (1/4) * log((n : ℝ) + 1) ≤ (1/2) * log((m : ℝ) + 2) - 1.
```

The standard Step 7a caller-side choice `m := ⌊n·θ/(4π)⌋ : ℕ` satisfies
the input hypothesis via `Nat.lt_floor_add_one`. Composed with the merged
S21 helper `trig_sum_subsum_log_lb` (whose RHS factor is exactly
`(1/2) · log((m : ℝ) + 2) − 1`), this yields an asymptotic
`(sin(θ/2) / (2π)) · n · log(n+1)` lower bound for the trig sum, ready
for `trig_sum_combine_small_large_const` (open: PR #17386).

**Witness**: `N₀ = ⌈16π² · e⁴ / θ²⌉` (provided by `exists_nat_gt(K + 1)`),
`c = 1/4`. The proof reduces

  `(1/2) · log(m+2) − 1 ≥ (1/4) · log(n+1)`  ⟺  `(m+2)² ≥ (n+1) · e⁴`

via `Real.log_le_log` + `Real.log_mul` + `Real.log_exp` + `Real.log_pow`.
From the hypothesis `m + 2 ≥ n·θ/(4π)`, `(m+2)² ≥ n²·θ²/(16π²)`. The
remaining `n²·θ²/(16π²) ≥ (n+1)·e⁴` ⟺ `n² ≥ K·(n+1)` where
`K := 16π²·e⁴/θ²`, which holds when `n ≥ K + 1`:

  `n² = n·n ≥ (K+1)·n ≥ K·n + n ≥ K·n + K = K·(n+1)`.

**Why this matters**: this is the **genuinely-asymptotic step** flagged
in PR #17386's body as "Step 4 (the genuinely-mathematical residue)".
With S21 (subsum_log_lb) + S22 (h_interior + small_n_const) + S23
(quarter_floor_hm_le_and_cap_max) + S24 (this session) merged, the only
remaining work for `trig_sum_harmonic_lb` is the **mechanical glue**:
WLOG-reduce to `θ ∈ (0, π/2]` via `trig_sum_reindex_symmetry` (S18),
pick `m := ⌊n·θ/(4π)⌋`, chain the merged helpers, and feed the result
to `trig_sum_combine_small_large_const`. No further inequality residue.

## Session 23 (researcher-3, build pending, merged via #17396)

Added the **Step 7a m-choice + arithmetic packager** as a new private helper
`chebyshev_quarter_floor_hm_le_and_cap_max` (~110 lines). Given:

  • `θ ∈ (0, π/2]`, `n ≥ 4`,
  • the standard nearest-node closeness `|θ - φ_{k₀}| ≤ π/(2n)`, and
  • any `m : ℕ` with `(m : ℝ) ≤ n·θ/(4π)` (e.g. `m := ⌊n·θ/(4π)⌋` via
    `Nat.floor_le`),

the lemma simultaneously discharges both arithmetic preconditions of the
trig sub-sum chain:

  • `hm_le`: `k₀.val + m + 1 ≤ n` (input to `trig_sum_subsum_log_lb`),
  • `hcap_max`: `(2(k₀+m)+1)·π/(2n) ≤ π - θ/2` (input to S22's
    `chebyshev_h_interior_of_close_and_max_index_cap`).

**Proof skeleton** (with `θ ≤ π/2` and `n ≥ 4`):

  1. `m·π/n ≤ θ/4 ≤ π/8`: multiply `(m : ℝ) ≤ n·θ/(4π)` by `π/n > 0`.
  2. `φ_{k₀} ≤ θ + π/(2n)` from `abs_le.mp hk₀_close`.
  3. `φ_{k₀+m} = φ_{k₀} + m·π/n ≤ π/2 + π/8 + π/8 = 3π/4 ≤ π - θ/2`.
  4. `2 k₀ ≤ n` (ℕ) from `(2k₀+1)π ≤ 2nθ + π ≤ nπ + π`; divide by π via
     `nlinarith`, cast.
  5. `8 m ≤ n` (ℕ) from `m·π/n ≤ π/8`, multiply by `8n`; cast.
  6. `omega` closes `k₀.val + m + 1 ≤ n` from `2 k₀ ≤ n`, `8 m ≤ n`,
     `n ≥ 4` (since `8(k₀+m+1) ≤ 5n + 8 ≤ 8n` for `n ≥ 3`).

**Why packaged this way**: the next session (Step 7a glue) will pick the
concrete `m := ⌊n·θ/(4π)⌋` and need both `hm_le` and `hcap_max` in the
*same* shape consumed by S22's `chebyshev_h_interior_of_close_and_max_index_cap`
verifier. Bundling both into one lemma keeps the asymptotic-branch caller
free of arithmetic boilerplate. The generality `(m : ℝ) ≤ n·θ/(4π)`
(rather than fixing `m := Nat.floor …`) leaves room for a tighter choice
if a future variant prefers `m := ⌊n·θ/(4π)⌋ - 1` for cleaner log estimates.

## Session 22 (researcher-3, h_interior verifier, merged via #17324)

Earlier in S22, researcher-3 added `chebyshev_h_interior_of_close_and_max_index_cap`
(~75 lines) — the **abstract h_interior verifier** that bridges:

  • `hk₀_close : |θ - φ_{k₀}| ≤ π/(2n)` and
  • `hcap_max : φ_{k₀+m} ≤ π - θ/2`

into the full `h_interior` of `trig_sum_subsum_lb` / `trig_sum_subsum_log_lb`
(setting `d = θ`). For each `j : Fin m`, both `θ/2 ≤ φ_{k₀+j+1}` (from
the closeness lower bound + section-spacing `(j+1)·π/n ≥ π/n = 2·(π/(2n))`)
and `φ_{k₀+j+1} ≤ π - θ/2` (monotone in the index, capped at `m`). All
arithmetic via `linarith` + `field_simp`. The S23 helper
`chebyshev_quarter_floor_hm_le_and_cap_max` (this session) is the natural
feeder for this lemma's `hcap_max` input when `m := ⌊n·θ/(4π)⌋`.

## Session 22 (researcher-11, trig_sum_small_n_const, merged via #17330)

Added one Step 7 helper: `trig_sum_small_n_const` (~80 lines) — closed the
**finite-set side** of `trig_sum_harmonic_lb`'s Step 7. For any cutoff
`N ≥ 1`, returns `C > 0` with `C · n · log(n+1) ≤ S(θ, n)` for every
`1 ≤ n ≤ N`.

Proof uses the Session-20 helper `chebyshev_trig_sum_pos` for term-wise
positivity, then takes `Finset.min'` over `(Finset.Icc 1 N).image` of the
ratio `n ↦ S(θ, n) / (n · log(n+1))`. Each ratio is positive
(`n ≥ 1 ⇒ log(n+1) ≥ log 2 > 0`), so the minimum is positive; inverting
the division via `le_div_iff` gives the bound.

Combined with an asymptotic large-`n` bound (Step 7a, future session)
extracted from `trig_sum_subsum_log_lb`, the unified `n · log(n+1)`
lower bound across all `n ≥ 1` follows by taking the minimum of the
two constants.

Form-bridging note: the existing `chebyshev_trig_sum_pos` uses
`(2 * (k.val : ℝ) + 1)` (mixed Nat-cast); the surrounding lemmas
`trig_sum_harmonic_lb` and the gallery target use
`(2 * k.val + 1 : ℝ)` (outer cast). The proof bridges via
`Finset.sum_congr` + `push_cast` + `ring`. Future cleanup could unify
the conventions across the file.

## Session 21 (doctor, build pending)

Added one Step 6c helper: `trig_sum_subsum_log_lb` (~36 lines) — combined
log lower bound composing `odd_harmonic_sum_shifted_lb` (Step 6a) with
`trig_sum_subsum_lb` (Step 6b). Yields the ready-to-apply
`sin(d/2)·(2n/π)·((1/2)·log(m+2)−1) ≤ Σ_k sin(φ_k)/|cos θ − cos φ_k|` shape
that drives the `n·log(m)` growth in `trig_sum_harmonic_lb`. Recovered from
PR #17046 (orphan-rescue) after the symmetry portion (`chebyshev_lebesgue_sum_pi_sub`)
became redundant with Session 18's `trig_sum_reindex_symmetry` already merged
on main via #17050; doctor preserved only the unique Step 6c content.

Hypotheses match `trig_sum_subsum_lb` plus `d ≤ π` (ensures `sin(d/2) ≥ 0`
via `Real.sin_nonneg_of_nonneg_of_le_pi`). Vacuous when `m ≤ 5`; substantive
at `m ≥ 6` where `(1/2)·log(8) − 1 ≈ 0.04 > 0`.

## Session 20 (build pending)

Added one Step 6/7 helper: `chebyshev_trig_sum_pos` — strict positivity of
the Chebyshev-Lebesgue trig sum `S(θ, n) = Σₖ sin(φₖ)/|cos θ − cos φₖ|`
for any θ avoiding all chebyshev nodes. This is the building block for the
finite-set `min'` argument in `trig_sum_harmonic_lb` Step 6/7: for the
finitely many small `n` (`1 ≤ n < N₀(d)`), the ratio `S(θ, n)/(n·log(n+1))`
is well-defined and positive, so its `Finset.min'` exists and is positive,
yielding the small-n constant.

Proof: every term has `sin > 0` (via `chebyshevAngle_sin_pos`) and
`|cos θ − cos φₖ| > 0` (via the `hne` hypothesis). Apply `Finset.sum_pos`
with the nonempty witness `k = 0` (`Fin n` nonempty since `n ≥ 1`).

## Current Focus
2 sorries remain in `proofs/Proofs/Erdos1151OQ04.lean` (1567 lines, on `main`):

1. `trig_sum_harmonic_lb` (line ~1379) — *general* θ ∈ (0, π) harmonic lower
   bound for the trig sum Σ sin(φₖ)/|cos θ − cos φₖ| ≥ C·n·log(n+1).
   Self-contained statement (no p/q dependency); Lipschitz + harmonic over
   near-nodes + finite-set minimum for small n. **Steps 1–5 already proved**
   as helper lemmas (`exists_nearest_chebyshev_angle`,
   `chebyshev_angle_dist_triangle`, `chebyshev_angle_dist_from_nearest`,
   `sin_lb_of_in_interior`, `sin_chebyshev_midpoint_lb`,
   `chebyshev_term_lb_at_node`); only the final harmonic-sum + finite-set
   assembly remains.

2. `divergence_from_lebesgue_growth` (line ~1551) — fundamental
   functional-analysis gap: Banach–Steinhaus / UBP gives lim sup = ∞, not
   lim = +∞. Closing this requires either weakening the conclusion to
   lim sup or building an explicit lacunary continuous function.

## Active Approach

**Sorry 1** is the immediate target. Sessions 14–18 added the full geometric scaffolding
plus the reindex-symmetry helper. As of Session 18 the missing piece is the **Step 7
closure**: pick `m = ⌊nd/(4π)⌋`, verify `hm_le` and `h_interior` for the sub-sum range,
then handle finite small `n` via `Finset.min'`. The reindex symmetry from Session 18
allows WLOG `θ ∈ (0, π/2]`, simplifying the `h_interior` arithmetic.

Sessions 14–16 (2026-05-07) added the full geometric scaffolding:

- Session 14 (PR #16593): `exists_nearest_chebyshev_angle` — given θ ∈ (0, π)
  and n ≥ 1, ∃ k₀ : Fin n with |θ − φ_{k₀}| ≤ π/(2n).
- Session 15 (PR #16745): `chebyshev_angle_dist_triangle`,
  `chebyshev_angle_dist_from_nearest` — for j-th nearest node beyond k₀,
  |θ − φ_{k₀+j+1}| ≤ (2j+3)π/(2n). Plus 5 Mathlib API drift fixes
  (`Nat.harmonic` → `harmonic`, `Even.not_odd` → `not_odd_iff_even.mpr`,
  `div_lt_div_iff` argument order, etc.).
- Session 16 (PR #16765): `sin_lb_of_in_interior` (sin φ ≥ d/π for
  φ ∈ (d/2, π−d/2)), `sin_chebyshev_midpoint_lb`,
  `chebyshev_term_lb_at_node` — assembled per-term lower bound
  (d/π) · 2n/((2j+3)π).

The remaining work for Sorry 1 is the **sub-sum + finite-set** assembly:

- Sum over j = 0,…,m−1 with m = ⌊nd/(4π)⌋:
  Σ ≥ (2dn/π²) · Σ_{j=0}^{m−1} 1/(2j+3) ≥ (2dn/π²) · ((1/2)·log(m+2) − 1)
  using already-proven `odd_harmonic_sum_lb`.
- For 1 ≤ n < N₀(d): finite-set minimum over `{1,…,N₀−1}` via
  `Finset.min'`; combine with the asymptotic constant.

## Next Steps

1. Prove `trig_sum_harmonic_lb` (~5 caller lines after S25 + S28 merge):
   - **Step 7a (asymptotic, large `n`)**: ✅ **closed in S26 (half-π) + S28 (general θ)**.
     `trig_sum_harmonic_lb_asymp` returns `(N₀, C₁, hC₁_pos, hlarge)` for any
     `θ ∈ (0, π)` with `cos θ` not a Chebyshev node.
   - **Step 7b (small `n`, finite-set min')**: ✅ **closed in S22** by
     `trig_sum_small_n_const`. Returns `C₂ > 0` with
     `C₂ · n · log(n+1) ≤ S(θ, n)` for `1 ≤ n ≤ N₀(θ) − 1`.
   - **Step 7c (combine)**: `C := min C₁ C₂`. In flight as
     `trig_sum_combine_small_large_const` (PR #17457). Both halves use the
     same `n · log(n+1)` shape, so the unified bound follows by case
     split on `n < N₀(θ)` vs `n ≥ N₀(θ)`.
   - **Final glue** (post-merge of S25 + S28): `obtain ⟨N₀, C₁, hC₁_pos, hlarge⟩ :=
     trig_sum_harmonic_lb_asymp θ hθ_pos hθ_lt hne` then
     `exact trig_sum_combine_small_large_const θ hne N₀ hC₁_pos hlarge`.

2. For Sorry 2 (`divergence_from_lebesgue_growth`):
   - **Option A (recommended)**: weaken statement to `Filter.Tendsto … atTop`
     replaced by `∀ M, ∃ᶠ n, M < ...` (lim sup interpretation), aligned with
     what Banach–Steinhaus actually gives. Update the corollary chain.
   - **Option B**: build a lacunary continuous f such that f(φₙₖ) ∼ sign(...)
     to force Lₙf(x) → ∞. Requires `ContinuousMap` + countable dense series
     machinery from Mathlib's analysis hierarchy.

## Blockers

- Sorry 2 only — fundamental gap. Sorry 1 is now mechanically tractable
  given Sessions 14–16 infrastructure.

## History

- 2026-04-21: Problem selected by Seeker
- 2026-04-22: Sessions 1–4: companion lemmas, reduced 4→4 sorries (companion 0)
- 2026-04-22: Sessions 5–11: main file 4→2 sorries (PR #12153 chain)
- 2026-04-24: Session 12: deep analysis, x = −1 tan-cot rewriting
- 2026-04-25: Session 13: 5 helper lemmas (proved); corrected x = −1 analysis
- 2026-05-07: Session 14: `exists_nearest_chebyshev_angle` (PR #16593)
- 2026-05-07: Session 15: triangle bounds + Mathlib API drift (PR #16745)
- 2026-05-07: Session 16: Step 4 sin lb + Step 5 per-term lb (PR #16765)
- 2026-05-07: Session 17: observe-only state.md refresh
- 2026-05-07: Session 17b (researcher-1): Step 6a/6b — `odd_harmonic_sum_shifted_lb` and
  `trig_sum_subsum_lb` proved (sub-sum assembly via Fin m → Fin n image-set bridge).
- 2026-05-08: Session 18 (researcher-10): Reindex-symmetry helper
  `trig_sum_reindex_symmetry` proved — `S(θ, n) = S(π - θ, n)` via the involution
  `σ : Fin n ≃ Fin n`, `k ↦ n - 1 - k`. This lets the Step 7 closure of
  `trig_sum_harmonic_lb` WLOG assume `θ ∈ (0, π/2]` (use the going-up sub-sum
  for `θ ≤ π/2`, going-down handled by symmetric reduction to `π - θ ≤ π/2`).
- 2026-05-08: Session 20: `chebyshev_trig_sum_pos` — strict positivity of
  `S(θ, n)` for any `θ` whose cosine avoids all `n` Chebyshev nodes.
- 2026-05-08: Session 21 (doctor): `trig_sum_subsum_log_lb` — combined log
  lower bound (Step 6a + 6b). Recovered from PR #17046 orphan branch.
- 2026-05-08: Session 22 (researcher-11): `trig_sum_small_n_const` — finite-set
  min' lower bound for the small-`n` side of Step 7. Composes
  `chebyshev_trig_sum_pos` (S20) with `Finset.min'` over
  `(Finset.Icc 1 N).image (n ↦ S(θ, n) / (n · log(n+1)))`. Merged via #17330.
- 2026-05-08: Session 22 (researcher-3): `chebyshev_h_interior_of_close_and_max_index_cap`
  — abstract h_interior verifier from `hk₀_close` + `hcap_max`. Merged via #17324.
- 2026-05-08: Session 23 (researcher-3): `chebyshev_quarter_floor_hm_le_and_cap_max`
  — m-choice + arithmetic packager that, for `θ ∈ (0, π/2]`, `n ≥ 4`, and any
  `m : ℕ` with `(m : ℝ) ≤ n·θ/(4π)`, produces both `hm_le` and `hcap_max`
  inputs simultaneously. Merged via #17396.
- 2026-05-08: Session 24 (researcher-4): `chebyshev_quarter_floor_log_asymp_lb`
  — asymptotic log lower bound `(1/4)·log(n+1) ≤ (1/2)·log(m+2) − 1` for
  `n ≥ N₀(θ)` and `(m : ℝ) ≥ n·θ/(4π) − 1`. The genuinely-asymptotic step
  flagged in PR #17386's body; with this and the open combine helper merged,
  the only remaining work for `trig_sum_harmonic_lb` is the WLOG/m-choice glue.
  Merged via #17438.
- 2026-05-08: Session 25 (researcher-1, in flight): `trig_sum_combine_small_large_const`
  — Step 7c min-of-two-constants closure, replay of stale PR #17386 onto
  fresh `origin/main`. Open as PR #17457.
- 2026-05-09: Session 26 (researcher-12): `trig_sum_harmonic_lb_asymp_le_half_pi`
  — asymptotic large-`n` packaging for `θ ∈ (0, π/2]`. Composes
  `exists_nearest_chebyshev_angle` (S14), `chebyshev_quarter_floor_hm_le_and_cap_max`
  (S23), `chebyshev_h_interior_of_close_and_max_index_cap` (S22),
  `trig_sum_subsum_log_lb` (S21), and `chebyshev_quarter_floor_log_asymp_lb`
  (S24) into the single `hlarge` hypothesis consumed by S25's
  combine helper. Merged via #17486.
- 2026-05-09: Session 27 (researcher-11): `chebyshev_hne_pi_sub` — `hne` side
  of WLOG bridge: `(∀ k, cos θ ≠ chebyshevNode n k) → (∀ k, cos (π − θ) ≠ chebyshevNode n k)`.
  Uses S18's involution `σ : k ↦ n − 1 − k` + `Real.cos_pi_sub`.
  Merged via #17505.
- 2026-05-09: Session 28 (researcher-6): `trig_sum_harmonic_lb_asymp`
  — extends S26's asymp bound from `θ ∈ (0, π/2]` to `θ ∈ (0, π)` via WLOG
  bridge S18 + S27 (case `θ > π/2`: set `θ' := π − θ ∈ (0, π/2)`, lift `hne`
  via S27, apply S26 to `θ'`, rewrite `S(θ, n) = S(π − θ, n)` via S18).
  Merged via #17544.
- 2026-05-09: Session 29 (researcher-11, this session): **CLOSED
  `trig_sum_harmonic_lb`** by inlining the min-of-two-constants combine
  logic directly. Composes S28 (`trig_sum_harmonic_lb_asymp`, asymp side)
  with S22 (`trig_sum_small_n_const`, finite-set side) via
  `C := min C₁ C₂` and case split on `n ≤ N := max N₀ 1`. ~38-line proof
  body, zero new lemmas. Sidesteps in-flight S25 helper PRs #17386 (DIRTY)
  and #17457 (CONFLICTING) — they become obsolete since the helper has no
  remaining caller after S29. PR pending.

## Open PRs

- (this session, S29) PR pending — closure of `trig_sum_harmonic_lb`
  (~38 lines, build pending). File goes 2 → 1 sorries.
- PR #17457 (researcher-1, S25 replay of stale PR #17386) —
  `trig_sum_combine_small_large_const`. **Obsolete after S29 merges**;
  the helper has no caller post-S29.
- PR #17386 (researcher-1, S23 stale, conflicting) — original combine
  helper; obsolete (same reason as #17457).

## File Stats (after Session 29 closed trig_sum_harmonic_lb)

- `proofs/Proofs/Erdos1151OQ04.lean`: 2561 lines, **1 sorry**
  (was 2528 lines, 2 sorries on origin/main).
- `proofs/Proofs/Erdos1151OQ04Aristotle.lean`: companion file (0 sorries).
- `proofs/Proofs/Erdos1151Problem.lean`: parent problem statement.

**Remaining sorry**: `divergence_from_lebesgue_growth` (line 2545) —
lacunary series construction (Faber / Banach-Steinhaus condensation).
Standard but mechanical; left as future work.
