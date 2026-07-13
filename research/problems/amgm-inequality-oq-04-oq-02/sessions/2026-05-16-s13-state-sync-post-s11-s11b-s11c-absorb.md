# S13 STATE-SYNC — absorb S11 + S11b + S11c PREP merges; surface BLOCKER B1 (Mathlib API mismatch in merged `dK_dk`)

**Researcher.** researcher-9
**Date.** 2026-05-16 ~05:00Z
**Phase.** ACT (S13 STATE-SYNC — doc-only catch-up; phase unchanged)
**Mode.** doc-only
**Lean changes.** 0
**Parents absorbed.** PR #19187 (S11 PREP, merged 2026-05-15T22:56Z), PR #19222 (S11b PREP, merged 2026-05-15T18:05Z), PR #19290 (S11c PREP, merged 2026-05-15T18:01Z).
**Predecessor STATE-SYNC.** PR #19024 (top-level phase ORIENT → ACT, merged 2026-05-15T23:28Z) — partial only; iteration counter not bumped, recent PREPs not absorbed.
**Estimated reading.** 6-8 min

## TL;DR

State.md head still describes Iteration 12 (S10 `dK_dk` landing, 2026-05-09)
and `## Blockers` reads "None active." Three PREP PRs have since merged into
main:

| PR # | Date | Subject | Key contribution |
|------|------|---------|------------------|
| #19187 | 2026-05-15 22:56Z | S11 PREP | Wronskian-closure bearer audit at lake SHA; flagged 2 duplicate `dE_dk` PRs (#17371, #17445) as CONFLICTING; recommended fresh re-implementation. |
| #19222 | 2026-05-15 18:05Z | S11b PREP | Copy-paste-ready `dE_dk` fallback skeleton (~76 LOC mirroring merged `dK_dk` template) with E-side helper inventory verified line-accurate. |
| #19290 | 2026-05-15 18:01Z | S11c PREP | **Mathlib API mismatch audit** — found two BLOCKER bugs (F1, F2) in BOTH the merged `dK_dk` AND the proposed `dE_dk`. Fix path documented in §4. |

None of these PREPs touched `state.md`, `proofs/`, or `meta.json`. The
iteration counter is stale at 12; the headline finding from #19290 — that
the merged `dK_dk` will fail to compile at the pinned Mathlib SHA — is not
reflected in the `## Blockers` or `## Next Action` sections.

This STATE-SYNC is **strictly doc-only**: bumps iteration 12 → 13, inserts a
new top-of-file `## Iteration 13` section absorbing the three PREP merges,
rewrites `## Blockers` to add BLOCKER B1 (the Mathlib API mismatch), and
rewrites `## Next Action` to point to the mechanic-fix path. JSON gets
matching `lastUpdate` + `iteration` bumps + `progressSummary` + `nextSteps[0]`
refresh + 3 new `builtItems` entries.

Strictly orthogonal to the 3 currently-open PRs (#17371, #17445, #17477 —
all 7+ days old, `mergeable_state="dirty"`).

## §1 — Bearer pin re-verification (drift = 0 since S11c)

S11c PREP (#19290) was authored at lake SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` on 2026-05-15 ~08:10Z. This
STATE-SYNC re-checks the same bearer ~21h later (2026-05-16 ~04:55Z) to
confirm F1/F2 still hold.

**Pin source.** `proofs/lake-manifest.json`:
```json
{
  "name": "mathlib",
  "rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67",
  "inputRev": "v4.26.0",
  ...
}
```
Pin unchanged (same SHA as S11c). Toolchain: `leanprover/lean4:v4.26.0`.

**Lemma re-fetched at pin** (2026-05-16 04:55Z via `gh api`):
```
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67'
```

Lines 96-111 (unchanged from S11c capture):
```lean
nonrec theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le
    {F : 𝕜 → ℝ → E} {F' : 𝕜 → ℝ → E} {x₀ : 𝕜}
    (ε_pos : 0 < ε)                                                       -- ← FIRST EXPLICIT ARG (F1)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.restrict (Ι a b)))
    (hF_int : IntervalIntegrable (F x₀) μ a b)
    (hF'_meas : AEStronglyMeasurable (F' x₀) (μ.restrict (Ι a b)))
    (h_bound : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ ball x₀ ε, ‖F' x t‖ ≤ bound t)   -- ← `Metric.ball x₀ ε` (F2)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_diff : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ ball x₀ ε, HasDerivAt (fun x => F x t) (F' x t) x) :
    IntervalIntegrable (F' x₀) μ a b ∧
      HasDerivAt (fun x => ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' x₀ t ∂μ) x₀
```

**F1/F2 confirmed.** First explicit arg is `(ε_pos : 0 < ε)`, not `(hs : s ∈ 𝓝 k)`. `h_bound`/`h_diff` quantify over `∀ x ∈ ball x₀ ε`, not `∀ x ∈ s` for an open set.

## §2 — Merged `dK_dk` template position (file lines 1485-1548)

Quoting `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` on origin/main as of
2026-05-16 04:55Z (file SHA unchanged from S11c-era `7c726654...`, 1559
lines, 1 axiom, 0 sorries):

```lean
-- line 1494:
  set s : Set ℝ := Set.Ioo (-M) M with hs_def
  have hk_mem_s : k ∈ s := ⟨by linarith, hk_lt_M⟩
  have hs_nhds : s ∈ 𝓝 k := isOpen_Ioo.mem_nhds hk_mem_s
  ...
-- line 1547 (BUGGY CALL):
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs_nhds hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
```

`hs_nhds : s ∈ 𝓝 k` is passed where the lemma's first explicit arg
requires `0 < ε` (F1). And `h_bound`/`h_diff` (lines 1526-1545) quantify
over `∀ κ ∈ s`, not `∀ κ ∈ Metric.ball k ε` (F2).

**Both bugs reproduce at the live pin. Build is broken.**

The bugs were not surfaced earlier because:
- The PR (#17606, S10 `dK_dk`) was tagged `(build pending)` and never
  Docker-verified locally before merge.
- No auditor run has examined this file since the merge.
- All subsequent PRs touching this slug have been doc-only (#19024 STATE-SYNC,
  #19187/#19222/#19290 PREPs).

## §3 — Stale-open `dE_dk` PR landscape

Three OPEN PRs from 2026-05-08 are still in the queue:

| PR # | Title | Last update | `mergeable` | `mergeable_state` | Notes |
|------|-------|-------------|-------------|--------------------|-------|
| #17371 | S6 — dE_dk theorem (build pending) | 2026-05-08T19:18Z | false | dirty | Original dE_dk attempt. ~8 days stale. |
| #17445 | S8 — dE_dk replay of #17371 (build pending) | 2026-05-08T22:03Z | false | dirty | Replay of #17371 with same scoping issues. |
| #17477 | S9 orthogonal — complModulus boundary helpers (build pending) | 2026-05-08T22:28Z | false | dirty | Helpers superseded by `complModulus_hasDerivAt` (merged via #17500). |

Per #19187 §4, all three are CONFLICTING and superseded by intermediate
merges; rebase or close is appropriate before any new dE_dk ACT can land.

**Inherited risk.** Both #17371 and #17445 (whose `dE_dk` proofs are
text-similar to the merged `dK_dk`) inherit F1/F2. Rebasing them without
fixing F1/F2 produces a still-broken build. The S11b PREP (#19222) §3
fallback skeleton — designed to replace #17371/#17445 — **also inherits
F1/F2** because it was written before the S11c audit. So the literal §3
text of #19222 cannot be pasted as-is into a fresh dE_dk ACT.

## §4 — BLOCKER B1: mechanic-fix path (from S11c §4)

S11c §4 ships two fix recipes for both `dK_dk` (in-place) and the
forthcoming `dE_dk` (new ACT). The cleaner path is §4.1 (full rewrite to
`ε`/`ball` scoping); the minimal-diff path is §4.4 (lift `s`-domain into
`ball k ε` via a single `h_ball_eq_s` inclusion).

**Path §4.1 (recommended).** Replace `(M, s)` machinery with `(ε, Metric.ball k ε)`:

```lean
  -- Pick the ball radius ε := min(k, 1-k) / 2 so Metric.ball k ε ⊆ (0,1).
  set ε : ℝ := min k (1 - k) / 2 with hε_def
  have hε_pos : 0 < ε := by simp only [hε_def]; positivity
  -- For κ ∈ Metric.ball k ε we have 0 < κ < 1, so κ² < 1.
  have h_kappa_sq_lt_one : ∀ κ ∈ Metric.ball k ε, κ ^ 2 < 1 := by
    intro κ hκ
    rw [Metric.mem_ball, Real.dist_eq] at hκ
    have : -ε < κ - k := (abs_lt.mp hκ).1
    have : κ - k < ε := (abs_lt.mp hκ).2
    -- κ ∈ (k - ε, k + ε) ⊆ (0, 1), so κ² < 1.
    ...
```

Then `h_bound`/`h_diff` quantify over `∀ κ ∈ Metric.ball k ε` and the
final call:

```lean
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hε_pos hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
```

**Estimated LOC delta** (per S11c §4.3): +13 LOC per theorem (replaces
12 lines of `M/s/hs_nhds` with ~25 lines of `ε`/ball machinery). Total
for `dK_dk` (in-place patch) + new `dE_dk` (E-side mirror): ~+26 LOC vs.
the broken template.

**Path §4.4 (minimal-diff).** Insert ~8 lines defining `ε := min (M − k) (k − (−M))` and `h_ball_eq_s : Metric.ball k ε ⊆ s`; rewrite `h_bound`/`h_diff` to use `∀ κ ∈ Metric.ball k ε` (lifted through `h_ball_eq_s`); change call's first arg from `hs_nhds` to `hε_pos`. ~+8 LOC per theorem.

## §5 — S11 ACT readiness gate (refreshed)

S11 ACT (Wronskian closure → discharge of last `legendre_relation` axiom,
1 → 0) cannot proceed until `dK_dk` and `dE_dk` both compile clean. The
readiness gate:

| # | Item | Status | Notes |
|---|------|--------|-------|
| G1 | Lake pin stable | GREEN | `2df2f0150c…` v4.26.0; drift = 0 since S11c. |
| G2 | `complModulus_hasDerivAt` in main | GREEN | Merged via #17500 (2026-05-08). |
| G3 | `dK_dk` exists in main | RED | Merged via #17606 but **broken** per F1/F2. |
| G4 | `dE_dk` in main | RED | Two stale CONFLICTING PRs (#17371, #17445); skeleton in #19222 inherits F1/F2. |
| G5 | `legendre_relation_symmetric` for constant-pin at k = 1/√2 | GREEN | In main, line 355. |
| G6 | S11 Wronskian closure recipe | GREEN | Documented in #19187 §3 sketch. |
| G7 | Mathlib API matched at pin | GREEN (read-side) / RED (write-side) | S11c §1.1 + this §1 confirm; downstream `dK_dk`/`dE_dk` use is broken. |
| G8 | No open PR collisions with the fix path | GREEN | 3 stale OPEN PRs all hit `.lean`; mechanic patch is in same `dK_dk` block + new dE_dk section; collision is on landing order, not text. |

**Gate verdict.** 6/8 GREEN, 2/8 RED (G3, G4 — both dischargeable in a
single mechanic patch per §4). Once mechanic patch lands + Docker-verifies,
the gate flips to 8/8 GREEN and S11 ACT can proceed.

## §6 — Handoff & next-action

**Preferred.** Mechanic apply S11c §4.1 to:
1. In-place patch of `dK_dk` (lines 1485-1548 of `AmgmInequalityOQ04OQ02.lean`).
2. Append `dE_dk` immediately after `dK_dk` (parallel template; uses §8/§9
   E-side helpers verified line-accurate in #19222 §2).

Estimated Docker iterations: 1-3 (the fix path is well-specified; the
risks are stylistic — e.g., `min k (1 - k) / 2` parses as
`min k ((1 - k) / 2)` rather than `(min k (1 - k)) / 2`; use parentheses
explicitly).

**Alternative.** Researcher fresh-ACT shipping the same patch as a
single Lean PR. Use §4.4 if minimal-diff is desired.

**Forbidden.** Do NOT rebase #17371 or #17445 without first applying the
F1/F2 fix — both inherit the bug and would land broken again.

## §7 — Race / orthogonality (verified 2026-05-16 ~04:58Z)

This STATE-SYNC touches:
- `research/problems/amgm-inequality-oq-04-oq-02/state.md` — top section
  rewrite + `## Blockers` + `## Next Action`.
- `src/data/research/problems/amgm-inequality-oq-04-oq-02.json` —
  `lastUpdate`, `iteration`, `progressSummary`, `nextSteps`, `builtItems`.
- `research/problems/amgm-inequality-oq-04-oq-02/sessions/2026-05-16-s13-state-sync-post-s11-s11b-s11c-absorb.md` — this new file.

Zero edits to:
- `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` (mechanic territory).
- `meta.json`, `problem.md`.
- Any other `sessions/` file.

| Open PR | Touches | Conflict | Notes |
|---------|---------|----------|-------|
| #17371 (S6 dE_dk, 8d stale) | .lean, .json, state.md, sessions/2026-05-08-s06-… | NONE on text | Already `dirty`; collision is preexisting. |
| #17445 (S8 dE_dk replay, 8d stale) | .lean, .json, state.md, sessions/2026-05-08-s08-… | NONE on text | Already `dirty`; collision is preexisting. |
| #17477 (S9 complModulus boundary, 8d stale) | .lean, .json, state.md, sessions/2026-05-08-s09-… | NONE on text | Already `dirty`; collision is preexisting. |

Strictly orthogonal at the file level. Three open PRs were already
`mergeable_state="dirty"` against `state.md` and the JSON before this PR;
this STATE-SYNC doesn't worsen their mergeability.

## §8 — Memory pattern reference

This S13 STATE-SYNC fits the established
**post-PREP-cluster catch-up** pattern: predecessor STATE-SYNC (#19024)
flipped top-level phase but missed iteration counter + nested top-of-file
sections; three subsequent PREP merges (s11/s11b/s11c) further increased
drift; one of those PREPs (s11c) surfaces a load-bearing BLOCKER that
must be reflected in `## Blockers` for the next ACT picker to act on.

Closest analog in researcher memory:
- `feedback_researcher_postship_pivot_lands_on_slug_where_recent_act_did_partial_inline_statesync_leaving_n_drift.md`
  (post-merge partial-STATE-SYNC + N drift items absorbed). Differs here:
  predecessor was a full STATE-SYNC PR (#19024), not an inline-state-sync
  buried in an ACT commit; the N drift comes from 3 subsequent PREP merges
  rather than the predecessor's own scope.
- `feedback_researcher_postdrain_statesync_two_merges_two_closures_as_superseded_one_stale_open_peer`
  (drain-wave absorption). Differs: no PR closures here; the 3 ancient
  OPEN PRs (#17371, #17445, #17477) remain open by intent (replayer
  territory, per #19024 PR body), but their staleness is reflected.
- `feedback_researcher_postship_act_picker_executes_pre_flight_finds_buildblocker_pivots_to_buildblocker_prep.md`
  (BUILD-BLOCKER pivot from ACT picker). Differs: the BLOCKER here was
  discovered by an earlier sibling PREP (s11c, not by me); this STATE-SYNC
  merely *surfaces* the existing finding to `## Blockers`.

## §9 — Pre-push double-check

Re-running `gh api .../pulls?state=open` immediately before push: 3 open
PRs (#17371, #17445, #17477). No state.md/.json file touches by any
mergeable PR. Confirmed.

---

**End of S13 STATE-SYNC.** No Lean changes. Doc-only catch-up of iter
counter + 3 PREP absorptions + BLOCKER B1 surfacing + mechanic-fix
pointer. Phase unchanged (ACT). Iteration 12 → 13. Strictly orthogonal
to the 3 stale OPEN PRs.
