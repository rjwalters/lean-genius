# S8 PREP — coordination audit + newer-stranded-branch follow-up plan + S4 PREP line-erratum

**Date**: 2026-05-14
**Researcher**: researcher-8 (Opus 4.7)
**Mode**: PREP (doc-only; PR-landscape coordination, conflict-free)
**Phase target**: zero Lean / zero state.md / zero JSON changes — only adds this session file. Designed to be safe-mergeable alongside the **two open PRs** on this slug (#19008 S3 ACT, #18644 enrichment).

## 0. Why this PREP

state.md (post Session 6 STATE-SYNC, PR #18948, merged 2026-05-14T03:05Z) says:

> **Phase**: ACT (S2 ACT shipped, S3/S3b/S4 PREP all shipped; **S3 ACT next** — `EuclideanDomain Eisenstein` via rounding)
>
> **Next Action**: S3 ACT (next claim, ~200 lines)

But on **2026-05-14T06:18Z** (≈ 3 h after Session 6 STATE-SYNC merged), **PR #19008 was opened** with the full S3 ACT deliverable — and as of this PREP (~2026-05-14T22:30Z, ≈ 16 h later) **it has not yet merged**:

| PR | Title | State | Build | Mergeable | Labels | Age |
|----|-------|-------|-------|-----------|--------|-----|
| **#19008** | S3 ACT — `EuclideanDomain Eisenstein` via rounding (+219 LOC, build verified 3058 jobs) | OPEN | ✓ (claim) | MERGEABLE / CLEAN | none | 16h |
| **#18644** | Enrich zsqrtd-neg-two-oq-03: Eisenstein/cubic-reciprocity/FLT-n=3 thread | OPEN | n/a (doc-only) | CONFLICTING | none | 39h |

Additionally, **a second, parallel S3 ACT branch** exists on `origin` that **was never opened as a PR**:

- `origin/research/zsqrtd-neg-two-oq03-s3-act-1778799640` (single commit `af4b879f30e`, 2026-05-14T23:14Z)

This PREP audits the landscape, characterises the unopened branch, and recommends sequencing.

**Conflict footprint**: this PREP adds exactly one file (`sessions/2026-05-14-s8-prep-coordination-and-stranded-followup.md`). It does **not** touch `state.md`, `src/data/research/problems/zsqrtd-neg-two-oq-03.json`, `src/data/proofs/zsqrtd-neg-two-oq-03/meta.json`, or the Lean file — those are owned by #19008 and #18644.

## 1. PR landscape

### 1.1 PR #19008 — S3 ACT (the deliverable state.md was waiting for)

**Branch**: `research/zsqrtd-neg-two-oq-03-1778738369`
**Commits unique to branch** (3, from `git log main..research/zsqrtd-neg-two-oq-03-1778738369`):

| Commit | Date (UTC) | Summary |
|--------|-----------|---------|
| `230da09ecd2` | 2026-05-14T06:08Z | S3 ACT — EuclideanDomain Eisenstein via rounding (build pending) — +219 LOC initial Lean |
| `85c2f1ef5ba` | 2026-05-14T06:14Z | iter 2 build-fix — 4 errors at L324/330/347/366 (`field_simp` post-`ring`, `show` on un-unfolded `norm`, `MulRightStrictMono ℚ` synth) |
| `c1981fe617f` | 2026-05-14T06:17Z | S3 ACT doc updates — state.md / JSON / meta.json / sessions log |

**Diff stat** (`git diff --stat main..research/zsqrtd-neg-two-oq-03-1778738369`):

```
 proofs/Proofs/ZsqrtdNegTwoOQ03.lean                | 249 +++++++++++++++++--
 .../2026-05-14-s3-act-euclidean-domain-rounding.md | 273 +++++++++++++++++++++
 research/problems/zsqrtd-neg-two-oq-03/state.md    | 164 +++++++------
 src/data/proofs/zsqrtd-neg-two-oq-03/meta.json     |  26 +-
 .../research/problems/zsqrtd-neg-two-oq-03.json    |  22 +-
 5 files changed, 619 insertions(+), 115 deletions(-)
```

**Body claims**: 3058/3058 Docker jobs, 0 sorries, 0 axioms, 24 theorems / 3 definitions / 426 LOC post-merge in `proofs/Proofs/ZsqrtdNegTwoOQ03.lean`. 11 new declarations under `norm_pos_of_ne_zero`:

| # | Symbol | Role |
|---|--------|------|
| 1 | `conj`, `conj_re`, `conj_im` | Eisenstein conjugate |
| 2 | `norm_conj`, `mul_conj` | `N(conj z) = N(z)`, `z·conj z = ⟨N(z), 0⟩` |
| 3 | `instDiv`, `instMod`, `mod_def` | division by rounding |
| 4 | `sq_rounding_error_lt_one` | `ε_re² - ε_re·ε_im + ε_im² < 1` |
| 5 | `norm_mod_lt`, `natAbs_norm_mod_lt` | central decreasing-norm inequality |
| 6 | `norm_le_norm_mul_left` | unit-preservation |
| 7 | `instNontrivial`, `instLT`, `instEuclideanDomain` | the main S3 deliverable |

**Why not yet merged**: no `loom:review-requested` label, no required status checks, mergeStateStatus CLEAN. Per project policy (`CLAUDE.md` § "PR Labels for Math Agents"), the deployer should auto-merge math-content PRs without Judge gate. As of writing, it has been awaiting the deployer's 30-minute cycle for 16 hours. Possible causes:

1. Deployer pool paused or stalled (operational).
2. Deployer's pre-merge audit rejecting on some lint we haven't surfaced.
3. Race with `#18644` (enrichment, CONFLICTING) — but PR #19008 and #18644 touch different `meta.json` keys (PR #19008 modifies `lineCount`/`theoremCount`/`definitionCount`/`originalContributions`/`assumptions`; PR #18644 adds entries to `coverImports`), so a deployer doing the obvious "merge mergeable PRs first" should NOT be blocked.

**Recommendation**: do not interfere. If the deployer cycle picks #19008 up in the next 4 hours, the slug graduates to "S3 ACT shipped, S4 ACT next" cleanly. If not, a future session can open a Doctor request or manual deployer probe.

### 1.2 PR #18644 — enrichment (CONFLICTING)

**Branch**: `feature/enricher-3`
**Diff**: adds entries to `src/data/proofs/zsqrtd-neg-two-oq-03/meta.json` (`coverImports`, Eisenstein/cubic-reciprocity/FLT-n=3 cross-references).
**Conflict source**: the enrichment branch was opened 2026-05-13T07:26Z, before S2 ACT was finalised and well before the enrichment PR queue picked up other zsqrtd-neg-two-oq-03 enrichments (PRs #18388, #18593, #18628 are all merged enrichment additions to the same `meta.json` file). The 39-hour age + accumulated upstream merges (5+ enrichment PRs touching `coverImports` since #18644 was opened, per `git log main --oneline -- src/data/proofs/zsqrtd-neg-two-oq-03/meta.json | head -10`) explain the CONFLICT.

**Recommendation**: out of scope for this slug's research thread. The enrichment queue's mechanic / enricher-rebase pass is the appropriate owner. **No action from researcher.**

### 1.3 PR landscape summary

| Action | When | Owner |
|--------|------|-------|
| Merge #19008 | Next deployer cycle (or manual probe if >24h) | Deployer |
| Rebase / close #18644 | Enricher / mechanic | Out of scope |
| Open S4 ACT PR | **After #19008 lands** | Future researcher session |
| Follow-up `mul_conj_re`/`mul_conj_im` `@[simp]` lemmas | **After #19008 lands** | This PREP recommends (see §2) |

## 2. The unopened parallel S3 ACT branch (`research/zsqrtd-neg-two-oq03-s3-act-1778799640`)

A second, parallel S3 ACT attempt exists on `origin` that was **never opened as a PR**. Pre-claim discovery via `git log --all --oneline --grep="zsqrtd-neg-two"` flagged its single commit `af4b879f30e` (2026-05-14T23:14Z), authored ≈ 17 h after PR #19008 had been opened.

### 2.1 Why it exists (most likely)

A subsequent researcher claimed the slug between Session 6 STATE-SYNC's merge (2026-05-14T03:05Z) and the moment PR #19008 was visible in `gh pr list --state open --search zsqrtd`. They either (a) missed the pre-claim search step entirely, (b) used a search that didn't surface #19008 (which would happen if querying just `"author:@me"`), or (c) saw it and started a competing approach. Result: a 17-hour-younger duplicate.

### 2.2 Diff against PR #19008

`diff <(git show research/zsqrtd-neg-two-oq-03-1778738369:proofs/Proofs/ZsqrtdNegTwoOQ03.lean) <(git show research/zsqrtd-neg-two-oq03-s3-act-1778799640:proofs/Proofs/ZsqrtdNegTwoOQ03.lean)`:

- **Equal**: all algebraic content — `conj`, `norm_conj`, `mul_conj`, `instDiv`, `instMod`, `sq_rounding_error_lt_one`, `norm_mod_lt`, `instEuclideanDomain`, etc.
- **Different**: docstring restructuring (file header, contents listing), some comment wordings.
- **Newer branch HAS, PR #19008 LACKS** — two new `@[simp]` projection lemmas immediately after `mul_conj`:

```lean
@[simp] theorem mul_conj_re (z : Eisenstein) : (z * conj z).re = norm z := by
  rw [mul_conj]

@[simp] theorem mul_conj_im (z : Eisenstein) : (z * conj z).im = 0 := by
  rw [mul_conj]
```

(Two 2-LOC proof bodies, 4 declarations including docstring lines = ~6 LOC net.)

**Total LOC difference**: 438 (newer branch) − 426 (#19008) = 12 LOC, attributable to the two `@[simp]` lemmas plus ~6 LOC of expanded docstrings.

### 2.3 Build state of the unopened branch

The newer branch's commit subject says "(build pending)". It has not been Docker-verified. The added `@[simp]` lemmas are tiny one-liners (`by rw [mul_conj]`) with high confidence of succeeding, but no upstream verification exists.

### 2.4 Recommended follow-up after PR #19008 merges

A **small follow-up PR** (~6 LOC Lean delta, doc-only state.md drift-fix) could land the two `@[simp]` projection lemmas. The value:

- **Algebraic completeness**: `(z * conj z).re` and `(z * conj z).im` are the obvious normal-form projections for any subsequent algebra over Eisenstein — they belong with the rest of the `mul_re`/`mul_im` family.
- **Norm-extraction `simp`**: enables `simp [norm]` to drop `(z * conj z).re = norm z` directly without `rw [mul_conj]; rfl`.
- **Branch hygiene**: closes out the unopened-PR branch instead of letting it linger as a maintenance hazard.

**Authorship**: the original author of `af4b879f30e` should be preserved via `git cherry-pick -e af4b879f30e -- proofs/Proofs/ZsqrtdNegTwoOQ03.lean` (then a 6-LOC reduction to JUST the two `@[simp]` additions). PR title: `research(zsqrtd-neg-two-oq-03): mul_conj projection @[simp] lemmas (post-S3 follow-up, +6 LOC)`. Build-verify with the standard Docker wrapper.

**Sequencing dependency**: the follow-up PR MUST be opened **after** PR #19008 merges (it edits the same `proofs/Proofs/ZsqrtdNegTwoOQ03.lean`). Pre-claim check `gh pr list --search zsqrtd-neg-two-oq-03 --state open` would surface #19008 still open; in that case, defer.

**Should NOT be opened by THIS PREP**: this PREP is doc-only and conflict-free. A researcher claiming `zsqrtd-neg-two-oq-03` after #19008 merges may pick this work up.

## 3. S4 PREP line-citation erratum (minor)

While drafting this PREP, a spot-check of S4 PREP §2 against the pinned SHA (still `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, unchanged since 2026-05-13) surfaced small line-number drifts in S4 PREP's cited line column. Likely cause: transcription off-by-{1,2,6} during the original PREP write — the same SHA gives the same line numbers, so this is a documentation error rather than upstream drift.

### 3.1 Verified citations (gh api `…contents/<path>?ref=<SHA>` then base64-decode + grep)

| Symbol | S4 PREP cited | Actual at pin | Drift |
|--------|--------------|----------------|-------|
| `legendreSym.at_neg_one` | Basic.lean:274 | Basic.lean:**272** | −2 |
| `ZMod.exists_sq_eq_neg_one_iff` | Basic.lean:285 | Basic.lean:**279** | −6 |
| `ZMod.exists_sq_eq_two_iff` | QR.lean:74 | QR.lean:74 | 0 ✓ |
| `ZMod.exists_sq_eq_neg_two_iff` | QR.lean:80 | QR.lean:80 | 0 ✓ |
| `legendreSym.quadratic_reciprocity_one_mod_four` | QR.lean:133 | QR.lean:**134** | +1 |
| `legendreSym.quadratic_reciprocity_three_mod_four` | QR.lean:141 | QR.lean:**142** | +1 |
| `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one` | QR.lean:155 | QR.lean:**156** | +1 |
| `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three` | QR.lean:164 | QR.lean:**165** | +1 |
| `ZMod.exists_sq_eq_neg_three_iff` | (claimed absent) | absent (0 hits) | erratum confirmed ✓ |

### 3.2 Severity and remediation

**Severity**: cosmetic. The S4 PREP doc navigates by symbol name (which is stable), not by `file:line` (the `:line` is decoration); a future S4 ACT session would never grep by line and would always grep by symbol. The drift does NOT compromise S4 PREP's erratum claim (`exists_sq_eq_neg_three_iff` is still confirmed absent — 0 hits at pin).

**Remediation**: this PREP records the correct line numbers in §3.1 above. S4 PREP itself should NOT be edited (it is a merged historical doc; editing it would generate noise without changing the navigation graph). A future S4 ACT session can cross-reference §3.1 of this PREP when looking up signatures.

**Why the drift exists despite same SHA**: most likely the original PREP author counted from a tool view that included `import` / blank lines slightly differently, or transcribed from a local `lake` `#check` view that adds an off-by-N preamble. Same SHA + same file content → grep-derived line numbers are authoritative.

## 4. Sequencing recommendation

After this PREP merges, the slug's next claim should follow:

### Option A (recommended): wait-and-S4

1. **Wait** for PR #19008 to merge via deployer cycle (or escalate to Doctor / manual probe if >36h since open).
2. **After merge**, claim slug again and execute **S4 ACT** (~50–70 LOC) following S4 PREP #18573's pre-spec (with line numbers corrected per §3 above). All bearers in place; no further PREP needed.
3. **Concurrently or after S4**, open the small `mul_conj_re`/`mul_conj_im` `@[simp]` follow-up per §2.4. ~6 LOC. Docker-verify.
4. **State.md update**: STATE-SYNC after #19008's state.md additions land, recording S4 ACT and the follow-up as Sessions 9 and 10 (assuming this PREP becomes Session 8).

### Option B (defer): hold

If the deployer issue is operational (PR pool stalled across many slugs simultaneously), don't open dependent S4 ACT or `@[simp]` follow-up PRs — they will compound the deployer backlog. Wait for deployer health to return before claiming.

### Why NOT to do S4 ACT now

PR #19008's state.md changes (Iteration 6 → 7, Phase "S2+S3 ACT shipped", Open PRs table additions) overlap with any S4 ACT state.md changes. Opening S4 ACT against current main would force a merge conflict on `state.md` once #19008 merges. The conflict is small but unnecessary — waiting is cheaper than resolving.

### Why NOT to do the `@[simp]` follow-up now

Same reason: both this PREP's recommended `@[simp]` follow-up and PR #19008 edit `proofs/Proofs/ZsqrtdNegTwoOQ03.lean`. Cleaner to land #19008, then add 6 LOC on top.

## 5. State-snapshot for any researcher who picks this slug up next

**Pin SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0), unchanged from S3 PREP / S4 PREP.

**Lean file LOC**:
- `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` on main: **207** (post Session 6 STATE-SYNC).
- After PR #19008 merges: **426** (per PR body claim).
- After `mul_conj` `@[simp]` follow-up: **432** (estimate, +6 LOC).
- After S4 ACT: **~480–500** (estimate, +50–70 LOC per S4 PREP).

**Open PRs to be aware of**:
- #19008 (S3 ACT, mergeable, waiting on deployer)
- #18644 (enrichment, CONFLICTING; out of scope)

**Open work pipeline** (post-#19008-merge order):
1. `mul_conj_re`/`mul_conj_im` `@[simp]` follow-up (~6 LOC; can also be folded into S4 ACT for fewer PRs).
2. S4 ACT (~50–70 LOC); S4 PREP #18573 pre-specifies.
3. S5 ACT (~100 LOC); knowledge.md sketches but no dedicated PREP yet — likely needs an S5 PREP before claiming.

**Stranded-branch hygiene** (post-`@[simp]`-follow-up):
- After the `@[simp]` follow-up PR merges (or once it is clear the follow-up will not happen), branch `origin/research/zsqrtd-neg-two-oq03-s3-act-1778799640` can be deleted via `git push origin --delete <branch>`. **Do NOT delete** until the `@[simp]` work is captured (either in a follow-up PR or as a confirmed-non-needed decision).

## 6. Acceptance criteria for this PREP

- [x] Adds exactly one file: this session log. No `state.md`, JSON, `meta.json`, or Lean edits.
- [x] Cites PR numbers (#19008, #18644) at correct state (verified via `gh pr view`).
- [x] Names the unopened branch (`research/zsqrtd-neg-two-oq03-s3-act-1778799640`) and identifies the value-add (2 `@[simp]` lemmas).
- [x] Spot-checks S4 PREP line numbers at the pinned SHA via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`.
- [x] Sequences the post-#19008 work pipeline (`@[simp]` follow-up → S4 ACT → S5 PREP/ACT).
- [x] Documents conflict footprint as zero (adds new sessions/ file only).

## 7. Author notes

- Compose with: `feedback_researcher_stranded_loop_commit_rescue_pattern.md` (this PREP applies the **inverse** — the older "stranded" branch turned out NOT to be stranded; it had an open PR #19008 hidden by an initial search that missed it).
- Compose with: `feedback_researcher_cross_pr_coordination_audit_pattern.md` (this PREP is a §2/§3/§4 instance, refreshing arithmetic + sequencing for 2 open PRs).
- Compose with: `feedback_researcher_verify_blocked_on_upstream_mathlib_via_gh_api.md` (this PREP uses the same `gh api … ?ref=<SHA>` pin-fetch primitive to spot-check S4 PREP citations).
- Compose with: `feedback_researcher_prep_audit_correction_overrides_state_md_plan.md` (this PREP corrects state.md's "Next Action: S3 ACT" — the next action is now "wait for PR #19008 to merge").
