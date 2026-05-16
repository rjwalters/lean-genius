# S16 STATE-SYNC — post-S15-ACT merge absorption + bearer drift recheck + S17 ACT-readiness

**Researcher**: researcher-5
**Date**: 2026-05-16 ~01:30 UTC
**Type**: doc-only STATE-SYNC (zero Lean / meta.json edits; only state.md head + research JSON + this session file)

---

## §0. Trigger and conflict-free guarantees

Claimed `shannon-channel-coding-oq-02-oq-01-oq-01` 2026-05-16 ~01:30 UTC
(RICH score 35, 1 open PR: #19430 fix(meta) by rjwalters/mechanic touching
only `src/data/proofs/shannon-channel-coding-oq-02-oq-01/meta.json`'s
`leanFile.sorries` field — conflict-free with this STATE-SYNC).

Triggering state:

| Artifact | Pre-S16 value (state.md / JSON) | Reality (origin/main `78448f56d0a`) | Drift |
|---|---|---|---|
| state.md `Phase` | `ACT-READY` | (post-S15-ACT-merge, would-be ACT-READY for S16) | stale label |
| state.md `Iteration` | `14` | (S14 STATE-SYNC merged + S15 ACT merged) | stale by 1-2 |
| state.md "Paste-ready S15 ACT (Option A′)" | calls for shipping S12-light + S13 strict-form companion ~12-15 LOC | **ALREADY SHIPPED** as PR #19393 (researcher-1, merged 2026-05-15T20:52:21 -0700) | reality has overtaken the recipe |
| JSON `currentState.phase` | `ACT-READY` | (same drift) | stale |
| JSON `currentState.iteration` | `14` | should be `16` post-STATE-SYNC bump | stale |
| JSON `lastUpdate` | `(S14 timestamp)` | should be `2026-05-16` | stale |
| `proofs/Proofs/ShannonEntropy.lean` (parent) | called for `entropy_eq_log_card_iff_eq_uniform` + `entropy_lt_log_card_iff_ne_uniform` to be added | **BOTH ON DISK** at lines 460-466 + 472-477 verbatim per S14 STATE-SYNC §"Paste-ready" recipe | fully realized |
| Build status of S15 | should be "Docker-verified 7743 jobs" per PR #19393 commit message | confirmed: build green | unchanged |

This is a textbook firing of `feedback_researcher_sibling_act_shipped_between_statesync_and_claim_pivot_to_next_named_work_item.md`:

The S14 STATE-SYNC (#19358, researcher-1, started ~2026-05-15T18:10Z, merged ~2026-05-16T01:10Z) named "S15 ACT (Option A′)" as the next action with paste-ready Lean. The S15 ACT (#19393, researcher-1, also, merged 2026-05-15T20:52:21 -0700 = **~2026-05-16T03:52:21Z**, well after the S14 STATE-SYNC's named work item) shipped that exact recipe before this researcher claimed.

**Pivot per the memory pattern**: ship an S16 STATE-SYNC absorbing the S15 ACT merge + re-syncing state.md / JSON + naming S17 ACT priorities from the still-valid (S12-vintage) "Next Action" candidates carried in state.md tail.

---

## §1. What S15 ACT (#19393) shipped

Per the PR's commit message and on-disk verification:

```lean
-- proofs/Proofs/ShannonEntropy.lean:460-466 (S12-light → S15-1)
theorem entropy_eq_log_card_iff_eq_uniform {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] {p : α → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    shannonEntropy p = Real.log (Fintype.card α) ↔
    p = (fun _ : α => (Fintype.card α : ℝ)⁻¹) :=
  (entropy_eq_log_card_iff_uniform hp hsum).trans
    ⟨funext, fun h x => congrFun h x⟩

-- proofs/Proofs/ShannonEntropy.lean:472-477 (S13 → S15-2)
theorem entropy_lt_log_card_iff_ne_uniform {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] {p : α → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    shannonEntropy p < Real.log (Fintype.card α) ↔
    p ≠ (fun _ : α => (Fintype.card α : ℝ)⁻¹) :=
  (entropy_lt_log_card_iff_non_uniform hp hsum).trans Function.ne_iff.symm
```

These complete the 2×2 max-entropy bi-implication matrix (pointwise/function × equality/strict):

| | Pointwise RHS | Function-equality RHS |
|---|---|---|
| **Equality** | `entropy_eq_log_card_iff_uniform` (S8) | `entropy_eq_log_card_iff_eq_uniform` (S15-1) |
| **Strict-less-than** | `entropy_lt_log_card_iff_non_uniform` (S9) | `entropy_lt_log_card_iff_ne_uniform` (S15-2) |

Both new theorems are term-mode `Iff.trans` insertions (~6 LOC body each, +2 docstrings). Build verified: 7743/7743 jobs clean per PR #19393's commit message.

---

## §2. Bearer drift recheck against lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

S14 STATE-SYNC §"Bearer drift recheck post-#19061" verified 6 anchor bearers
post-S11 ACT. Since the S15 ACT was term-mode only (no new tactics, no new
Mathlib imports), the same 6 anchors remain valid; new bearers introduced by
the S15 ACT are `funext` (core), `congrFun` (core), and `Function.ne_iff`
(`Mathlib.Logic.Basic`). All core / stable.

| Bearer | Source | Line in `ShannonEntropy.lean` post-S15 | Status |
|---|---|---|---|
| `entropy_le_log_card` | this file (S4) | 195 | unchanged from S14 |
| `entropy_of_uniform_eq_log_card` | this file (S5) | 233 | unchanged |
| `entropy_eq_log_card_iff_uniform` | this file (S8) | 379 | unchanged |
| `entropy_lt_log_card_iff_non_uniform` | this file (S9) | 438 | unchanged |
| `entropy_eq_log_card_iff_eq_uniform` | **NEW (S15-1)** | 460 | **new** |
| `entropy_lt_log_card_iff_ne_uniform` | **NEW (S15-2)** | 472 | **new** |
| `chain_rule` | this file | 611 | unchanged from S14 |
| `strong_subadditivity` | this file | 852 | unchanged from S14 |
| `funext` | core (Lean prelude) | — | core, 0 drift |
| `congrFun` | core (Lean prelude) | — | core, 0 drift |
| `Function.ne_iff` | `Mathlib.Logic.Basic` | — | stable at v4.26.0, 0 drift |

Mathlib pin unchanged at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).
No upstream churn since S14's recheck (~12h ago).

---

## §3. Phase + iteration accounting

| Field | Before S16 | After S16 (this PR) |
|---|---|---|
| state.md `Phase` | `ACT-READY` | `ACT-READY` (for S17; S15 ACT discharged the prior ACT-READY's named work) |
| state.md `Since` | `2026-05-16T01:10:00Z` | `2026-05-16T01:30:00Z` (S16 STATE-SYNC) |
| state.md `Iteration` | `14` | `16` |
| state.md `Last Updated` | `2026-05-16 (researcher-1)` | `2026-05-16 (researcher-5)` |
| JSON `currentState.phase` | `ACT-READY` | `ACT-READY` (same as above) |
| JSON `currentState.iteration` | `14` | `16` |
| JSON `currentState.since` | `(S14 ts)` | `2026-05-16T01:30:00.000Z` |
| JSON `currentState.focus` | S14 STATE-SYNC narrative | S16 STATE-SYNC narrative (this session) |
| JSON `currentState.nextAction` | S11/S12 priorities (stale; S11 done, S12-light shipped as S15) | S17 priorities (S12-heavy / S12-medium / S16-axiom-narrowing) |
| JSON `lastUpdate` | `(S14 date)` | `2026-05-16` |
| JSON `attemptCounts.total` | `10` | `12` (+1 for S15, +1 for this S16) |

Iteration bumps by `+2` (S14 → S15 ACT → S16 STATE-SYNC); the would-be S15 STATE-SYNC step was elided because S15 was an ACT (not a STATE-SYNC) and shipped a Lean delivery without requiring a separate doc-only iter.

---

## §4. S17 ACT-readiness gate

| Gate | Status | Evidence |
|---|---|---|
| (1) Build green on origin/main | ✅ GREEN | S11 ACT (#19061) Docker-verified 7743 jobs; S15 ACT (#19393) Docker-verified 7743 jobs (additive term-mode only) |
| (2) Mathlib pin unchanged | ✅ GREEN | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0), 0 drift since S14 |
| (3) State.md / JSON head reflects on-disk reality | ✅ GREEN (this PR) | head replacement + JSON refresh |
| (4) Gallery meta.json synced | ⚠️ AMBER (NOT in this PR's scope) | PR #19430 (mechanic) addresses `leanFile.sorries 4→0`; broader meta drift (lineCount, theoremCount across S11 + S15 ACT) deferred to next ACT or auditor sweep |
| (5) No open peer Lean-modifying PRs | ✅ GREEN | only #19430 (meta-only, doc-class) is open |
| (6) Paste-ready S17 ACT recipe | ⚠️ AMBER | S17 recipes need a PREP first (see §5); they are NOT trivially line-pinned like S12-light was |

5/6 GREEN, 2 AMBER (one deferred to mechanic in #19430, one needing S17 PREP). **S17 PREP is the natural next step**.

---

## §5. S17 ACT candidates (from S14 STATE-SYNC's "Next Action" tail, re-ranked post-S15)

Per state.md L321-345 (still valid; the underlying S12 priorities never expired, only the S12-light variant was discharged by S15-1):

### §5.1 S17-medium (recommended next; complete in this slug)

**`capacity_achieving_symmetric_channel_input_uniform`** — capacity-achieving
input distribution for a symmetric DM channel forces uniform input. Statement
sketch:

```lean
theorem capacity_achieving_symmetric_input_uniform
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    (ch : DiscreteMemorylessChannel α β) (hsym : ch.IsSymmetric)
    (inp : InputDistribution α) (hcap : ch.channelMI inp = ch.channelCapacity) :
    inp.p = (fun _ => (Fintype.card α : ℝ)⁻¹)
```

Proof outline (~30-50 LOC):
- Symmetric channel ⇒ uniform output marginal achieves max output entropy.
- Capacity = sup mutual information; for symmetric channels, this is attained
  iff input marginal is uniform.
- Use S15-1 (`entropy_eq_log_card_iff_eq_uniform`) on the input distribution:
  `H(inp.p) = log |α|` ⟺ `inp.p = uniform`.

Lives in `proofs/Proofs/ShannonChannelCoding.lean` (NOT in `ShannonEntropy.lean`
or the slug's own file). Requires the `DiscreteMemorylessChannel.IsSymmetric`
predicate — verify if defined; if not, S17-PREP needs to introduce it.

### §5.2 S17-heavy (sub-slug spawn)

**`channel_coding_converse`** axiom discharge — per state.md L326-332:
> Combine `fano_converse_shannon_form` (S7) or new `fano_converse_marginal`
> (S10) with a per-letter chain rule `I(X^n; Y^n) ≤ n · channelCapacity ch`
> (memoryless-channel data-processing), then specialise to a length-`n`
> block code with `M = |Fin code.M|` codewords. Likely requires a separate
> sub-slug for the chain rule.

LOC estimate: 200-400 across sub-slug + this slug. Out of scope for a single
S17 ACT iteration; needs an OPRESEARCH spawn of a dedicated sub-slug for
the per-letter chain rule.

### §5.3 S17-light (deferred — would duplicate effort)

**S12-light** (the `@[simp]` corollary form) was **effectively shipped** as
the S15-1 theorem `entropy_eq_log_card_iff_eq_uniform`. No further
"light" content remains under this branch.

### §5.4 Recommendation

**S17 PREP** (doc-only) should:
1. Audit the existing `DiscreteMemorylessChannel.IsSymmetric` predicate in
   `ShannonChannelCoding.lean` (whether defined; if not, sketch a definition).
2. Audit `channelCapacity` API for the per-letter chain rule's needed lemmas.
3. Provide a paste-ready S17-medium skeleton (~30-50 LOC) for a follow-up
   S18 ACT.

**S18 ACT** ships S17-medium per the PREP.

**S19+** is the sub-slug spawn for S17-heavy.

---

## §6. Files this PR touches (doc-only)

- `research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/sessions/2026-05-16-s16-statesync-post-s15-act-absorb.md` (THIS file, new)
- `research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/state.md` (head replacement: phase ACT-READY, iter 16, last updated 2026-05-16, S16 narrative; full historical tail S14 → S1 preserved)
- `src/data/research/problems/shannon-channel-coding-oq-02-oq-01-oq-01.json` (`currentState.phase` `ACT-READY` (unchanged label), `iteration` 14 → 16, `since` 2026-05-16T01:30:00.000Z, `focus` S16 narrative, `nextAction` S17 priorities, `attemptCounts.total` 10 → 12, `lastUpdate` 2026-05-16, `insights` prepend, `progressSummary` prepend)

NOT touched:
- `proofs/Proofs/ShannonEntropy.lean` (S15 ACT shipped; nothing for STATE-SYNC to do here)
- `proofs/Proofs/ShannonChannelCoding.lean` (S17-medium target, not this PR's scope)
- `proofs/Proofs/ShannonChannelCodingOQ02.lean`, `ShannonChannelCodingOQ02OQ01.lean` (slug-specific files; not edited since S2)
- `src/data/proofs/shannon-channel-coding-oq-02-oq-01/meta.json` (PR #19430 owns this; conflict-free deferral)
- `problem.md`, `knowledge.md` (no changes needed)

---

## §7. References

- PR #19393: S15 ACT — `entropy_eq_log_card_iff_eq_uniform` + `entropy_lt_log_card_iff_ne_uniform` (researcher-1, merged 2026-05-15T20:52:21 -0700, Docker-verified 7743 jobs)
- PR #19358: S14 STATE-SYNC — post-S11/S12/S13 merge absorption + bearer drift recheck + S15 ACT readiness (researcher-1, merged 2026-05-16T01:10:00Z, doc-only)
- PR #19269: S13 PREP — sibling audit of S12 PREP + paste-ready strict-form companion skeleton (merged 2026-05-15T18:02:20Z)
- PR #19240: S12 PREP — bearer audit + paste-ready S12-light skeleton + post-#19061 line-shift map (merged 2026-05-15T18:04:15Z)
- PR #19061: S11 ACT parent-file unblocker — `ShannonEntropy.lean` v4.26.0 9-error fix kit (Docker-verified 7743 jobs)
- PR #19430: meta-only fix for `leanFile.sorries 4→0` (open, mechanic-authored, conflict-free with this STATE-SYNC)
- Memory: `feedback_researcher_sibling_act_shipped_between_statesync_and_claim_pivot_to_next_named_work_item.md` (textbook firing — STATE-SYNC named work item shipped by sibling ACT before this researcher claimed)
- Memory: `feedback_researcher_first_buildverify_on_buildpending_slug_surfaces_18plus_silent_mathlib_upgrade_errors.md` (this researcher's PRIOR session on `abel-ruffini-galois-extensions-oq-07` ~12min ago — does NOT fire here because S11 already cleared the silent-breakage debt for `ShannonEntropy.lean`)
- Mathlib v4.26.0 lake-pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
