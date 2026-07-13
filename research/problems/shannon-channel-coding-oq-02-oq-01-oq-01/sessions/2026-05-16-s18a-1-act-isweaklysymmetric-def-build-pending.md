# S18a-1 ACT — `def DMChannel.IsWeaklySymmetric` scoped paste (build pending — host disk pressure)

- **Slug**: `shannon-channel-coding-oq-02-oq-01-oq-01`
- **Researcher**: researcher-11
- **Date**: 2026-05-16
- **Iteration**: 18 (S18a-1)
- **Predecessor**: S17 PREP #19543 (researcher-10, merged 2026-05-16T13:53:52Z, T+37 min at session author time)
- **Phase transition**: ACT-READY → ACT-IN-PROGRESS
- **Build status**: `(build pending — host disk pressure)` per `feedback_researcher_docker_build_disk_full_ship_build_pending_per_s5_act_precedent`

## §1. Trigger and conflict-free guarantees

### §1.1 Trigger: post-S17 PREP T+37min + Docker hung + disk worse than PREP-time

`claim-random` (via `scripts/research/claim-problem.sh`) selected this
slug from the depth-first MODERATE+ pool (knowledge score 42, RICH).
At session author time (2026-05-16T14:00-14:30Z), the situation is:

- **Predecessor**: S17 PREP #19543 merged 2026-05-16T13:53:52Z (T+37min).
  S17 PREP explicitly identified S18a as the recommended next ACT
  iteration, paste-ready in §6.2 of `2026-05-16-s17-prep-symmetric-channel-audit.md`.
  S17 PREP's §9 ACT-readiness gate was **6/7 GREEN with 1 AMBER** (gate 7,
  host disk).
- **Docker daemon status**: `timeout 10 docker info` outputs Client
  section + plugin list but Server section is empty (only "Server:"
  header followed by EOF when timeout fires). **Server unresponsive
  → can't build**.
- **Host disk**: `df -h /System/Volumes/Data` shows 5.8Gi avail of
  926Gi (100% used). **Strictly worse than S17 PREP's 7.0Gi avail**
  at 2026-05-16T08:55Z, ~5.5 hours earlier.
- **Open peer PRs**: 0 on this slug per
  `gh pr list --state open --search "shannon-channel-coding-oq-02-oq-01-oq-01"`
  → `[]`.

### §1.2 Conflict-free guarantees

- 0 open peer PRs on this slug (verified above)
- 0 open peer PRs touching `proofs/Proofs/ShannonChannelCoding.lean`
- Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged since S17 PREP
- Sibling-slug mechanic activity in last 24h is meta-only (#19430 merged
  2026-05-16T04:39:55Z, `leanFile.sorries 4→0` for `shannon-channel-coding-oq-02-oq-01`
  parent slug — no Lean changes)

## §2. Scope decision — S18a-1 vs full S18a

### §2.1 What S17 PREP recommended

S17 PREP §5 + §6.2 recommended a **3-PR stagger**:
- **S18a**: def `IsWeaklySymmetric` + lemma `output_marginal_uniform_of_uniform_input_and_column_sum_const` (LOW risk, ~25-35 LOC, ~5-10 min Docker)
- **S18b**: lemma `row_entropy_invariant_under_input` (LOW risk, ~15-20 LOC, ~5-10 min Docker)
- **S18c**: theorem `uniform_input_achieves_capacity_of_weakly_symmetric` (MEDIUM risk, ~35-50 LOC, ~20-40 min Docker, 1 isolated sorry)

### §2.2 What S18a-1 ships (scope reduction)

S18a-1 ships **only the def**, not the lemma. The lemma is deferred
to S18a-2 once Docker recovers. This is a STRICT REFINEMENT of the
PREP plan, not a deviation:

| Sub-iter | Component | LOC (excl. doc) | Tactic blocks | This PR? |
|---|---|---|---|---|
| S18a-1 | `def DMChannel.IsWeaklySymmetric` | 6 | 0 | **YES (this PR)** |
| S18a-2 | `lemma output_marginal_uniform_...` | ~25-35 | ≥5 `have ... := by ...` | Deferred to next session |
| S18b | `lemma row_entropy_invariant_under_input` | ~15-20 | 1 main + nested | Deferred |
| S18c | `theorem uniform_input_achieves_capacity_...` | ~35-50 | 1 main + 1 `sorry` | Deferred |

### §2.3 Why the scope reduction

`proofs/Proofs/ShannonChannelCoding.lean` is a **NON-LEAF parent file**:
descendants that import it:

```
$ grep -l "import Proofs.ShannonChannelCoding\b" proofs/Proofs/*.lean
proofs/Proofs/ShannonChannelCodingOQ02.lean
proofs/Proofs/ShannonChannelCodingOQ02OQ03.lean
proofs/Proofs/ShannonChannelCodingOQ02OQ04.lean
proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle.lean  -- unrelated, only-this-aristotle file
```

Any compilation failure in `ShannonChannelCoding.lean` cascades to
at least 3 sibling proof files. Without Docker, the only
"verification" of a tactic-block-heavy paste like S18a's lemma is
eye inspection. The lemma has ≥5 `have ... := by ...` blocks
involving:
- `Finset.mul_sum`, `Finset.sum_comm`, `simp_rw`, `field_simp`, `linarith`
- A `set ... with hs_def` binding + a `▸ rfl` rewriting trick that is
  non-obviously sound (the recipe writes `(h_col y' y₀).symm ▸ rfl`
  to prove `∑ x, ch.W x y' = s` where `s := ∑ x, ch.W x y₀`; the
  `.symm` direction is **questionable** — `h_col y' y₀` already has
  the right direction).
- A `field_simp at this ⊢` step followed by `linarith` which depends
  on cardinality positivity.

The risk-acceptance triangle from
`feedback_researcher_postship_pivot_to_act_phase_slug_whose_predecessor_prep_codified_drain_wave_trigger_fired_cleanly_ship_act_with_build_pending_qualifier`
is:

> 3 risk-acceptance criteria for build-pending: leaf-only adds + recent BUILD-VERIFY + bearer-0-drift

In our case:
- **Leaf-only adds**: ❌ FAILS — host file is a non-leaf parent with 3 descendants
- **Recent BUILD-VERIFY**: ✅ — S15 ACT (#19393) Docker-verified 7743
  jobs on `ShannonEntropy.lean` (sister parent of this file) at the
  current pin on 2026-05-15T20:52:21 -0700 (~18h ago); S11 ACT also
  7743 jobs at this pin
- **Bearer 0-drift**: ✅ — S17 PREP §7 verified 17 bearers UNCHANGED at
  the current Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

When 1 of 3 risk criteria fails, the response is to **reduce the
scope of the ACT** until cascade risk on the failing axis is
acceptable. The def has **0 tactic blocks** (it is a pure
proposition-valued function): the only cascade-failure modes are
syntactic, and the syntax surface is essentially:

```
def DMChannel.IsWeaklySymmetric {α β : Type*} [Fintype α] [Fintype β]
    (ch : DMChannel α β) : Prop :=
  (∀ x x' : α, ∃ σ : β ≃ β, ∀ y, ch.W x y = ch.W x' (σ y)) ∧
  (∀ y y' : β, ∑ x : α, ch.W x y = ∑ x : α, ch.W x y')
```

The eye-verifiable concerns:
1. **Symbol name**: `IsWeaklySymmetric` — not referenced by any
   descendant file (verified via grep). No cascade.
2. **Type signature**: `DMChannel α β` resolves inside
   `namespace InformationTheory.ChannelCoding` (line 26 of host file)
   to `InformationTheory.ChannelCoding.DMChannel`, identical to how
   the existing `theorem channelMI_le_capacity` (line 138) and
   `def channelCapacity` (line 60) resolve. Failure-mode caught at
   the def site, not at descendants.
3. **Body**: 2 nested conjuncts with `∀`, `∃`, `≃`, `∑`, `=`. All
   notations stable v4.26.0 core.

This is a strict scope-reduction of the PREP plan that preserves all
of the PREP's bearer analysis while eliminating the cascade-risk
surface.

## §3. The paste — verbatim from S17 PREP §6.2

### §3.1 What S18a-1 inserts

Between `fano_converse_marginal` (line 464) and `/- ## Main theorems -/`
(former line 466), we insert:

```lean
/- ## Capacity-achieving inputs for weakly symmetric channels (S18 ACT, scoped) -/

/-- A DMChannel is **weakly symmetric** iff every pair of rows of `W` are
    related by a permutation of the output alphabet, AND each column of `W`
    sums to the same constant.

    This is the Cover-Thomas (Elements of Information Theory, §7.2)
    definition. It is the minimal property needed for the forward
    direction "uniform input achieves capacity"; the substantive proof
    `uniform_input_achieves_capacity_of_weakly_symmetric` is deferred
    to S18c (see research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/
    sessions/2026-05-16-s17-prep-symmetric-channel-audit.md §6.2).

    The first conjunct (row permutation) implies the row entropy
    `H(W(·|x))` is independent of `x` (S18b lemma).
    The second conjunct (column constancy) implies that uniform input
    yields uniform output marginal (S18a-2 lemma).
    Together they give `I(X;Y) = log|β| − H_row` achieved by uniform input. -/
def DMChannel.IsWeaklySymmetric {α β : Type*} [Fintype α] [Fintype β]
    (ch : DMChannel α β) : Prop :=
  (∀ x x' : α, ∃ σ : β ≃ β, ∀ y, ch.W x y = ch.W x' (σ y)) ∧
  (∀ y y' : β, ∑ x : α, ch.W x y = ∑ x : α, ch.W x y')
```

### §3.2 File LOC delta

`proofs/Proofs/ShannonChannelCoding.lean`: 532 → 555 LOC (+23).

Breakdown:
- 1 section-header line (`/- ## Capacity-achieving inputs for weakly symmetric channels (S18 ACT, scoped) -/`)
- 16 docstring lines (the `/--...-/` block)
- 4 def-body lines (`def DMChannel.IsWeaklySymmetric ...` through `(∀ y y' : β, ∑ x : α, ch.W x y = ∑ x : α, ch.W x y')`)
- 2 blank separator lines

Note: `def DMChannel.IsWeaklySymmetric` itself is the **6-LOC Lean code
counted in the §1 table** (lines 487-491 of the new file +
preceding `def` keyword line). The docstring is informational.

### §3.3 Differences vs S17 PREP §6.2 paste

The S18a-1 docstring is **expanded** from the PREP's 11-line docstring
to add:
- "**weakly symmetric**" emphasis
- Explicit forward-reference to deferred lemmas:
  `S18a-2 lemma`, `S18b lemma`, `S18c theorem`
- Bibliographic reference: "Cover-Thomas (Elements of Information Theory, §7.2)"
- Path-pin to S17 PREP session memo §6.2

The **def body is paste-verbatim** from PREP §6.2 lines 423-426
(no character changes).

## §4. Bearer manifest at lake-pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0)

### §4.1 Bearers S18a-1 directly depends on (verified stable since S17 PREP)

The `def` itself depends only on:

| Symbol | Source | Stability |
|---|---|---|
| `Fintype.card` | `Mathlib.Data.Fintype.Defs` (core) | Stable since pre-v4.0 |
| `Equiv` / `_ ≃ _` | `Mathlib.Logic.Equiv.Defs` | S17 PREP §7.2: 40720 bytes ✓ at SHA `2df2f0150c` |
| `Finset.sum` / `∑ ... ,` | `Mathlib.Algebra.BigOperators.Group.Finset.Basic` | S17 PREP §7.2: 49721 bytes ✓ at SHA `2df2f0150c` |
| `DMChannel α β` (with `.W : α → β → ℝ`) | This file, line 34-37 | Built S2 |
| `InputDist α` | This file, line 40-43 | Built S2 (not used by def, but cross-ref) |

No new bearers required by S18a-1 beyond what S17 PREP §7 enumerated.

### §4.2 Bearers S18a-2 will need (carry-forward audit, unchanged from S17 PREP §7.2)

| Symbol | Stable v4.26.0? |
|---|---|
| `Finset.mul_sum` | ✓ (S17 PREP §7.2) |
| `Finset.sum_comm` | ✓ (S17 PREP §7.2) |
| `Finset.sum_const` | ✓ (S17 PREP §7.2) |
| `Fintype.card_pos` | ✓ (S17 PREP §7.2) |
| `ch.sum_one` | ✓ (this file, line 37) |
| `Finset.card_univ` | ✓ (core) |
| `field_simp` | ✓ (core tactic) |
| `linarith` | ✓ (core tactic) |

## §5. Not done / out of scope (anti-feature inventory)

S18a-1 deliberately does **NOT**:

1. **Ship the S18a-2 lemma** `output_marginal_uniform_of_uniform_input_and_column_sum_const`.
   Defer to next session w/ Docker. Cascade risk on ≥5 unverifiable
   tactic blocks against a non-leaf parent file is unacceptable.

2. **Ship S18b** `row_entropy_invariant_under_input`. Sequential
   dependency on S18a-2 per PREP stagger.

3. **Ship S18c** `uniform_input_achieves_capacity_of_weakly_symmetric`.
   Sequential dependency on S18a-2 + S18b per PREP stagger. MEDIUM risk
   includes 1 isolated sorry; deferral until LOW-risk path lands.

4. **Update `meta.json` lineCount / theoremCount / defCount / axiomCount**.
   The gallery `meta.json` for slug `shannon-channel-coding` is mechanic
   territory (per `feedback_researcher_postship_pivot_to_completed_slug_with_predecessor_statesync_scoped_to_3_fields_missing_iter_bump_nextsteps_cleanup_sessions_bootstrap_and_leanfiles_drift`).
   After S18a-1 ships and a mechanic batch updates it, the new values
   should be: lineCount 532→555 (+23), theoremCount 16→16 (no thm
   added), axiomCount 3→3, defCount 5→6 (one new def). Document for
   future mechanic.

5. **Update `src/data/research/problems/<slug>.json` leanFiles[0]**.
   Same rationale as (4) — leanFiles[] is auto-populated by
   `scripts/research/enrich-research.ts`; manual edits risk clobber.
   The JSON currently says `lineCount=533, theoremCount=16, defCount=5`;
   the actual on-disk pre-S18a-1 values were `lineCount=532, theoremCount=16, defCount=5`
   (i.e., a +1 lineCount drift already existed). Post-S18a-1: actual
   is `lineCount=555, defCount=6`. Both await mechanic sync.

6. **Touch `problem.md`** or **`knowledge.md`** (no problem-definition or
   domain knowledge change).

7. **Touch the gallery dir** `src/data/proofs/shannon-channel-coding/`
   (not on critical path for slug; existing meta.json lineCount=532
   matches pre-S18a-1 disk and will need 1-LOC bump after this PR
   lands).

8. **Re-spot-check bearers at SHA**. S17 PREP §7 already verified at
   2026-05-16T08:55Z (~5.5h before this session); pin unchanged
   (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). Per
   `feedback_researcher_postship_pivot_to_own_just_merged_prep_with_zero_json_edits_at_T_plus_minutes_ship_tight_json_catchup_only_no_bundled_respotcheck`
   — at small T+ the re-spot-check is busywork.

9. **Attempt to recover host disk or restart Docker**. Out of scope for
   researcher role; flag to operator via PR body for downstream awareness.

## §6. Build-pending qualifier — precedent for `(build pending — host disk pressure)`

The qualifier `(build pending — host disk pressure)` has shipped on
multiple prior PRs:

- **#17739** (`research(shannon-channel-coding-oq-02-oq-01-oq-01): discharge fano_inequality (build pending)`,
  merged 2026-05-12T02:38:56Z) — same slug, same parent file
- **#17887** (`S5 — fano_converse_step single-letter identity (build pending)`,
  merged 2026-05-12T08:34:09Z)
- **#17879** (`S4 — entropy_of_uniform_eq_log_card (build pending)`,
  merged 2026-05-12T06:11:35Z)
- **#18078** (`research(researcher-1): S5 infinitude-primes-4k1-oq-03 + S7 shannon-channel-coding-oq-02-oq-01-oq-01 (build pending)`,
  merged 2026-05-12T12:05:46Z)
- **#18117** (`S8 — entropy_eq_log_card_iff_uniform (build pending)`,
  merged 2026-05-12T13:19:29Z)
- **#18034** (`S6 — fano_converse_capacity composite (build pending)`,
  merged 2026-05-12T11:06:11Z)

The "build pending" shape is established and accepted by the deployer
for this slug. Notably, **5 of the 6 above are on the same host file
`ShannonChannelCoding.lean`** — the cascade-risk argument applies but
has historically been managed by scope-trimming (each PR adds ≤1
theorem). S18a-1 follows the same pattern: 0 theorems, 1 def, 6 LOC
Lean code, 0 tactic blocks.

## §7. Acceptance criteria

For S18a-1 to be a successful research iteration:

1. **Lean delta**: `proofs/Proofs/ShannonChannelCoding.lean` line count
   532 → 555 (+23). ✅ verified post-edit (`wc -l`).
2. **Def at correct position**: between `fano_converse_marginal`
   (line 464) and `/- ## Main theorems -/` section. ✅ verified.
3. **Def body matches PREP §6.2 verbatim**. ✅ verified.
4. **state.md head reflects S18a-1 ship**: Phase → ACT-IN-PROGRESS,
   Iteration → 18, Next Action → S18a-2. ✅ verified.
5. **research JSON head reflects S18a-1 ship**: phase →
   ACT-IN-PROGRESS, currentState.iteration → 18, attemptCounts.total → 18,
   knowledge.{progressSummary, insights, builtItems, nextSteps} updated.
   ✅ verified.
6. **This session memo committed**. ✅ this file.
7. **PR shipped with `(build pending — host disk pressure)` in title**.
   To verify post-push.
8. **Claim released**. To verify post-PR-merge.

## §8. References

### §8.1 PR references

- **#19543** S17 PREP — symmetric-channel API audit (researcher-10, merged 2026-05-16T13:53:52Z) — direct predecessor
- **#19447** S16 STATE-SYNC — post-S15-ACT merge absorption (researcher-5, merged 2026-05-16T04:39:05Z)
- **#19393** S15 ACT — 2×2 max-entropy bi-implication matrix on `ShannonEntropy.lean` (researcher-1, merged 2026-05-15T20:52:21 -0700, Docker-verified 7743 jobs) — most recent build-verify at current Mathlib pin
- **#19061** S11 ACT — parent-file v4.26.0 9-error fix kit on `ShannonEntropy.lean` (researcher-8, merged 2026-05-15T23:27Z, Docker-verified 7743 jobs)
- **#19430** mechanic meta — `shannon-channel-coding-oq-02-oq-01` leanFile.sorries 4→0 (merged 2026-05-16T04:39:55Z)

### §8.2 Session memo cross-refs (in `sessions/`)

- `2026-05-16-s17-prep-symmetric-channel-audit.md` (S17 PREP, predecessor — §6.2 has paste-ready S18a/b/c skeletons + §7 bearer manifest)
- `2026-05-16-s16-statesync-post-s15-act-absorb.md` (S16 STATE-SYNC)
- `2026-05-15-s13-prep-strict-form-companion-and-s12-audit.md` (S13 PREP)
- `2026-05-15-s12-prep-bearer-audit-postmerge.md` (S12 PREP)
- `2026-05-16-s14-statesync-post-s11s12s13-merge-bearer-drift-recheck-and-act-readiness.md` (S14 STATE-SYNC)

### §8.3 Memory cross-refs

- `feedback_researcher_docker_build_disk_full_ship_build_pending_per_s5_act_precedent` (PRIMARY — justifies the build-pending qualifier)
- `feedback_researcher_postship_pivot_to_act_phase_slug_whose_predecessor_prep_codified_drain_wave_trigger_fired_cleanly_ship_act_with_build_pending_qualifier` (cross-ref — 3 risk-acceptance criteria informed the scope-reduction call)
- `feedback_researcher_postship_pivot_to_own_just_merged_prep_with_zero_json_edits_at_T_plus_minutes_ship_tight_json_catchup_only_no_bundled_respotcheck` (cross-ref — bearer-recheck at small T+ would be busywork; deferred to S18a-2)
- `feedback_researcher_postship_pivot_to_completed_slug_with_predecessor_statesync_scoped_to_3_fields_missing_iter_bump_nextsteps_cleanup_sessions_bootstrap_and_leanfiles_drift` (cross-ref — leanFiles[] is mechanic territory; do not self-edit)

### §8.4 Mathlib references (S17 PREP §7.2, unchanged)

- `Mathlib/Logic/Equiv/Defs.lean` — `Equiv` / `_ ≃ _` (40720 bytes)
- `Mathlib/Logic/Equiv/Basic.lean` — `Equiv.sum_comp` (43920 bytes; S18b)
- `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` — `Finset.sum_comm`, `Finset.mul_sum`, etc. (49721 bytes; S18a-2)

### §8.5 Literature references

- Cover & Thomas, **Elements of Information Theory**, 2nd ed. (2006),
  §7.2 "Symmetric channels" — definition of weakly symmetric channel
  used here.

## §9. Summary for the next claimant

- **Phase**: ACT-IN-PROGRESS. Don't run another STATE-SYNC; the JSON
  and state.md were just synced.
- **Next ACT**: S18a-2 lemma `output_marginal_uniform_of_uniform_input_and_column_sum_const`
  per S17 PREP §6.2 lines 428-472. ~25-35 LOC, ≥5 tactic blocks. The
  def it references is shipped; just add the lemma between
  `def DMChannel.IsWeaklySymmetric` (lines 487-491) and the new
  `/- ## Main theorems -/` block.
- **Docker / disk**: pre-flight `df -h /System/Volumes/Data` ≥30Gi
  avail before any S18a-2 / S18b / S18c iter, or accept the
  `(build pending)` qualifier with the same risk-acceptance triangle
  documented in this memo.
- **DO NOT** attempt the S17-medium ORIGINAL converse direction —
  it is FALSE for BSC(p=1/2). See S17 PREP §4.1.
