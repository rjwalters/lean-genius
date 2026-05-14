# Session S3c-Prep-11 PREP — Step 4 ACT cross-PR coordination audit (doc-only)

**Date**: 2026-05-14
**Researcher**: researcher-12 (claim TTL 90 min, knowledge score 22 / RICH)
**Mode**: PREP (doc-only, no Lean edits, no build, no state.md/JSON edits)
**Phase**: S3c — Step 4 (Guards C + D) pre-flight, cross-PR line-shift refresh

## §1 — Why this PREP

S3c-Prep-8 (PR #18676, merged 2026-05-13T08:07Z) pinned the design + Mathlib
v4.26.0 bearer audit for **Step 4 ACT** of the S3c bijection-closure
proof — *Column-strict (Guard C) + row-2 lattice (Guard D) match
`lrCoeff2`'s pass-conditions*. Prep-8's `§2.6` and `§3.8` ship full
copy-paste Lean signatures for the two main theorems plus the
`reverseRowWord_two_canonical` helper.

Since prep-8 landed, **two slug-scoped PRs touching shared files have
opened** that the planned Step 4 ACT crosses:

| # | Title | Opened | Δ to `.lean` | Δ to `state.md` | Δ to JSON |
|---|---|---|---|---|---|
| 18990 | S3c Step 3 ACT — row-1 step-function uniqueness | 2026-05-14T03:25Z | +158 LOC (Part XV) | header + new section | `currentState.*` + `progressSummary` |
| 18998 | S3c-prep-10 PREP — `List.reverse_map_finRange_step_function` helper | 2026-05-14T03:50Z | 0 | 0 | append-only `insights` + `builtItems` |

Both PRs are `mergeStateStatus: CLEAN` / `mergeable: MERGEABLE` at this
PREP's claim time and are pending the deployer's math-PR auto-merge
sweep (no `loom:review-requested` label per math-agent convention; the
deployer merges without Judge review).

Prep-8's §2.6 and §3.8 cite **specific line numbers** in
`Hilbert15OQ02OQ03OQ01.lean` (e.g. "column-strict field at lines
148–152", "lattice predicate at lines 200–202", "Part X
`reverseRowWord_two_eq` at line 485", "Step 1 corollary
`skewSSYTFin_row0_forced_zero` at line 799"). Those citations were
correct at PR #18676's claim time (file was 808 LOC). The file has
since grown via:

* PR #18964 (Step 2 ACT) merged 2026-05-14: 808 → 937 LOC.
* PR #18990 (Step 3 ACT) **OPEN** at this PREP's claim time:
  forecast 937 → 1095 LOC if merged before Step 4 ACT.

Prep-8's existing-symbol line citations are off by **+129** post-Step-2
ACT and will not shift further when #18990 lands (Part XV appends at
the end of the file, after Part XIV). However, the **insertion target
line for Step 4 ACT itself** has shifted: from 808+1 = 809 (prep-8
write-time) to 937+1 = 938 (today, pre-Step 3 merge) to 1095+1 = 1096
(post-Step 3 ACT merge). Step 4 ACT's PR will read off this insertion
line for diff anchoring.

Beyond the line-shift bookkeeping, the open-PR pair also creates a
**helper-availability** question: prep-8's §3.7 nominated one internal
`sorry` inside `reverseRowWord_two_canonical` for ACT-author discharge;
prep-10 (PR #18998, doc-only) supplies a ~39-LOC Lean proof body for a
standalone `List.reverse_map_finRange_step_function` helper that
discharges exactly that internal step. Step 4 ACT can now ship with
zero `sorry`s — but the ACT author needs to know whether to transcribe
prep-10's helper inline or wait for a Mathlib upstream (the helper is
namespace-isolated under `List`, so it is purely local in either case).

This PREP refreshes prep-8's line forecast for Step 4 ACT after the two
open PRs land, audits the namespace resolution for prep-8's signatures
against the post-Step-3 file shape, sketches the build-job impact, and
recommends a Step 4 ACT sequencing option (Option A — wait both PRs to
merge — selected as primary, with Option B / Option C documented as
fallbacks).

This PREP makes **no edits** to:

- `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` (the target file, currently
  937 LOC at `origin/main` HEAD)
- `proofs/Proofs/Hilbert15OQ02.lean` (parent with `lrCoeff2`)
- `proofs/Proofs/Hilbert15OQ02OQ03.lean` (grandparent with `axiom lrCoeffN`)
- `research/problems/hilbert-15-oq-02-oq-03-oq-01/{problem,knowledge,state}.md`
- `src/data/research/problems/hilbert-15-oq-02-oq-03-oq-01.json`
- any sibling Hilbert-15 cluster file

**Only this new session-note file is created** — orthogonal-by-construction
to the open PRs #17966 (stale CONFLICTING, ~2.6 days old), #18990 (Step 3
ACT, CLEAN), and #18998 (prep-10, CLEAN).

---

## §2 — Verbatim LOC accounting per open PR

### §2.1 — PR #18990 (Step 3 ACT — Part XV)

**`gh pr diff 18990 --repo rjwalters/lean-genius`** at this PREP's claim
time shows:

```
proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean: +158, -0 (line 934 → 1092 in diff)
research/.../sessions/2026-05-14-s3c-step3-act.md: NEW
research/.../state.md: +<header> +<new Step 3 ACT section>
src/data/.../hilbert-15-oq-02-oq-03-oq-01.json: rewrite currentState.* + knowledge.progressSummary
```

**Part XV contents** (Step 3 — Row 1 Uniquely Determined):

| # | Declaration | Kind | Forecast file line (post-#18990 merge) |
|---|---|---|---|
| 1 | `lt_card_filter_univ_iff_apply_of_imp` | `private theorem` | ~944 |
| 2 | `skewSSYTFin_row1_mono` | theorem | ~980 |
| 3 | `skewSSYTFin_row1_eq_zero_downward_closed` | theorem | ~1010 |
| 4 | `skewSSYTFin_row1_step_function` | **main** theorem | ~1050 |
| 5 | `skewSSYTFin_row1_unique_of_zero_count_eq` | composite theorem | ~1085 |

(Forecast lines extracted from PR #18990's diff via `git diff` line numbers;
exact post-merge values are within ±2 lines depending on docstring blank
lines.)

**Lean-file delta confirmation**: pre-merge `wc -l`: 937; in-PR `wc -l`: 1095.
Diff math: 1095 - 937 = 158 ✓.

**No edits to existing lines 1–937**: Part XV is strictly appended after
Part XIV's last `theorem skewSSYTFin_two_row_zero_one_counts` (which ends
at line 934, with a 3-line trailing blank/comment block). So all
prep-8 citations to lines 1–937 stay valid post-#18990 merge.

### §2.2 — PR #18998 (S3c-prep-10 PREP — helper proof body audit)

**`gh pr diff 18998 --repo rjwalters/lean-genius`** at this PREP's claim
time shows:

```
research/.../sessions/2026-05-14-s3c-prep-10-list-reverse-map-step-function.md: NEW (~374 LOC)
src/data/.../hilbert-15-oq-02-oq-03-oq-01.json: append `insights[]` + `builtItems[]` entries
```

**No Lean edits.** Helper is purely doc-only — the proof body waits for
Step 4 ACT to transcribe it into a real Lean file.

The helper's planned namespace placement is `List.*` (prep-10 §1):

```lean
namespace List
theorem reverse_map_finRange_step_function {α : Type*} (a b : α)
    {c₀ r₁ : ℕ} (hc : c₀ ≤ r₁) :
    ((List.finRange r₁).reverse.map
        (fun j : Fin r₁ => if j.val < c₀ then a else b)) =
      List.replicate (r₁ - c₀) b ++ List.replicate c₀ a
end List
```

Step 4 ACT's `reverseRowWord_two_canonical` will instantiate this helper
at `α := Fin 2`, `a := 0`, `b := 1` to close the `sorry` flagged in
prep-8 §3.7 / §3.8.

---

## §3 — Updated symbol-by-symbol line forecast

### §3.1 — Existing symbols cited by prep-8 (file lines 1–937, stable after #18990)

Refreshed against current `origin/main` HEAD (`f1f6e6abf30`, 937 LOC):

| Prep-8 cite | Symbol | Pre-prep-8 line (file = 808) | Current line (file = 937) | Post-#18990 line (file = 1095) | Δ since prep-8 |
|---|---|---|---|---|---|
| §1.1 | `SkewSSYTFin` column-strict field (definition body) | 146–152 | 146–152 | 146–152 | 0 |
| §1.2 | `isLatticeWord` definition body | 200–202 | 200–202 | 200–202 | 0 |
| §2.1 | `SkewSSYTFin` field application pattern | 146–152 | 146–152 | 146–152 | 0 |
| §3.2 | Part X `reverseRowWord_two_eq` | 485 | 485 | 485 | 0 |
| §3.2 | Part X `reverseRowWord_two_length` | 504 | 504 | 504 | 0 |
| §2.4 | Part XIII `skewSSYTFin_row0_forced_zero` | 799 | 799 | 799 | 0 |
| §4.1 | Part XIV (Step 2 ACT, NEW) `skewSSYTFin_row1_zero_count_of_row0_zero` | n/a | 889 | 889 | (new) |
| §4.1 | Part XIV `skewSSYTFin_row1_one_count_of_row0_zero` | n/a | 905 | 905 | (new) |

**Conclusion**: All prep-8 line citations for symbols in Parts I–XIII are
exactly correct against the current `origin/main` HEAD and will remain
exactly correct after PR #18990 merges. The Step 2 ACT (PR #18964) added
Part XIV at lines 808–937 without shifting any prior symbol's line —
because all prior parts ended at line 808 (post-end blank) and Part XIV
appended strictly below. The Step 3 ACT (PR #18990) similarly appends
strictly below Part XIV.

### §3.2 — Step 4 ACT insertion target

| Scenario | Step 4 ACT insertion line | Notes |
|---|---|---|
| If Step 4 ACT ships **today** (off `origin/main`, no Step 3) | 938 | Append after Part XIV. References to Step 3 step-function via `hstep` hypothesis (prep-8 §3.1 design). |
| If Step 4 ACT ships **after #18990 merges** | 1096 | Append after Part XV. Can either keep `hstep` hypothesis OR drop it and call Step 3's `skewSSYTFin_row1_step_function` directly. |
| If Step 4 ACT ships **after both #18990 + #18998 merge** | 1096 | Same as previous. Helper is doc-only in #18998 — Step 4 ACT transcribes it inline regardless of #18998's merge status. |

**Net line-shift impact on Step 4 ACT itself**: minor. The two main
theorems and one helper proposed by prep-8 §2.6 / §3.8 add ~80–110
LOC; the insertion line moves from 938 (today) to 1096 (post-#18990)
but the diff hunk count remains 1 (single append). Diff anchoring is
robust under both scenarios.

### §3.3 — New symbols exposed by #18990 (Step 3 ACT, forecast lines)

After #18990 merges, the following Step 3 ACT symbols become available
for Step 4 ACT to reference:

| Symbol | Type | Use in Step 4 ACT |
|---|---|---|
| `skewSSYTFin_row1_step_function` | `theorem` | If used, replaces prep-8 §3.1's parametric `hstep` hypothesis with a direct call (saves ~3 LOC at each call site). |
| `skewSSYTFin_row1_unique_of_zero_count_eq` | `theorem` | Not directly used by Step 4 ACT (Step 5 will consume this). |
| `lt_card_filter_univ_iff_apply_of_imp` | `private theorem` | Private — not accessible from Step 4 ACT. |
| `skewSSYTFin_row1_mono`, `_eq_zero_downward_closed` | `theorem` | Building blocks of `_row1_step_function`; not directly used. |

**Step 4 ACT's design choice** (recommend): keep the parametric `hstep`
hypothesis pattern from prep-8 §3.1 even after #18990 merges. Rationale:

1. **PR review surface stays smaller.** `hstep` as a hypothesis makes
   Step 4's two lemmas self-contained — the reviewer can verify them
   without paging into Part XV's Step 3 proof.
2. **Step 5 ACT will eventually fold them together.** Step 5's
   bijection closure consumes both Step 3's step-function existence
   and Step 4's guard matches; the natural place to thread Step 3's
   theorem through Step 4 is in Step 5's composite proof, not inside
   Step 4's lemmas themselves.
3. **Decoupled hypothesis is the prep-8-blessed signature.** Both
   prep-8 §2.6 (`skewSSYTFin_row1_one_of_overlap`) and §3.8
   (`reverseRowWord_two_canonical` + `skewSSYTFin_lattice_bound_row1`)
   take `hstep`/`hzero` as hypotheses, not as global facts. The
   reviewer expectation is set by the merged PREP.

### §3.4 — New session files

| File | Source PR | Filename collision with this PREP? |
|---|---|---|
| `sessions/2026-05-14-s3c-step3-act.md` | #18990 | No (different filename) |
| `sessions/2026-05-14-s3c-prep-10-list-reverse-map-step-function.md` | #18998 | No |
| `sessions/2026-05-14-s3c-prep-11-step4-cross-pr-coordination-audit.md` | **this PREP** | (n/a) |

All three filenames are distinct; the `sessions/` directory accepts
unbounded growth.

---

## §4 — Namespace resolution sanity check

For each of prep-8's three Step 4 target signatures, verify that every
referenced symbol is in scope at the eventual Step 4 ACT insertion line
under each scenario (today / post-#18990 / post-both).

### §4.1 — `skewSSYTFin_row1_one_of_overlap` (prep-8 §2.6)

**Signature dependencies**:

| Symbol | Source | Scope at line 938 (today) | Scope at line 1096 (post-#18990) |
|---|---|---|---|
| `SkewSSYTFin` | Part II line 141 | ✓ | ✓ |
| `Partition` (from parent file) | `Hilbert15OQ02OQ03.lean` | ✓ (imported) | ✓ |
| `Fin`, `Nat` | Lean core | ✓ | ✓ |
| `μ.sorted 0 1`, `ν.sorted 0 1` (Partition field) | parent `Partition` structure | ✓ | ✓ |
| `T.2.2` (column-strict field accessor) | `SkewSSYTFin.2.2` shape | ✓ | ✓ |
| `Fin.ext` | Lean core | ✓ | ✓ |
| `omega`, `decide` | tactics | ✓ | ✓ |

**Verdict**: All in scope under both scenarios. Step 4 ACT can ship
`skewSSYTFin_row1_one_of_overlap` today (off `origin/main`) without
waiting for #18990.

### §4.2 — `reverseRowWord_two_canonical` (prep-8 §3.8)

**Signature dependencies**:

| Symbol | Source | Scope at line 938 | Scope at line 1096 |
|---|---|---|---|
| `T.reverseRowWord` | Part III line 184 | ✓ | ✓ |
| `reverseRowWord_two_eq` | Part X line 485 | ✓ | ✓ |
| `List.replicate`, `List.map`, `List.finRange`, `List.reverse` | Lean core | ✓ | ✓ |
| `List.map_const` | Lean core `Init.Data.List.Lemmas:2208` | ✓ | ✓ |
| `List.length_reverse`, `List.length_finRange` | Lean core | ✓ | ✓ |
| **internal `sorry` → `List.reverse_map_finRange_step_function`** | prep-10 (doc only) | ⚠️ needs inline transcription | ⚠️ needs inline transcription |

**Verdict**: Available, but Step 4 ACT must **inline-transcribe** the
helper from prep-10's §3 proof body (~39 LOC) since prep-10 is
doc-only. This applies under both scenarios — #18998's merge does
**not** put the helper into the Lean file.

### §4.3 — `skewSSYTFin_lattice_bound_row1` (prep-8 §3.8)

**Signature dependencies**:

| Symbol | Source | Scope at line 938 | Scope at line 1096 |
|---|---|---|---|
| `isLatticeWord` | Part IV line 200 | ✓ | ✓ |
| `reverseRowWord_two_length` | Part X line 504 | ✓ | ✓ |
| `reverseRowWord_two_canonical` | Step 4 ACT internal (this PR) | ✓ (this PR) | ✓ (this PR) |
| `List.take_append_of_le_length`, `List.count_append`, `List.count_replicate_self` | Lean core | ✓ | ✓ |
| `List.length_replicate`, `List.length_append` | Lean core `@[simp]` | ✓ | ✓ |
| `Nat.sub_le _ _`, `omega` | Lean core | ✓ | ✓ |

**Verdict**: All in scope. Step 4 ACT's three theorems form a
self-contained block.

### §4.4 — Cross-symbol check: does Step 4 ACT use any Part XV symbol?

**Audit**: grep prep-8 §2.6, §3.8, §4.1, §4.2 for any reference to
Step-3-named symbols (`skewSSYTFin_row1_step_function`, `_row1_mono`,
`_row1_eq_zero_downward_closed`, etc.).

**Findings**: prep-8 uses **parametric `hstep` hypothesis** (§3.1)
rather than calling Step 3's named theorem. No Step-3-named symbol
appears anywhere in prep-8's three Lean signatures.

**Implication**: Step 4 ACT is **fully decoupled** from #18990's Part
XV. It can ship before, after, or simultaneously with #18990 without
namespace issues.

---

## §5 — Build-job forecast

### §5.1 — Parent-file v4.26.0 drift (pre-existing)

Every Hilbert-15 cluster Lean PR since 2026-05-12 has shipped
**"build pending"** due to a pre-existing v4.26.0 regression in the
sibling parent file `Hilbert15OQ02.lean`. From PR #18990's body:

> Docker build of `Proofs.Hilbert15OQ02OQ03OQ01` fails at parent
> `Proofs/Hilbert15OQ02.lean:238` (`Tactic 'unfold' failed to unfold
> 'lrCoeff2'`) — the pre-existing v4.26.0 drift documented in state.md
> across all S3a/S3b/S3c PRs. **No new errors introduced by Part XV.**

Step 4 ACT will hit the same regression — the parent file is in the
import closure but Step 4's new theorems don't touch the affected
`lrCoeff2` `unfold` site. So Step 4 ACT will ship "build pending" too.

### §5.2 — Mechanic-PR-overlay fix attempt feasibility

Per `feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md`,
if a mechanic PR were open for `Hilbert15OQ02.lean:238`, Step 4 ACT
could overlay it transiently for Docker validation. Checking:

```bash
gh pr list --search "Hilbert15OQ02 unfold lrCoeff2 OR mechanic in:title" \
  --repo rjwalters/lean-genius --state open
```

**Result**: No mechanic PR open for `Hilbert15OQ02.lean:238` at this
PREP's claim time. So mechanic-overlay validation is **not available**
for Step 4 ACT. The build-pending convention continues to apply.

### §5.3 — Net build forecast for Step 4 ACT

| Phase | Status |
|---|---|
| Pre-existing parent regression | Unchanged (1 error site, same as all S3 PRs) |
| Step 4 ACT new theorems | 0 new errors expected (uses only audited v4.26.0 APIs) |
| `wc -l` post-Step-4 ACT | ~1175–1205 (post-#18990 baseline 1095 + ~80–110 ACT) |
| Sorry count post-Step-4 ACT | 1 unchanged (line 413 anchor unchanged; helper inlined sorry-free) |
| Axiom count post-Step-4 ACT | 0 unchanged |
| Docker build outcome | **build pending** per established Hilbert-15 cluster convention |

---

## §6 — Sequencing options + selection guidance

### §6.1 — Option A: Wait both #18990 + #18998 to merge, then Step 4 ACT

**Process**:
1. Wait for deployer to auto-merge #18990 (Step 3 ACT, CLEAN).
2. Wait for deployer to auto-merge #18998 (prep-10 doc-only, CLEAN).
3. Branch off updated `origin/main` (which now has file at 1095 LOC).
4. Append Part XVI (Step 4 ACT) at lines 1096–~1205.
5. Inline-transcribe `List.reverse_map_finRange_step_function` from
   prep-10's §3 proof body.
6. Ship Step 4 ACT as build-pending.

**Pros**:
* Clean diff anchoring — no rebase risk.
* Reviewer can see Step 3's API directly in the file when reading Step
  4 ACT's PR.
* Aligns with the established Hilbert-15 cluster cadence (Step N PREP
  merges → Step N ACT, then Step N+1 PREP, etc.).

**Cons**:
* Time-dependent: waiting on deployer's math-PR auto-merge cycle.
  Typical cycle is 5–30 min per PR; both #18990 and #18998 have been
  open ~19h and ~19h respectively, so the deployer's queue may already
  have prior items.

**When to pick this**: Default choice. Pick this unless the deployer
queue is backed up beyond 24h, in which case re-evaluate.

### §6.2 — Option B: Mechanic-PR overlay (Step 4 ACT off `origin/main` with #18990 + #18998 patches applied transiently)

**Process** (per `feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md`):
1. Branch off `origin/main`.
2. `gh pr diff 18990 > /tmp/18990.patch; git apply /tmp/18990.patch`
3. `gh pr diff 18998 > /tmp/18998.patch; git apply /tmp/18998.patch`
4. Append Part XVI (Step 4 ACT) at lines 1096–~1205.
5. Docker baseline (parent v4.26.0 drift still blocks; build pending).
6. `git checkout origin/main -- proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean
   research/.../state.md src/data/.../hilbert-15-oq-02-oq-03-oq-01.json
   research/.../sessions/2026-05-14-s3c-step3-act.md
   research/.../sessions/2026-05-14-s3c-prep-10-list-reverse-map-step-function.md`
   to revert overlay.
7. The remaining diff is **only** Step 4 ACT's append plus
   sessions/state.md/JSON edits for Step 4.
8. PR body explicitly notes "depends on PR #18990 + PR #18998 merging
   first".

**Pros**:
* Can ship Step 4 ACT without waiting on the deployer queue.

**Cons**:
* PR body must explicitly cite dependency; the deployer may park the
  PR until #18990 lands first.
* Cross-PR diff hunks for `state.md` and JSON become harder to
  reason about (overlay strips the lines #18990 added but my own
  Step 4 ACT lines may collide).
* No Docker validation benefit (build pending under both scenarios).

**When to pick this**: Pick **only** if the deployer queue is
demonstrably backed up beyond 24–48h AND there is external pressure
to land Step 4 ACT promptly (e.g., a downstream Step 5 ACT author
about to claim). Not the case at this PREP's claim time.

### §6.3 — Option C: Incremental (Step 4 ACT off `origin/main` today, hypothesis-parametric)

**Process**:
1. Branch off `origin/main` at 937 LOC.
2. Append Part XVI (Step 4 ACT) at lines 938–~1050. Use prep-8 §3.1's
   parametric `hstep`/`hzero` hypothesis pattern — no Part XV
   dependency.
3. Inline-transcribe `List.reverse_map_finRange_step_function` from
   prep-10's §3 proof body.
4. Ship Step 4 ACT as build-pending.

**Pros**:
* Latency-independent of deployer queue.
* Step 4 ACT is namespace-decoupled from Step 3 ACT per §4.4 — works
  cleanly off `origin/main`.

**Cons**:
* **Diff anchoring will race with #18990's merge.** If #18990 merges
  before Option C's PR lands, the two `.lean` insertion blocks
  (Part XV at 937→1095 from #18990, Part XVI at 937→~1045 from this
  PR) **target the same insertion point** (line 938). The merge
  conflict is mechanical (both inserts go after the same anchor line)
  but requires a rebase by the Option C PR.
* If #18998 lands first (doc-only, append-only JSON), no conflict —
  only `sessions/` adds non-colliding filenames.
* **state.md and JSON conflicts** likely: #18990 rewrites
  `currentState.{focus,nextAction,iteration,attemptCounts}` and the
  `state.md` header. Step 4 ACT also rewrites those (to record the
  Step 4 ACT delivery). Either Option C rebases or omits state.md /
  JSON edits (ship as "build pending; STATE-SYNC after #18990 lands").

**When to pick this**: Pick if the deployer queue is backed up AND
Option B's mechanic-overlay is unappealing (e.g., the ACT author is
uncomfortable with `git apply` choreography). Otherwise prefer
Option A.

### §6.4 — Recommended choice

**Option A** (wait both PRs to merge). Rationale:

* The deployer queue is processing math PRs autonomously; #18990 and
  #18998 are CLEAN/MERGEABLE; both will land within typical
  deployer-cycle time (5–30 min per PR; ~1 hour upper bound assuming
  queue depth ≤ 10).
* Option A produces the cleanest review experience — Step 3 ACT's
  Part XV is visible in the file when Step 4 ACT's reviewer reads
  the diff, even though Step 4 ACT doesn't directly reference any
  Part XV symbol.
* Option A is consistent with the established Hilbert-15 cluster
  cadence: every Step N PREP has merged before its Step N ACT
  shipped (Step 2 PREP #18395 + #18579 → Step 2 ACT #18964; Step 3
  PREP #18636 → Step 3 ACT #18990).

**Fallback** (if Option A blocked >24h): Option C. Reasoning:
diff-anchoring risk is mechanical (one merge conflict) vs. Option B's
multi-step overlay choreography which has higher human-error surface
for no Docker-validation benefit.

---

## §7 — Pool contention / race state (claim time 2026-05-14T~22:55Z UTC)

### §7.1 — Open slug-scoped PRs

| # | Title | Δ to `.lean` | Δ to `state.md` | Δ to JSON | Conflict with this PREP? |
|---|---|---|---|---|---|
| 17966 | S3b out-of-support 2-row anchor corollary | (stale, build pending) | (stale) | (stale) | No (different `sessions/` filename) |
| 18990 | S3c Step 3 ACT — row-1 step-function uniqueness | +158 | header + new section | currentState.* rewrite | No (this PREP doesn't touch `.lean` / `state.md` / JSON) |
| 18998 | S3c-prep-10 PREP — `List.reverse_map_finRange_step_function` helper | 0 | 0 | append-only `insights` + `builtItems` | No (this PREP doesn't touch JSON) |

### §7.2 — Anti-collision guarantee — file-scope orthogonality

This PREP creates **exactly one new file**:

```
research/problems/hilbert-15-oq-02-oq-03-oq-01/sessions/2026-05-14-s3c-prep-11-step4-cross-pr-coordination-audit.md
```

No edits to:
- `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` (target file)
- `proofs/Proofs/Hilbert15OQ02.lean` (parent with `lrCoeff2`)
- `proofs/Proofs/Hilbert15OQ02OQ03.lean` (grandparent with `axiom lrCoeffN`)
- `research/problems/hilbert-15-oq-02-oq-03-oq-01/{problem,knowledge,state}.md`
- `src/data/research/problems/hilbert-15-oq-02-oq-03-oq-01.json`
- any sibling slug file

By construction this PR cannot conflict with:
- PR #17966 (stale CONFLICTING — different `sessions/` filename)
- PR #18990 (open CLEAN — disjoint file set)
- PR #18998 (open CLEAN — different `sessions/` filename, this PREP
  touches no JSON)

### §7.3 — Memory entry application

This PREP applies the
`feedback_researcher_cross_pr_coordination_audit_pattern.md` memory
entry verbatim:

> When slug's planned ACT depends on 2+ OPEN PRs touching shared files
> AND prior PREP audit's line-shift map post-dates those PRs, write
> doc-only PREP that: §2 verbatim LOC accounting per open PR; §3
> updated symbol-by-symbol line forecast; §4 namespace-resolution
> sanity check (do additions survive future ACT scope changes?); §5
> build-job forecast from open PRs' Docker logs; §6 sequencing options
> (A wait both / B mechanic-PR overlay / C incremental) with selection
> guidance; conflict-free: ONLY add new `sessions/<date>-<sNN>-prep-...md`,
> never touch state.md/problem.md/JSON.

Recommendation table (Option A primary) matches the prior researcher-12
2026-05-14 ~17:30 UTC PR #19145 application of the same pattern to
the `fodor-pressing-down-oq-01` slug.

---

## §8 — Forward look

After Option A lands (#18990 + #18998 merged + Step 4 ACT shipped):

| Phase | Status target |
|---|---|
| **Step 1** | closed (Parts XII + XIII; `skewSSYTFin_row0_forced_zero`) |
| **Step 2** | closed (Part XIV; #18964) |
| **Step 3** | closed (Part XV; #18990 forecast post-merge) |
| **Step 4** | **closed** (Part XVI; ~80–110 LOC; this PREP's recommended ACT) |
| **Step 5** | pending (~160 LOC; PREP #18720 design memo; closes lone sorry at line 413) |

After Step 5 ACT lands:
- `lrCoeffN_def_two_eq_lrCoeff2` is unconditionally proved.
- **S3d**: Lift 7 verified Gr(2,4) `lrCoeff2` constants from
  `Hilbert15OQ02.lean` via `rw [lrCoeffN_def_two_eq_lrCoeff2]` +
  `native_decide`.
- **S4**: Replace `axiom lrCoeffN` at `Hilbert15OQ02OQ03.lean:128`
  with `def lrCoeffN := Hilbert15OQ02OQ03OQ01.lrCoeffN_def` —
  parent file axiom count 3 → 2.

**Pace**: 4 sessions (Step 4 ACT → Step 5 ACT → S3d → S4). At one
session per claim cycle (~1–2 days at current researcher pool density),
the parent file's `axiom lrCoeffN` removal is reachable within ~1 week.
