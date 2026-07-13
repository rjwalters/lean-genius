# S4 PREP — Parent-File Trim Audit (`Proofs/FodorPressingDown.lean`)

**Date**: 2026-05-12
**Agent**: researcher-5
**Mode**: PREP (doc-only)
**Slug**: `fodor-pressing-down-oq-01`
**Phase**: state.md "Migration plan" **S4 ACT** — trim
`proofs/Proofs/FodorPressingDown.lean` once S2 ACT (PR #18367) and
S3 ACT (PR #18412 PREP'd) have merged.

## 1. Why this memo (and why doc-only)

S1 OBSERVE (PR #18280, merged) and the slug's `state.md` lock a
four-phase migration plan:

* **S2 ACT** — ship `proofs/Proofs/Club/Basic.lean` with 5 defs +
  5 mechanical lemmas (~80 LOC). **PR #18367 in flight** (build pending).
* **S3 ACT** — verbatim-migrate `diagInter_isClosedBelow` from parent
  to new module. **PR #18412 PREP in flight** (doc-only, 336 LOC).
* **S4 ACT** — **THIS MEMO'S TARGET** — trim parent: remove the 4
  def-likes + 6 lemmas (5 from S2 + 1 from S3), add
  `import Proofs.Club.Basic`, update `meta.json`. Net delta ≈ −82 LOC.
* **S5 (optional)** — doc-only update to `fodor-pressing-down-oq-04`'s
  `problem.md` recording the new dependency path.

S4 ACT is the **first parent-touching step**. Until S4 lands, the
parent file is unchanged and PR #18367 / PR #18412 are strictly
additive. The risk surface for S4 is moderate: every theorem that
remains in the parent (the combinatorial heavyweights:
`diagInter_isUnboundedBelow`, `diagInter_isClubBelow`, `fodor`,
`fodor_aleph1`, `IsStationaryBelow.nonempty`,
`IsStationaryBelow.of_subset`) references the soon-to-be-migrated
names. After the trim, these references must resolve to the new
`Ordinal.*` namespace.

This memo pre-stages S4 by:
1. Exact line-range delete list (verified against current parent at
   `git rev-parse HEAD = 1c5999358ac`).
2. **Call-site resolution audit**: for every remaining reference to a
   migrated name, predict what it resolves to after the trim. **Flag
   one non-trivial gotcha** (dotted-method theorems
   `IsStationaryBelow.nonempty` / `IsStationaryBelow.of_subset`).
3. Meta.json delta (`lineCount`, `theoremCount`, `definitionCount`).
4. Import-line addition.
5. Verification script (one-liner) to confirm post-trim parent still
   resolves all symbols.
6. Anti-targets (what S4 ACT must NOT do).

**Doc-only deliverable**: one new file under `sessions/`. Zero Lean
source edits, zero gallery edits, zero `problem.md` / `state.md` /
`knowledge.md` edits. Conflict-free with PRs #18367 and #18412 (see §10).

## 2. Source state (verified at `git rev-parse HEAD = 1c5999358ac`)

* `proofs/Proofs/FodorPressingDown.lean` is **385 LOC**.
* It declares **4 def-likes** (3 `def` + 1 `structure`) and **12
  `theorem` declarations** (`grep -c "^def \|^structure \|^abbrev "` →
  4; `grep -c "^theorem "` → 12).
* `meta.json.leanFile`: `lineCount: 385, theoremCount: 12,
  definitionCount: 4, axiomCount: 0, sorries: 0`.
* `meta.json.meta.status: "verified"`.

## 3. Exact delete ranges

The parent's relevant ranges (1-indexed line numbers from the current
file content):

| Range | Content | Type | Migrating-to-Club/Basic via |
|---|---|---|---|
| **43–46** | Part I banner comment | comment | n/a (banner becomes meaningless) |
| **47–49** | `def IsUnboundedBelow` | def | S2 ACT (PR #18367) |
| **51–56** | `structure IsClubBelow` | structure | S2 ACT (PR #18367) |
| **58–60** | `def IsStationaryBelow` | def | S2 ACT (PR #18367) |
| **62–64** | `theorem IsClubBelow.mem_lt` | theorem | S2 ACT (PR #18367) |
| **66–68** | `theorem IsClubBelow.mem_of_isAcc` | theorem | S2 ACT (PR #18367) |
| **70–80** | `theorem isClubBelow_Iio_of_isSuccLimit` | theorem | S2 ACT (PR #18367) |
| **82–84** | Part II banner comment | comment | n/a |
| **86–88** | `def diagInter` | def | S2 ACT (PR #18367) |
| **90–92** | `@[simp] theorem mem_diagInter` | theorem | S2 ACT (PR #18367) |
| **94–96** | `theorem diagInter_subset_Iio` | theorem | S2 ACT (PR #18367) |
| **98–100** | Part III banner comment (lines `══` separator + title) | comment | n/a (banner-style only) |
| **102–124** | `theorem diagInter_isClosedBelow` (docstring + body) | theorem | S3 ACT (PR #18412 PREP) |

**Total deletion budget**: lines 43–124 = **82 lines removed** (matches
the state.md's "Net parent delta ≈ −150 LOC" upper-bound estimate from
S1 OBSERVE; the audit shows the true delta is closer to **−82 LOC**,
not −150).

**Note**: line 100 says `-- § Part III: Diagonal Intersection of Clubs
is a Club`. If S4 keeps the remaining `diagInter_isUnboundedBelow` and
`diagInter_isClubBelow` theorems, the banner can be **kept** (re-tag
to a Part-III-revised heading) or **removed** (if S4 chooses to leave
those two with no banner). Recommendation: keep but retitle (see §5).

**Note on `IsRegressive`**: S2 ACT adds `Ordinal.IsRegressive` to
Club/Basic.lean, but the parent file does NOT currently use a named
`IsRegressive` predicate — it inlines the predicate in `fodor`'s
hypothesis (`hf_reg : ∀ α ∈ S, f α < α`). So `IsRegressive` is a **net
addition** in S2, not a relocation. No parent-side delete needed.

## 4. Call-site resolution audit

The remaining parent theorems (lines 126–384) reference the migrated
names extensively. After the trim, these must resolve to
`Ordinal.*` (via the existing `open Ordinal` at line 41).

`grep -n "IsClubBelow\|IsUnboundedBelow\|IsStationaryBelow\|diagInter\|IsRegressive"` summary
across the remaining post-trim block (lines 126–384):

| Line | Reference | Post-trim resolution |
|---|---|---|
| 137 | `diagInter f κ.ord` (in docstring) | `Ordinal.diagInter` via `open Ordinal` |
| 138 | `theorem diagInter_isUnboundedBelow {f}` | declares `FodorPressingDown.diagInter_isUnboundedBelow` (kept in parent) |
| 140 | `IsClubBelow (f β) κ.ord` (hypothesis) | `Ordinal.IsClubBelow` via `open Ordinal` |
| 141 | `IsUnboundedBelow (diagInter f κ.ord) κ.ord` (conclusion) | both via `open Ordinal` |
| 148 | `(hf β hβ).unbounded δ hδ` | field projection: `Ordinal.IsClubBelow.unbounded` (structure field, accessed via dot syntax on a `hf β hβ : Ordinal.IsClubBelow ..` value — **resolves**) |
| 208 | `γ ∈ diagInter f κ.ord` | `Ordinal.diagInter` |
| 209 | `rw [mem_diagInter]` | `Ordinal.mem_diagInter` (because `IsAcc` etc. are also `Ordinal`-namespaced) — resolves via `open Ordinal`. **Note**: still `@[simp]` because S2's Club/Basic copy keeps the simp attribute. |
| 216 | `(hf β (lt_trans hβγ hγ_lt)).mem_of_isAcc hγ_lt` | dot-syntax `IsClubBelow.mem_of_isAcc` on a value of type `Ordinal.IsClubBelow` — resolves to `Ordinal.IsClubBelow.mem_of_isAcc`. |
| 240 | `theorem diagInter_isClubBelow` | declares `FodorPressingDown.diagInter_isClubBelow` (kept) |
| 242 | `IsClubBelow (f β) κ.ord` | `Ordinal.IsClubBelow` |
| 243 | `IsClubBelow (diagInter f κ.ord) κ.ord where` | `Ordinal.IsClubBelow` |
| 244 | `subset_Iio := diagInter_subset_Iio f κ.ord` | RHS: `Ordinal.diagInter_subset_Iio` via `open Ordinal` |
| 245 | `closed := diagInter_isClosedBelow hf` | RHS: `Ordinal.diagInter_isClosedBelow` (S3 ACT migration target) |
| 246 | `unbounded := diagInter_isUnboundedBelow hκ hκ_unc hf` | RHS: `FodorPressingDown.diagInter_isUnboundedBelow` (still in this file — same namespace, resolves) |
| 260 | `IsStationaryBelow S κ.ord` (hypothesis) | `Ordinal.IsStationaryBelow` |
| 265 | `IsStationaryBelow (S ∩ ...) κ.ord` (conclusion) | `Ordinal.IsStationaryBelow` |
| 270 | `IsClubBelow C κ.ord` (in hypothesis) | `Ordinal.IsClubBelow` |
| 272 | `¬IsStationaryBelow ...` | `Ordinal.IsStationaryBelow` |
| 273 | `rw [IsStationaryBelow, ...]` | **GOTCHA #1**: this is a `rw` on a `def`-name. Now that `IsStationaryBelow` is `Ordinal.IsStationaryBelow`, the `rw` becomes `rw [Ordinal.IsStationaryBelow, ...]`. With `open Ordinal`, the bare name should still resolve, but `rw` resolves via name-discovery and may show `unknown identifier 'IsStationaryBelow'` if `open Ordinal` doesn't lift def-names for `rw`. **VERIFY** with `rw [Ordinal.IsStationaryBelow, ...]` explicit form as a fallback. |
| 280 | `IsClubBelow (pickC c hc) κ.ord` | `Ordinal.IsClubBelow` |
| 288 | `IsClubBelow (F β) κ.ord` | `Ordinal.IsClubBelow` |
| 293 | `IsClubBelow (diagInter F κ.ord) κ.ord` | `Ordinal.*` |
| 294 | `diagInter_isClubBelow hκ hκ_unc hF_club` | `FodorPressingDown.diagInter_isClubBelow` (same namespace, still here) |
| 296 | `hS (diagInter F κ.ord) hD_club` | `Ordinal.diagInter` |
| 297 | `rw [mem_diagInter] at hγD` | **same as line 209** — `Ordinal.mem_diagInter` via `open Ordinal` |
| 321 | `IsStationaryBelow S (ℵ₁).ord` | `Ordinal.IsStationaryBelow` |
| 326 | `IsStationaryBelow (S ∩ ...) (ℵ₁).ord` | `Ordinal.IsStationaryBelow` |
| 334 | `theorem IsStationaryBelow.nonempty` | **GOTCHA #2 (load-bearing)** — see §4.1 below |
| 335 | `(hS : IsStationaryBelow S o)` | `Ordinal.IsStationaryBelow` |
| 336 | `IsClubBelow (Iio o) o := isClubBelow_Iio_of_isSuccLimit ho` | `Ordinal.IsClubBelow`, `Ordinal.isClubBelow_Iio_of_isSuccLimit` |
| 343 | `theorem IsStationaryBelow.of_subset` | **GOTCHA #2 (load-bearing)** |
| 344–346 | hypothesis types | `Ordinal.*` |

### 4.1 Gotcha #2 (load-bearing): dotted-method theorems

Lines 334 and 343 declare:

```lean
theorem IsStationaryBelow.nonempty ...
theorem IsStationaryBelow.of_subset ...
```

In Lean 4, dot notation `hS.nonempty` resolves by inspecting the type
of `hS`. After the trim:

* `hS : IsStationaryBelow S o` has type `Ordinal.IsStationaryBelow S o`
  (resolved via `open Ordinal` at line 41).
* Dot notation `hS.nonempty` looks up
  `Ordinal.IsStationaryBelow.nonempty`, **NOT**
  `FodorPressingDown.IsStationaryBelow.nonempty`.

But the theorems at lines 334 and 343 are declared *inside*
`namespace FodorPressingDown` (line 39), so they are
**`FodorPressingDown.IsStationaryBelow.nonempty`** and
**`FodorPressingDown.IsStationaryBelow.of_subset`**.

After the trim, calling them via dot notation **WILL FAIL TO RESOLVE**.

**Three mitigation routes for S4 ACT** (pick one):

* **Route A (recommended — clean)**: Move both theorems into
  `Proofs/Club/Basic.lean` under `namespace Ordinal`. Net delta:
  −15 LOC parent, +15 LOC Club/Basic. Theorems live where their
  type-name lives.

* **Route B (in-parent fixup)**: Keep both in the parent but
  re-declare them under `namespace Ordinal` inside the
  `namespace FodorPressingDown` scope:

  ```lean
  namespace FodorPressingDown
  open Cardinal Order Ordinal Set
  -- ... (after the trim block) ...
  namespace _root_.Ordinal
  theorem IsStationaryBelow.nonempty ... := ...
  theorem IsStationaryBelow.of_subset ... := ...
  end _root_.Ordinal
  ```

  Slightly awkward; works because nested `_root_.Ordinal` declares
  under the `Ordinal` namespace despite being inside
  `FodorPressingDown`.

* **Route C (verbose-but-safe)**: Keep both inside
  `FodorPressingDown` but rename to e.g.
  `FodorPressingDown.isStationaryBelow_nonempty` (snake_case,
  no dot notation), and update the docstring banner. Loses the
  dot-notation ergonomics but preserves the namespace separation.

**Recommendation**: **Route A**. The two theorems are general-purpose
facts about `IsStationaryBelow` that belong in `Club/Basic.lean`
alongside the definition. Routes B and C are workarounds.

### 4.2 Gotcha #1: `rw [IsStationaryBelow, ...]` (line 273)

`rw` uses Lean's name-elaboration, which honours `open Ordinal`. In
practice, `rw [IsStationaryBelow, ...]` should resolve to
`rw [Ordinal.IsStationaryBelow, ...]`. However, this can be fragile
if there is any context-shadowing.

**Mitigation**: S4 ACT should test the post-trim build; if line 273
fails, rewrite explicitly to `rw [Ordinal.IsStationaryBelow, ...]` (or
delete the `rw` and use `show ¬ ∀ C, ... → ...` directly).

**Conservative recommendation**: pre-emptively rewrite line 273 to
`rw [Ordinal.IsStationaryBelow, not_forall] at hnot` to remove the
ambiguity. +0 LOC delta.

## 5. Header / docstring updates

The parent's top-of-file docstring (lines 1–37) explicitly references
the soon-to-be-migrated names:

```text
**Infrastructure Built Here** (not in Mathlib as of 2026-04):
- `IsUnboundedBelow`, `IsClubBelow`, `IsStationaryBelow`
- `diagInter`: diagonal intersection
- `diagInter_isClosedBelow`: closed part of diagonal intersection lemma
- `diagInter_isUnboundedBelow`: unbounded part via zipper construction
- `fodor`: Fodor's pressing-down lemma (0 sorries)
```

After S4 ACT:

* `IsUnboundedBelow`, `IsClubBelow`, `IsStationaryBelow`, `diagInter`,
  `diagInter_isClosedBelow` → now in `Proofs/Club/Basic.lean`.
* `diagInter_isUnboundedBelow`, `diagInter_isClubBelow`, `fodor`,
  `fodor_aleph1` remain here (the combinatorial heavyweights, with
  the zipper construction).

**Suggested S4 ACT docstring rewrite** (replace lines 14–23):

```text
**Infrastructure built here** (composes with `Proofs/Club/Basic.lean`):
- `diagInter_isUnboundedBelow`: zipper construction giving the unbounded
  half of the diagonal-intersection-is-club result (`Cardinal.{0}`-pinned).
- `diagInter_isClubBelow`: the diagonal-intersection-is-club result, by
  combining `Ordinal.diagInter_isClosedBelow` (Club/Basic.lean) with
  the unbounded half above.
- `fodor`: Fodor's pressing-down lemma (0 sorries, regular uncountable κ).
- `fodor_aleph1`: specialization to `ω₁` for the parent slug consumer.
- `IsStationaryBelow.nonempty` / `.of_subset`: utility lemmas for
  stationary sets (note: these may be moved to Club/Basic.lean per
  S4 PREP §4.1 Route A).

**Library API**: `Proofs/Club/Basic.lean` provides the definitions
`Ordinal.IsClubBelow`, `Ordinal.IsStationaryBelow`, `Ordinal.diagInter`
plus the elementary lemmas `mem_lt`, `mem_of_isAcc`,
`isClubBelow_Iio_of_isSuccLimit`, `mem_diagInter`, `diagInter_subset_Iio`,
`diagInter_isClosedBelow`. See PR #18280 (S1 OBSERVE) for the
migration plan.
```

This is a ~16-line block (replaces ~10 lines). Net +6 LOC in the
header, partially offsetting the −82 LOC removed by the trim.

The bottom-of-file summary docstring (lines 366–384) similarly
references migrated names. Suggested rewrite: shorter, cross-references
Club/Basic.lean.

## 6. Import-line addition

S4 ACT adds **one** import line, somewhere between line 28
(`import Mathlib.SetTheory.Cardinal.Ordinal`) and line 38 (blank
before `namespace FodorPressingDown`):

```lean
import Proofs.Club.Basic
```

**Placement**: alphabetically would put it after the Mathlib block,
just before the blank line at line 38. Concretely:

```text
Line 28: import Mathlib.SetTheory.Cardinal.Ordinal
Line 29: import Mathlib.SetTheory.Cardinal.Cofinality
Line 30: import Mathlib.SetTheory.Cardinal.Regular
Line 31: import Mathlib.SetTheory.Ordinal.Arithmetic
Line 32: import Mathlib.SetTheory.Ordinal.Topology
Line 33: import Mathlib.Tactic
Line 34: <NEW> import Proofs.Club.Basic
Line 35: (blank)
Line 36: namespace FodorPressingDown
```

**Sanity check**: PR #18367 already adds `import Proofs.Club.Basic`
to `proofs/Proofs.lean` (the project manifest), so the module path
exists. The parent's new import just exposes the API for in-file use.

**`meta.json.leanFile.imports` update**: the imports array currently
has 6 entries (Mathlib only); after S4 add one entry to make it 7.

## 7. Meta.json delta

`src/data/proofs/fodor-pressing-down/meta.json` updates:

| Key | Before | After | Δ |
|---|---|---|---|
| `meta.lineCount` (top-level) | 385 | ~303 (target ±5) | −82 ± 5 |
| `meta.theoremCount` | 12 | 6 | −6 |
| `meta.definitionCount` | 4 | 0 | −4 |
| `leanFile.lineCount` | 385 | ~303 | −82 |
| `leanFile.theoremCount` | 12 | 6 | −6 |
| `leanFile.definitionCount` | 4 | 0 | −4 |
| `leanFile.imports` | 6 entries | 7 entries (+`Proofs.Club.Basic`) | +1 |
| `leanFile.axiomCount` | 0 | 0 | 0 |
| `leanFile.sorries` | 0 | 0 | 0 |
| `meta.status` | `"verified"` | `"verified"` (post-build) | 0 |

**`+/− 5` line tolerance**: depends on whether the Part-III banner is
kept (S4's choice) and whether the header docstring is rewritten per
§5. The mechanic auditor pass after S4 can re-compute exact counts.

**Banner / boundary effects**:
* If S4 keeps the Part-I/II/III banners (3 banner blocks at lines
  43–46, 82–84, 98–100) but Part-I and Part-II have nothing left under
  them, S4 SHOULD remove them. Including the banners: 3 × ~3 lines =
  ~9 lines additional deletion.
* If S4 rewrites the header docstring per §5: +~6 LOC in the header.
* Net: ~−82 ± 9 LOC, settling near 303 lines.

**If Route A from §4.1 is taken** (moving `IsStationaryBelow.nonempty`
and `IsStationaryBelow.of_subset` to Club/Basic.lean):

| Key | Before | After Route A | Δ |
|---|---|---|---|
| `leanFile.theoremCount` (parent) | 12 | 4 | −8 |
| `leanFile.lineCount` (parent) | 385 | ~286 | −99 |

Club/Basic.lean theorem count increases by 2.

## 8. Verification script (post-S4 build)

After S4 ACT lands, the implementer should run:

```bash
# 1. Parent compiles cleanly (no `unknown identifier 'IsClubBelow'` etc.).
./proofs/scripts/docker-build.sh Proofs.FodorPressingDown

# 2. Symbol-resolution sanity check (one-line awk over Lean log).
grep -E "(unknown identifier|unresolved identifier|invalid field)" \
  .loom/logs/researcher-N-fodor-s4-build.log
# (should produce zero output)

# 3. meta.json consistency: theoremCount matches actual count.
LF=$(grep -c "^theorem " proofs/Proofs/FodorPressingDown.lean)
DF=$(grep -c "^def \|^structure \|^abbrev " proofs/Proofs/FodorPressingDown.lean)
TC=$(jq -r '.leanFile.theoremCount' src/data/proofs/fodor-pressing-down/meta.json)
DC=$(jq -r '.leanFile.definitionCount' src/data/proofs/fodor-pressing-down/meta.json)
[[ "$LF" == "$TC" ]] && echo "theoremCount OK" || echo "DRIFT: theorem $LF vs meta $TC"
[[ "$DF" == "$DC" ]] && echo "definitionCount OK" || echo "DRIFT: def $DF vs meta $DC"
```

This script catches the most common S4 ACT failure modes:
* `unknown identifier` if `open Ordinal` doesn't propagate (Gotcha #1).
* `invalid field 'nonempty' / 'of_subset'` (Gotcha #2 if Routes B/C
  not applied correctly).
* meta.json drift (the auditor will catch this later, but flagging
  in-PR is cleaner).

## 9. Anti-targets (what S4 ACT must NOT do)

9.1 **Do NOT modify any theorem signature**. Body changes via
    namespace re-qualification are fine (e.g. `IsClubBelow` →
    `Ordinal.IsClubBelow` if the explicit rewrite from §4.2 is taken),
    but **statement-level types** (hypotheses, conclusions) must
    remain bitwise-identical modulo the namespace prefix.

9.2 **Do NOT touch `Proofs/Club/Basic.lean`** (S2 ACT's domain;
    PR #18367 owns it). Bundle any Club/Basic additions only as part
    of Route A from §4.1, and only if Route A is taken (Routes B/C
    keep parent edits self-contained).

9.3 **Do NOT change `meta.json.meta.status`**. Stays `"verified"`
    once build passes; the badge stays `"original"`.

9.4 **Do NOT split S4 into multiple commits/PRs**. The trim is
    atomic: removing lines 43–124 leaves the file *temporarily*
    broken (`IsClubBelow` etc. are unbound until `import
    Proofs.Club.Basic` is added). Both edits land together.

9.5 **Do NOT add deprecation aliases** like
    `notation "IsClubBelow" => Ordinal.IsClubBelow` in the parent.
    The parent's `open Ordinal` (line 41) already handles every
    remaining call site (verified in §4). Aliases would clutter.

9.6 **Do NOT extend or rewrite the `fodor` proof body** during S4.
    S4 is a pure trim — proof bodies of remaining theorems
    (`fodor`, `diagInter_isUnboundedBelow`, etc.) are
    bitwise-untouched modulo namespace resolution.

9.7 **Do NOT touch `src/data/proofs/fodor-pressing-down/annotations.json`**.
    Annotations may reference line numbers; they'll need a separate
    re-anchor pass *after* S4 lands (auditor / mechanic territory).

9.8 **Do NOT extend `problem.md` / `state.md` / `knowledge.md`
    from this branch (S4 PREP)**. S4 ACT will own that update —
    specifically a `state.md` "Migration plan" status update from
    "S4 ACT pending" to "S4 ACT in flight" / "S4 ACT landed".

9.9 **Do NOT run the docker build from this PREP branch.** S4 PREP
    is doc-only; no Lean compilation needed. Build verification is
    S4 ACT's responsibility.

## 10. Conflict-free guarantee

This PR adds **one file at a fresh path**:

```
research/problems/fodor-pressing-down-oq-01/sessions/2026-05-12-s04-prep-parent-trim-audit.md
```

PR #18367 (S2 ACT) edits:
* `proofs/Proofs.lean` (manifest)
* `proofs/Proofs/Club/Basic.lean` (new file, owned by S2)
* `research/problems/fodor-pressing-down-oq-01/sessions/2026-05-12-s02-act-club-basic.md`

PR #18412 (S3 PREP) edits:
* `research/problems/fodor-pressing-down-oq-01/sessions/2026-05-12-s03-prep-diagInter-isClosedBelow-migration.md`

Three different sessions/-filenames, three disjoint surfaces.
git auto-merges the `sessions/` directory creation; no conflict.

Files NOT touched by **this** PR:
* `proofs/**` (all Lean source — S4 ACT's job)
* `src/data/proofs/fodor-pressing-down/**` (gallery — S4 ACT's job)
* `src/data/research/problems/fodor-pressing-down-oq-01.json`
* `research/problems/fodor-pressing-down-oq-01/{problem,knowledge,state}.md`
* Any sibling slug (`fodor-pressing-down-oq-04`, `cantor-diagonalization-oq-02-oq-03`)

## 11. Cheat-sheet for S4 ACT implementer

Once S2 ACT (PR #18367) and S3 ACT (the implementation, post-PREP
#18412) have both merged:

1. **Verify dependencies merged**:
   ```bash
   git log origin/main --oneline | head -20 | grep -E "fodor.*S2|fodor.*S3"
   # Expect two lines: S2 ACT + S3 ACT
   ```

2. **Open** `proofs/Proofs/FodorPressingDown.lean`.

3. **Decide on Route A vs B vs C from §4.1** for
   `IsStationaryBelow.nonempty` / `IsStationaryBelow.of_subset`.
   **Recommended: Route A** (move both to `Club/Basic.lean`).

4. **Delete** lines 43–124 (= 82 lines, the entire Parts I–II and the
   `diagInter_isClosedBelow` theorem from Part III). Keep the Part-III
   banner only if its remaining content (`diagInter_isUnboundedBelow`,
   `diagInter_isClubBelow`) warrants it; otherwise remove the banner
   too (lines 98–100).

5. **Insert** `import Proofs.Club.Basic` after line 33 (after the
   Mathlib imports, before the blank line and `namespace
   FodorPressingDown` declaration).

6. **Pre-emptive fix for Gotcha #1**: replace line 273 from
   `rw [IsStationaryBelow, not_forall] at hnot`
   to `rw [Ordinal.IsStationaryBelow, not_forall] at hnot`.

7. **If Route A from §4.1**: cut lines 334–349 (the two
   `IsStationaryBelow.*` theorems) and paste them into
   `Proofs/Club/Basic.lean` under `namespace Ordinal`.

8. **Rewrite** the file's header docstring per §5 (replaces lines
   14–23 with the suggested block). Optional but recommended.

9. **Update** `src/data/proofs/fodor-pressing-down/meta.json` per
   §7: `lineCount`, `theoremCount`, `definitionCount` (and
   `leanFile.imports`).

10. **Build**: `./proofs/scripts/docker-build.sh Proofs.FodorPressingDown`
    (~25–45 min Docker cold). Build-pending PRs land per convention.

11. **Run §8 verification script**, attach output to PR body.

12. **PR title pattern**: `research(fodor-pressing-down-oq-01): S4 ACT —
    trim parent (5 defs + 6 lemmas moved to Club/Basic.lean, build
    pending)`. Add label `research`.

## 12. Honesty assessment

* **Mathematical content of S4 ACT**: zero new mathematics. Pure
  library refactor — code that used to live in `FodorPressingDown.lean`
  now lives in `Club/Basic.lean`.
* **Significance**: medium. The refactor enables sibling slugs
  (`fodor-pressing-down-oq-04` Solovay splitting) to consume the
  club/stationary API without depending on the Fodor parent — clean
  module boundaries.
* **Originality**: zero. Standard library-extraction refactor every
  textbook-formalization project does after the first proof lands.
* **What this memo claims**: it locks the parent-side trim audit so
  the S4 ACT implementer doesn't re-derive call-site resolution from
  scratch, and flags the **dotted-method gotcha (§4.1, Gotcha #2)**
  that the S1 OBSERVE migration plan did NOT call out. That gotcha is
  the single load-bearing finding of this memo.

**Memo's value-add over S1 OBSERVE**:
* §4.1 Gotcha #2 (dotted-method theorems) is **not** mentioned in S1
  OBSERVE PR #18280's migration plan or in `knowledge.md`. Without
  this audit, S4 ACT would hit a `field 'nonempty' / 'of_subset'
  not found` error at build time and have to retry. Pre-emptive Route
  A recommendation saves one build-retry cycle (~30–45 min Docker).
* §4.2 Gotcha #1 (`rw [IsStationaryBelow, ...]` at line 273) is also
  not flagged in S1 OBSERVE — a pre-emptive 1-character fix is safer
  than gambling on `open Ordinal` resolving inside `rw`.

## Appendix A: Verification commands used in this memo

```bash
# Confirm current parent file state at the commit this memo was authored:
git rev-parse HEAD
# 1c5999358acd78afd76cb832c59be68a3fd561c2

# Count current declarations:
grep -c "^def \|^structure \|^abbrev " proofs/Proofs/FodorPressingDown.lean  # → 4
grep -c "^theorem " proofs/Proofs/FodorPressingDown.lean                      # → 12

# Confirm `IsRegressive` is NOT in parent (only inline):
grep -c "IsRegressive\|hf_reg" proofs/Proofs/FodorPressingDown.lean           # → 4 (hf_reg only; no named def)

# Confirm parent's `open` line:
grep "^open " proofs/Proofs/FodorPressingDown.lean                            # → "open Cardinal Order Ordinal Set"

# Confirm S2 ACT PR #18367 file contents include the 5 defs + 5 lemmas:
gh api repos/rjwalters/lean-genius/pulls/18367/files --jq '.[] | select(.filename == "proofs/Proofs/Club/Basic.lean") | .patch' | grep -c "^+def \|^+structure "  # → 4 (matches parent's 4 to-remove)
```

## Appendix B: Estimated S4 ACT effort

* **Code edits**: ~85 line deletions + 1 line insertion + ~6 lines
  docstring update + optional Route-A move (~15 LOC). Net: −82 LOC
  parent, +0 or +15 LOC Club/Basic depending on Route.
* **Meta.json edits**: ~6 numeric fields.
* **Build**: 25–45 min Docker cold.
* **Total wall-clock**: 60–90 min including PR creation, build,
  and meta-drift verification.

This is a **fast-track ACT** because the audit removes guesswork. The
S1 OBSERVE state.md estimated "Net parent delta ≈ −150 LOC" without
a line-by-line audit; the actual delta is **−82 LOC** (−99 LOC if
Route A is taken). The estimate was a 2× overshoot due to under-counting
banner-comment removals and not having tabulated the actual decl widths.
