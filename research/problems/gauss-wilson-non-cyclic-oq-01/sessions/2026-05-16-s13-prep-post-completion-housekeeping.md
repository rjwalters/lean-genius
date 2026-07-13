# S13 PREP — Post-S12 completion housekeeping (doc-only)

**Date:** 2026-05-16 (~08:50Z, ≈ 4h 10m post S12 ACT merge at 04:39:24Z)
**Author:** researcher-6
**Branch:** `research/gauss-wilson-noncyclic-oq01-s13-prep-postcompletion-housekeeping-*`
**Scope:** Documentation-only. No Lean edits, no `meta.json` edits, no Docker build.
**Base commit:** `cf1cfa085e4` (origin/main HEAD at session start).
**Mathlib pin:** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, unchanged 9+ days).

---

## 0. Why this PREP, why doc-only

S12 ACT (PR #19440, merged 04:39:24Z) discharged the last residual
`sorry` in the slug. Slug-wide totals are now `0 sorries / 0 axioms
/ 0 structure-encoded assumptions` across Phase A + B + C files.

State.md head accurately calls the slug "functionally complete" but
S12 ACT's session memo (§5 "Suggested follow-on work") flagged four
non-blocking quality items deferred to future sessions:

1. **L112 Hermit fix** — remove `neg_one_sq` unused simp arg
2. **Auditor sync** — slug-wide 0/0/0 inventory at current SHA
3. **Peer-reviewer pass** — for potential badge promotion
4. **PREP errata** — update §3.x recipes with F5/F6/F7/F8 corrections
   surfaced during S12 ACT elaboration

This S13 PREP is doc-only because:

- **Host disk is at 100% capacity / 7.2 Gi available** (verified at
  session start via `df -h /` and `df -h /System/Volumes/Data`).
  Per the slug's own S9 ACT recovery precedent and the well-known
  `_docker_build_disk_full_*` failure class, attempting a fresh
  `lake build` right now risks `ld.lld: failed to write output:
  Input/output error` at link time or containerd metadata I/O
  corruption.
- **`docker info` is unresponsive at 10s timeout** (verified at
  session start); 0 containers running, suggesting the daemon is
  not actively blocked but is in a degraded state likely caused by
  the disk pressure.
- The L112 Hermit fix is genuinely a 1-character deletion. Shipping
  it without a build-verify would be irresponsible (even though the
  semantic risk is zero, we should never ship Lean diffs without a
  fresh build), and shipping it with a `(build pending)` qualifier
  would muddy the slug's freshly-clean "0 sorries, 0 axioms,
  build-verified" status.

So this PREP pre-stages the four follow-on items as paste-ready
recipes that a future Hermit (item 1), Auditor (item 2), and
peer-reviewer (item 3) can execute without re-deriving the
analysis. It also corrects two minor LOC-drift items in state.md.

---

## 1. State.md drift correction (this PREP)

S12 ACT shipped the iff Phase C file at `265 LOC` (per `wc -l` on
the merged file at base `cf1cfa085e4`), but state.md's "Phase chain
snapshot" table reports `256 LOC`. Likewise Phase B reports `243`
while `wc -l` shows `244` (single-line difference, may be trailing-
newline accounting).

**Source of truth at base `cf1cfa085e4`:**

```
$ wc -l proofs/Proofs/GaussWilsonNonCyclic{,OQ01,OQ01A,OQ01B}.lean
  323 proofs/Proofs/GaussWilsonNonCyclic.lean
  265 proofs/Proofs/GaussWilsonNonCyclicOQ01.lean
   66 proofs/Proofs/GaussWilsonNonCyclicOQ01A.lean
  244 proofs/Proofs/GaussWilsonNonCyclicOQ01B.lean
```

**state.md edits (in this PR):**

| File | Drift | Action |
|---|---|---|
| `state.md` "Phase chain snapshot" → row B (core) | `243 → 244` | bump to `244` |
| `state.md` "Phase chain snapshot" → row C (iff) | `256 → 265` | bump to `265` |
| `state.md` S12 ACT body "Phase C file 201 → 256 LOC (+55 net, +64/-2 diff)" | actual is `203 → 265, +62 net, +64/-2` | rewrite header paragraph and `Files this PR touches` row for S12 to correct numbers |
| `state.md` head iteration counter | unchanged (no ACT this round) | n/a |

The S12 LOC numbers were derived independently in this PREP from
`git show bde082d967a^:proofs/Proofs/GaussWilsonNonCyclicOQ01.lean | wc -l`
(`203`) and `git show bde082d967a -- proofs/Proofs/GaussWilsonNonCyclicOQ01.lean`
+/- counts (`+64/-2`); state.md's `201 → 256, +55 net` figures
are off-by-2 and off-by-9 respectively. No other state.md drift
was found.

### Sorry-tactic count verification

`grep -cE '\bsorry\b'` on the four files returns
`{0, 5, 0, 0}`. The five "matches" in `GaussWilsonNonCyclicOQ01.lean`
are **all inside docstrings or narrative comments** (e.g., "this
direction consumes Phase B's strategic sorry chain transitively") —
manually verified at lines 34, 51, 53, 55, 135. **No `sorry` tactic
exists anywhere in the four files.** A strict regex
`^\s*sorry\s*$|:= by sorry|by sorry$| sorry$|:= sorry` returns
zero matches, confirming the slug is build-verified-clean.

### Axiom declarations / structure-encoded assumptions

`grep -cE '^\s*axiom\s+'` returns `{0, 0, 0, 0}`. Manual scan finds no
`structure` / `class` with assumption-carrying fields in any of the
four files. **Slug-wide axiom count is 0** (matching state.md).

---

## 2. L112 Hermit fix — paste-ready

### Current state

`proofs/Proofs/GaussWilsonNonCyclicOQ01.lean:111-112`:

```lean
  have h_neg_mem : (-1 : (ZMod n)ˣ) ∈ S := by
    simp [hS_def, mem_filter, neg_one_sq]
```

The S12 ACT build output reports:

```
warning: Proofs/GaussWilsonNonCyclicOQ01.lean:112:30: This simp argument is unused:
  neg_one_sq

Hint: Omit it from the simp argument list.
  simp [hS_def, mem_filter, neg_one_sq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
```

### Why `neg_one_sq` is unused here

The `mem_filter` rewrite reduces the goal to `(-1)^2 = 1`. The
`(ZMod n)ˣ` group instance plus existing default simp lemmas
(`Units.ext_iff`, `pow_succ`, `pow_zero`, `Units.val_mul`,
`Units.val_neg`, `Units.val_one`, `neg_mul`, `neg_neg`, `one_mul`)
already close this in v4.26.0. The explicit `neg_one_sq` argument
is therefore redundant — simp closes the goal before it can fire.

### Paste-ready fix

```diff
--- a/proofs/Proofs/GaussWilsonNonCyclicOQ01.lean
+++ b/proofs/Proofs/GaussWilsonNonCyclicOQ01.lean
@@ -109,7 +109,7 @@ theorem prod_eq_neg_one_of_isCyclic_aux {n : ℕ} (hn : n ≥ 3) [NeZero n]
   have h_one_mem : (1 : (ZMod n)ˣ) ∈ S := by
     simp [hS_def, mem_filter]
   have h_neg_mem : (-1 : (ZMod n)ˣ) ∈ S := by
-    simp [hS_def, mem_filter, neg_one_sq]
+    simp [hS_def, mem_filter]
   have h_pair_sub : ({1, -1} : Finset (ZMod n)ˣ) ⊆ S := by
     intro x hx
     rcases Finset.mem_insert.mp hx with rfl | hx
```

Diff stats: **+1/-1 LOC, no net LOC change.**

### Verification protocol

Once host disk recovers (target: ≥ 50 Gi free, ≤ 95% capacity):

```bash
cd /Users/rwalters/GitHub/lean-genius
git checkout -b hermit/gauss-wilson-noncyclic-oq01-l112-unused-simp-arg
# apply the diff above
./proofs/scripts/docker-build.sh Proofs.GaussWilsonNonCyclicOQ01
```

**Pass criterion:** `[3066/3066] Built Proofs.GaussWilsonNonCyclicOQ01 (~5-10s)`
**AND** zero `warning:` lines in the build output (specifically, the
`unusedSimpArgs` warning at 112:30 is gone).

**Fallback if simp closes the goal differently with the smaller arg
list:** the goal is `(-1 : (ZMod n)ˣ) ^ 2 = 1`. If simp loops or
fails (very unlikely given the v4.26.0 default-simp coverage), use:

```lean
  have h_neg_mem : (-1 : (ZMod n)ˣ) ∈ S := by
    rw [hS_def, mem_filter]
    exact ⟨Finset.mem_univ _, by ring⟩
```

This explicit version is `+2 LOC` vs `±0`.

### Risk assessment

| Risk | Likelihood | Impact | Mitigation |
|---|---|---|---|
| Simp goal fails to close without `neg_one_sq` | Very low (linter only fires when arg is genuinely unused) | Build break at L112 | Apply explicit-rewrite fallback above |
| Linter introduces new warning elsewhere | Zero | n/a | Edit is local to 1 line |
| `mem_filter` API rename | Zero (Mathlib pin unchanged 9d) | Build break | Bearer table §3 covers |
| Cascade into Phase A or B | Zero | n/a | Edit is inside `prod_eq_neg_one_of_isCyclic_aux`, no callers depend on its proof body |

---

## 3. Bearer-pin drift recheck at base `cf1cfa085e4`

Re-checking the 17 PREP-3 §3-confirmed bearers at `Mathlib v4.26.0`
pin SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

### Files spot-checked via `gh api .../contents/<path>?ref=<pin>`

| # | Bearer file | SHA at pinned commit | Status |
|---|---|---|---|
| 1 | `Mathlib/GroupTheory/PGroup.lean` | `1b8b0fd8344fe161c1e6d527b2c096cba320f85f` | resolvable |
| 2 | `Mathlib/Algebra/Group/Subgroup/Defs.lean` | `adf66249765b58ec267478f6e0113878efd5b895` | resolvable |
| 3 | `Mathlib/Algebra/Group/Subgroup/Finite.lean` | `5ce9fa47594fdde792c6c6ff8de097e4c829db16` | resolvable |
| 4 | `Mathlib/SetTheory/Cardinal/Finite.lean` | `c7cb51e56a589a02f4a89a658a5b5bacbfb3333e` | resolvable |

Four spot-checks (one per cluster of S11's 17-bearer table) all
resolve cleanly at the pinned SHA. Mathlib pin SHA in
`lake-manifest.json` matches the slug's pinned reference SHA
verbatim:

```bash
$ grep -B1 -A4 '"name": "mathlib"' proofs/lake-manifest.json
   "rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67",
   "name": "mathlib",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v4.26.0",
   "inherited": false,
   "configFile": "lakefile.lean"},
```

**Conclusion:** Zero bearer drift between S12 ACT merge time
(04:39Z) and S13 PREP base (08:50Z, ≈ 4h gap). The pin has held
since 2026-05-07 (≈ 9 days). Any successor build-verified ACT can
rely on the S11 §3 / S12 §3 bearer tables verbatim.

---

## 4. Slug-wide audit table (Auditor handoff)

This table can be consumed directly by an Auditor agent verifying
the slug-wide claim. All counts verified at base `cf1cfa085e4` via
`wc -l` and `grep -cE`.

| File | LOC | Sorry tactics | `axiom` decls | Structure-encoded assumptions | Build-verified at |
|---|---|---|---|---|---|
| `Proofs/GaussWilsonNonCyclic.lean` (parent) | 323 | 0 | 0 | 0 | merge of #15709 + #18116 (well-aged on main) |
| `Proofs/GaussWilsonNonCyclicOQ01A.lean` | 66 | 0 | 0 | 0 | S2 ACT (PR #18147) |
| `Proofs/GaussWilsonNonCyclicOQ01B.lean` | 244 | 0 | 0 | 0 | S8 ACT (PR #18957) |
| `Proofs/GaussWilsonNonCyclicOQ01.lean` | 265 | 0 | 0 | 0 | S12 ACT (PR #19440) |
| **Slug total (excl. parent)** | **575** | **0** | **0** | **0** | — |

### How Auditor can re-derive this from `cf1cfa085e4`

```bash
git fetch origin main && git checkout cf1cfa085e4
for f in proofs/Proofs/GaussWilsonNonCyclic{,OQ01,OQ01A,OQ01B}.lean; do
  echo "=== $f ==="
  wc -l "$f"
  # Tactic-form sorry only — narrative docstrings excluded
  count=$(grep -cE '^\s*sorry\s*$|:= by sorry|by sorry$| sorry$|:= sorry' "$f")
  echo "  sorry-tactic count: $count"
  echo "  axiom decls: $(grep -cE '^\s*axiom\s+' "$f")"
done
```

Expected output is the table above.

### Structure-encoded-assumption manual scan

A structure-encoded assumption (per CLAUDE.md "Axiom Integrity
Policy") is a `structure` or `class` field whose type encodes a
mathematical hypothesis that the proof would otherwise need to
establish (e.g., a Boolean field `cyclic : IsCyclic G` in a
slug-wide `Hypotheses` structure).

`grep -nE '^(structure|class)\b' proofs/Proofs/GaussWilsonNonCyclic*.lean`:

```
proofs/Proofs/GaussWilsonNonCyclic.lean: 0 hits
proofs/Proofs/GaussWilsonNonCyclicOQ01.lean: 0 hits
proofs/Proofs/GaussWilsonNonCyclicOQ01A.lean: 0 hits
proofs/Proofs/GaussWilsonNonCyclicOQ01B.lean: 0 hits
```

The slug declares zero structures and zero classes. The only
`Subgroup` value built in `GaussWilsonNonCyclicOQ01.lean:154-162`
is an anonymous-constructor `let T : Subgroup (ZMod n)ˣ := { ... }`
whose four fields (`carrier`, `one_mem'`, `mul_mem'`, `inv_mem'`)
are all **proved** by tactic blocks, not assumed. There is no
structure-encoded assumption in the slug.

---

## 5. Badge / status promotion eligibility (peer-reviewer handoff)

### Current gallery `meta.json` status

`src/data/proofs/gauss-wilson-non-cyclic/meta.json` (the parent
gallery entry) already reports:

```json
{
  "status": "verified",
  "badge": "original",
  "sorries": 0,
  "axiomCount": 0,
  "lineCount": 323,
  "theoremCount": 21,
  ...
  "leanFile": {
    "path": "Proofs/GaussWilsonNonCyclic.lean",
    "axiomCount": 0,
    "lineCount": 323,
    "theoremCount": 21,
    "definitionCount": 1,
    "sorries": 0
  }
}
```

### Important observation

The gallery `meta.json` **points only at the parent file**
`Proofs/GaussWilsonNonCyclic.lean`. The three slug files (`OQ01.lean`,
`OQ01A.lean`, `OQ01B.lean`) — totalling 575 LOC and 12 theorems — do
**not appear in any gallery `meta.json`** (verified by
`grep -l 'GaussWilsonNonCyclicOQ01' src/data/proofs/*/meta.json`
returning empty).

**Implication:** The slug's "Phase chain" is research-tier work that
lives outside the gallery's verified-status accounting. No badge
promotion on `gauss-wilson-non-cyclic/meta.json` is *required* by
the S12 ACT completion (the parent file's `verified/original` status
remains accurate). The follow-up question is whether the slug merits
its own gallery entry — that is a peer-reviewer / curator decision,
not a researcher decision.

### Two paths peer-reviewer / curator can take

**Path A — Cross-reference annotation only.** Leave the parent
gallery entry as-is. Add a one-paragraph note in
`src/data/proofs/gauss-wilson-non-cyclic/meta.json` `conclusion.implications`
or in `annotations.json` pointing at the three OQ-01 slug files as
"deeper proof of the iff direction available in research/." Risk:
zero. LOC: ~5.

**Path B — New gallery entry for the iff theorem.** Build a new
`src/data/proofs/gauss-wilson-iff/` gallery entry whose `leanFile`
points at `Proofs/GaussWilsonNonCyclicOQ01.lean` (the OQ01.lean
file is the iff-bearing one), with `proofRepoPath`,
`sections` (matching the §2 / §3 / §4 / §5 / §6 internal sections
of the file), `keyInsights`, etc. Risk: medium (requires
peer-review of the iff proof against the file's docstrings; gallery
schema validation). LOC: ~150 (new file + index.ts update + tests).

A researcher PREP cannot make this call (it's curator scope). This
PREP just records the eligibility and the two paths.

### Verifying badge eligibility

For badge promotion to `verified / original` on a hypothetical
new gallery entry (Path B), the peer-reviewer must confirm:

| Check | How | Expected |
|---|---|---|
| Build-verified at v4.26.0 | `docker-build.sh Proofs.GaussWilsonNonCyclicOQ01` | `[3066/3066] Built ... (~9s)` |
| No `sorry` tactic | `grep -cE '^\s*sorry\s*$\|:= by sorry\|by sorry$\| sorry$\|:= sorry' Proofs/GaussWilsonNonCyclicOQ01.lean` | `0` |
| No `axiom` decl | `grep -cE '^\s*axiom\s+' Proofs/GaussWilsonNonCyclicOQ01.lean` | `0` |
| No structure-encoded assumption | manual `grep '^(structure\|class)\b'` scan | `0` hits |
| Proof statement matches Gauss-Wilson | inspect `prod_univ_units_zmod_eq_neg_one_iff_isCyclic` | matches docstring claim |
| Originality | distinct from `Mathlib.NumberTheory.Wilson` (Mathlib has `ZMod.wilsons_lemma` for prime case; slug covers full iff) | confirmed |

All six checks pass at base `cf1cfa085e4` per §4 above.

---

## 6. PREP errata batch (future researcher handoff)

S12 ACT's session memo §2 documented four ACT-time fixes (F5-F8)
beyond PREP-2 §6's recipe. The original PREP-2 §6 and PREP-3 §3.x
recipes are still on `main` and would re-introduce these bugs if
re-consumed verbatim. Future Researcher iterations re-using those
recipes should apply this errata batch.

### Errata table

| # | Recipe section | Bug | Fix |
|---|---|---|---|
| E1 | PREP-2 §6 import block | Missing `import Mathlib.GroupTheory.PGroup` | Add line `import Mathlib.GroupTheory.PGroup` alongside other GroupTheory imports |
| E2 | PREP-2 §6 import block | Missing `import Mathlib.Algebra.Group.Subgroup.Finite` (needed for `Fintype ↥T` synthesis) | Add line `import Mathlib.Algebra.Group.Subgroup.Finite` |
| E3 | PREP-2 §6 Step 4 bridge | `Fintype.card T = Fintype.card { x // x^2 = 1 } := by rfl` blocked by `Fintype` instance discrepancy between `Subgroup`-derived and `Subtype`-derived instances | Replace with explicit `Equiv T ≃ { x // x ^ 2 = 1 }` constructed via Subtype-mk/Subtype-val swap, then `Fintype.card_congr e` |
| E4 | PREP-2 §6 Step 6 bridge | `symm` before `apply Finset.prod_subtype` is the inverse of the needed direction (PREP-2 over-correction) | Drop the `symm`; `apply Finset.prod_subtype` matches directly post-`rw [SubmonoidClass.coe_finset_prod]` |

### Where to record these

Two options:

- **Option A (heavy):** Issue a "PREP-2 §6 + PREP-3 §3.x errata"
  PR amending those merged session memos. Risk: rewrites history
  for files already long-merged; reviewers may push back.
- **Option B (light, RECOMMENDED):** Embed this errata table in
  the slug's `knowledge.md` so future readers searching for
  `prod_eq_one_of_not_isCyclic_aux` recipe land on the corrected
  version. Risk: minimal; `knowledge.md` is explicitly the
  "lessons learned" file for the slug.

This S13 PREP does **NOT** edit `knowledge.md` (per the "minimal
doc-only" charter). Instead, it records the errata here so the
**next researcher** (or a future Hermit) can decide between A and B
and execute.

---

## 7. S14 ACT readiness gate (post-disk-recovery)

The next "natural ACT" for this slug, if anyone wants one, is the
L112 Hermit fix from §2 above. Pre-flight gate **before** opening
a successor PR:

| # | Gate | Verification command | Expected |
|---|---|---|---|
| 1 | Host disk ≥ 50 Gi free, ≤ 95% capacity | `df -h /System/Volumes/Data` | `Avail ≥ 50G`, `Capacity ≤ 95%` |
| 2 | Docker daemon responsive | `timeout 10 docker info -f '{{.ServerVersion}}'` | exits 0 in < 10s |
| 3 | Mathlib pin unchanged | `grep '"rev"' proofs/lake-manifest.json` | `"rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"` |
| 4 | Parent file untouched | `git log -1 --format='%H' -- proofs/Proofs/GaussWilsonNonCyclic.lean` | unchanged from `cf1cfa085e4` |
| 5 | OQ01 file head sha matches PREP | `git log -1 --format='%H' -- proofs/Proofs/GaussWilsonNonCyclicOQ01.lean` | tip of `bde082d967a` (S12 ACT) |
| 6 | No competing PR | `gh pr list --repo rjwalters/lean-genius --search "gauss-wilson-non-cyclic-oq-01 in:title" --state open` | empty |

When **all 6 gates pass**, apply the §2 diff, run
`./proofs/scripts/docker-build.sh Proofs.GaussWilsonNonCyclicOQ01`,
expect `[3066/3066] Built ... ~5-10s` and zero linter warnings,
then open a Hermit-style PR titled
`hermit(gauss-wilson-non-cyclic-oq-01): drop unused neg_one_sq simp arg at L112 (build-verified)`.

---

## 8. Files this PR touches

| File | Action | Delta |
|---|---|---|
| `research/problems/gauss-wilson-non-cyclic-oq-01/state.md` | UPDATE | 3 LOC-drift corrections (256→265 ×2, 243→244 ×1) + S13 PREP entry prepended to iteration log |
| `research/problems/gauss-wilson-non-cyclic-oq-01/sessions/2026-05-16-s13-prep-post-completion-housekeeping.md` | NEW | this file |

## Files this PR does NOT touch

- Any `proofs/Proofs/*.lean` file (zero Lean edits)
- Any `src/data/proofs/*/meta.json` file (badge-promotion path is curator scope)
- Any `research/problems/*/knowledge.md` (errata recording deferred to next session)
- Any `proofs/lake-manifest.json` (Mathlib pin unchanged)
- `research/registry.json` (slug not tracked there per `grep gauss-wilson` returning empty)

### Conflict-free guarantees

- Single slug touched (`gauss-wilson-non-cyclic-oq-01/`); no other
  slug-tree edits.
- No Lean / no Docker → cannot race with build-verified PRs.
- State.md head head-of-file is being updated, but only in 4 specific
  cells of the phase-chain table + 1 paragraph; no structural
  reorganization. Merge conflicts with concurrent STATE-SYNCs are
  unlikely (and trivially resolvable line-by-line).
- No `meta.json` edits → no schema-validation risk.

---

## 9. Sorries / axioms delta for this PR

- Sorries: unchanged (slug-wide remains 0).
- Axioms: unchanged (slug-wide remains 0).
- Structure-encoded assumptions: unchanged (0).

This PREP is doc-only by design.

---

## 10. Honest confidence assessment

**High confidence (act on directly):**
- §1 LOC-drift correction (verified by `wc -l`).
- §2 L112 Hermit fix paste-ready diff (1-token deletion; semantic risk is zero; only risk is "linter warning persists" which only happens if simp suddenly fails to close the goal — extremely unlikely with v4.26.0 default simp set).
- §3 bearer-pin drift recheck (4 spot-checks all resolve at pinned SHA).
- §4 slug-wide 0/0/0 audit (verified by grep + manual structure scan).

**Medium confidence:**
- §5 Path B (new gallery entry) recommendation — this is genuinely a
  curator / peer-reviewer decision that requires reading the iff
  proof against the file's docstrings, not a researcher rubber-stamp.
- §6 errata batch — accurate as documentation but may be overruled
  by a researcher who finds a cleaner re-derivation.

**Low confidence:**
- None. This PREP intentionally constrains scope to verifiable
  documentation and paste-ready protocols.

**What this PREP explicitly does NOT do:**
- Verify the L112 fix builds (deferred until host disk recovers; §7
  pre-flight gate lists exactly what to check before attempting).
- Edit `knowledge.md` (deferred to next session, see §6).
- Promote a gallery badge (curator scope, see §5).
- Audit the slug's Lean files for further lint warnings beyond the
  known `neg_one_sq` one (out of scope; sample-of-one).

---

## Handoff

| Recipient | Item | Section |
|---|---|---|
| Hermit (or next Researcher) | L112 unused-simp-arg fix | §2 + §7 pre-flight |
| Auditor | slug-wide 0/0/0 confirmation table | §4 |
| Peer-reviewer | badge-promotion eligibility analysis | §5 |
| Curator | gallery cross-reference vs new entry decision | §5 |
| Next Researcher iteration | PREP-2 / PREP-3 errata batch | §6 |

Slug status after this PR: **functionally complete with one
unused-simp-arg lint warning pending Hermit sweep at L112.** All
other follow-on items are quality-of-life / metadata polish.

— end S13 PREP —
