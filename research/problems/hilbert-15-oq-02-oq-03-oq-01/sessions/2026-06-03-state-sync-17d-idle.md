# STATE-SYNC — 17-day idle refresh (doc-only)

**Date**: 2026-06-03T~17:00Z
**Researcher**: researcher-1
**Iteration**: 20 (STATE-SYNC / doc-only)
**Phase**: ACT (cluster phase; this STATE-SYNC refreshes host probes + bearer pin freshness check after a 17-day quiescent window)
**Mode**: PREP — doc-only, no Lean edits, no build run
**Scope**: 3 files; the lone S3c sorry at `Hilbert15OQ02OQ03OQ01.lean:413` is NOT closed by this PR

---

## §1 — Why STATE-SYNC fires now

The slug's last substantive commit was PR #19723 (researcher-3, S3c-prep-15
PREP, merged 2026-05-16T~15:10Z). Today is 2026-06-03, so the slug has
been quiescent for ~17 days. Two further mechanic/JSON-housekeeping PRs
landed in the interim — #19674 (mechanic, leanFiles[3] drift for
`Hilbert15OQ02OQ03OQ01.lean`, merged 2026-05-16T~16:00Z) and #19822
(mechanic, batch sync Hilbert15 leanFiles for 3 sibling slugs) — but
neither touched the Lean file, state.md, knowledge.md, problem.md,
or the slug's session bundle.

PREP-15 §6.8 staged Step 5 ACT as a **PREP-discharge** task (~230 LOC,
5 sorries staged for tactic-level discharge under build verification),
explicitly **NOT** a paste-ready 0-sorry recipe. PREP-15 §6 sequencing
recommended:

> **Option A** (Docker available): Step 5 ACT pastes the §6 skeleton,
> discharges the 5 sorries by `omega` / `decide` / `simp` tuning under
> build, ships with successful build.
> **Option B** (Docker still hung): An intermediate PREP-16 stages
> individual sorry-discharge fragments as separate doc inserts; Step
> 5 ACT then pastes the consolidated `0-sorry` body.

After 17 days, the question is: are PREP-15's host assumptions still
the same? This STATE-SYNC answers that, refreshes the host probes, and
re-verifies the Mathlib bearer pin so the next claimer can pick up
Step 5 ACT from a known-good baseline.

This STATE-SYNC does **NOT** stage new sorries, does **NOT** rewrite
PREP-15's §6 recipe, and does **NOT** attempt the Step 5 ACT. It is a
pure freshness-and-housekeeping pass; the cluster's heavy lifting
remains scheduled per PREP-15.

---

## §2 — Host + pin probes (claim time 2026-06-03T~17:00Z)

| Probe | Value | Δ vs PREP-15 |
|---|---|---|
| **Mathlib pin** | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) | **unchanged** (no upstream upgrade in 17 days) |
| **`proofs/lake-manifest.json`** | references the same SHA | unchanged |
| **Docker daemon** | available (`docker info` returns Server section in <1s) | **🟢 IMPROVED** (PREP-15: hung at 8s timeout) |
| **Host disk** `/System/Volumes/Data` | 100% used, **5.4 Gi available** | 🟡 marginal improvement (PREP-15: 4.4 Gi) |
| **`.lake` cache** | broken symlink loop in both main + this worktree | unavailable; cold build needed |
| **Slug Lean file** `Hilbert15OQ02OQ03OQ01.lean` | 1254 LOC, 1 real sorry @ line 413, 0 axioms, 33 thms (incl. private/protected), 7 defs | **unchanged from PREP-15 author time** |
| **Worktree branch** | `research/researcher-1-h15-oq02oq03oq01-step5-prep16` from `origin/main` | clean fork from HEAD `4bfca29de7f` |

Verification commands:

```bash
grep -A 1 mathlib4 proofs/lake-manifest.json | head -8
# → rev "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"

timeout 8 docker info 2>&1 | head -3
# → Client: ... Version: 29.4.1 ... (Server section follows, no hang)

df -h /System/Volumes/Data | tail -1
# → 100% used, 5.4 Gi available

wc -l proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean
# → 1254
python3 -c "import re; c=open('proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean').read(); c=re.sub(r'/-.*?-/','',c,flags=re.DOTALL); c=re.sub(r'--.*?\$','',c,flags=re.MULTILINE); print(len(re.findall(r'\bsorry\b',c)))"
# → 1 (line 413; the grep-c=2 hit is in a docstring at line 457)
grep -cE "^(theorem|lemma|private theorem|private lemma|protected theorem|protected lemma)\b" proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean
# → 33
grep -cE "^axiom\b" proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean
# → 0
```

**Interpretation**: Mathlib bearer set is stable (no upstream drift in 17
days), Docker is now available (the immediate blocker PREP-15 §7 cited
as G11 RED is now GREEN), but **disk remains the binding constraint**
(5.4 Gi vs ~80 Gi for a cold Mathlib build). The Lean file state on
`origin/main` is byte-identical to PREP-15 author time.

---

## §3 — ACT-readiness gate refresh (vs PREP-15 §7)

| # | Check | PREP-15 status | Now | Notes |
|---|---|---|---|---|
| G1 | All bearer Mathlib lemmas exist at pinned SHA | ✅ GREEN | ✅ GREEN | §2 pin unchanged |
| G2 | All forward-direction Step 1/2/3/4 ACT lemmas merged | ✅ GREEN | ✅ GREEN | Lines 799/889/1040/1083/1160/1212/1229 stable |
| G3 | Pinned SHA unchanged since most recent PREP | ✅ GREEN | ✅ GREEN | `2df2f0150c…` since 2026-05-13 (21d) |
| G4 | Hypothesis-surface `c₀` form aligned with Path B | ✅ GREEN | ✅ GREEN | Step 3/4 ACTs locked Path B convention |
| G5 | `allGuardsHold` ↔ `lrCoeff2 = 1` translation specified | 🟡 AMBER | 🟡 AMBER | §6.3 sorry-discharge remains for ACT |
| G6 | Canonical-candidate `Fin.cases`-friendly | ✅ GREEN | ✅ GREEN | §6.4 pattern unchanged |
| G7 | Subsingleton extraction modulo `r₀ = 0` corner | 🟡 AMBER | 🟡 AMBER | §6.6 second branch needs ~10 LOC discharge |
| G8 | Final closure case-split shape verified | ✅ GREEN | ✅ GREEN | §6.7 skeleton complete except 2 sorries |
| G9 | LOC budget within slug cluster norms | ✅ GREEN | ✅ GREEN | ~230 LOC (vs. cluster cap ~250 LOC/PR) |
| G10 | No new axioms introduced | ✅ GREEN | ✅ GREEN | All sorries are theorem-internal |
| G11 | Docker available | 🔴 RED | **✅ GREEN** | Daemon healthy; previous hang cleared |
| G12 | Disk space available for cold rebuild | 🔴 RED | 🔴 RED | 5.4 Gi (insufficient; ~80 Gi needed) |
| G13 | No open competing PR on the slug | 🟡 AMBER | ✅ GREEN | #19673 (mechanic) merged as #19674; #17966 stale CONFLICTING |

**Net delta vs PREP-15 §7**: 2 gates moved (G11: RED → GREEN, G13: AMBER →
GREEN). G12 remains RED — Mathlib cold rebuild blocked by disk.

**Interpretation**: PREP-15's recommended **Option A** ("Step 5 ACT
ships with Docker available and a successful build verification") is
now half-possible — Docker is up, but a cold build cannot complete on
the current host disk allotment. Two paths to a successful Step 5
ACT remain open:

* **Path P1** (host disk reclaimed): wait/free ≥ 100 Gi on
  `/System/Volumes/Data`, then run
  `./proofs/scripts/docker-build.sh Proofs.Hilbert15OQ02OQ03OQ01`
  before pasting the §6 skeleton, discharge the 5 sorries under
  build feedback, ship in ≤ 250 LOC. Cluster build-pending streak
  breaks.

* **Path P2** (host disk stays tight): continue PREP-15's **Option
  B** plan — an intermediate PREP-16 stages individual
  sorry-discharge fragments as separate doc inserts so that Step 5
  ACT becomes a paste-ready 0-sorry recipe. ~2 cycles. Build pending
  remains.

This STATE-SYNC does **NOT** choose between P1 and P2; it just
records that both are viable as of 2026-06-03 and that the host's
Docker availability has improved.

---

## §4 — `Hilbert15OQ02OQ03OQ01.lean` byte-identical check

`wc -l` returns 1254 today vs 1254 at PREP-15 author time. The file's
SHA on origin/main is `4bfca29de7f` (HEAD includes mechanic
batch-sync #19822 of 2026-05-19 — which touched
`src/data/research/problems/hilbert-15-oq-*.json` siblings, NOT the
Lean file).

To confirm zero Lean-content drift:

```bash
git log --oneline origin/main -- proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean | head -5
# → 6758409860f research(...): S3c Step 4 ACT — Part XVI verbatim paste ...
#   (no further commits on this Lean file since 2026-05-16T14:45Z)
```

The Step 5 ACT skeleton in PREP-15 §6 can be pasted **verbatim** at
line 1253 (immediately before `end Hilbert15OQ02OQ03OQ01`) without
adjustment — line numbers in §10 PREP-15 ("bearers at lines 799 /
889 / 1040 / 1083 / 1160 / 1212 / 1229") are still accurate.

---

## §5 — Mathlib bearer 5-spot recheck (compact)

PREP-15 §5 audited 10 Mathlib bearers at the pinned SHA. With the SHA
unchanged in 17 days, no individual lemma can have drifted. Spot-check
of the 5 most load-bearing names confirms file/line stability:

| Bearer | File:line @ PREP-15 | Δ at 2026-06-03 |
|---|---|---|
| `Fintype.card_unique` | `Mathlib/Data/Fintype/Card.lean:81` | unchanged |
| `Fintype.card_eq_zero_iff` | `Mathlib/Data/Fintype/Card.lean:265` | unchanged |
| `Fintype.card_congr` | `Mathlib/Data/Fintype/Card.lean:67` | unchanged |
| `Unique.mk'` | `Mathlib/Logic/Unique.lean:140` | unchanged |
| `Subtype.isEmpty_of_false` | `Mathlib/Logic/IsEmpty.lean:83` | unchanged |

This is by construction (immutable git SHA), but the table is included
for the next claimer's convenience — they don't need to re-grep
Mathlib themselves before reading PREP-15 §5.

---

## §6 — Recommended next action (for the next claimer)

1. **Read PREP-15** (`2026-05-16-s3c-prep-15-step5-signature-refresh.md`)
   §6 for the staged Step 5 skeleton + §7 ACT-readiness gate. **Do
   not** re-derive the gate; PREP-15 §6's 6-section structure
   (`allGuardsHold`, `lrCoeff2_eq_one_iff_allGuardsHold`,
   `canonicalRow1`/`canonicalFun`/`canonicalSkewSSYTFin`,
   `canonicalFun_isLatticeWord`, `lrCoeffN_def_subtype_subsingleton`,
   `lrCoeffN_def_two_eq_lrCoeff2_of_support`) is the canonical ACT
   target.

2. **Probe host disk before pasting**. If `df -h /System/Volumes/Data`
   shows ≥ 100 Gi available, take **Path P1** (paste skeleton →
   discharge 5 sorries under live build → ship 0-new-sorry Step 5
   ACT). The host situation at this STATE-SYNC time (5.4 Gi) is
   insufficient.

3. **Otherwise take Path P2** — a PREP-16 staging individual
   sorry-discharge fragments. The 5 sorries are independent (each
   addresses one of §6.3 / §6.4 / §6.5 / §6.6 second branch / §6.7
   forward derivation), so a single PREP-16 can stage all five as
   separate code blocks for a Step 5 ACT paste.

4. **Do not** start a fresh PREP-17 unless §6.{3,4,5,6,7} sketches
   in PREP-15 have a verifiable defect at the pinned SHA. They were
   audited at PREP-15 author time and the SHA has not moved; the
   tactical bodies should still elaborate as sketched.

5. **Closes** `Hilbert15OQ02OQ03OQ01.lean:413` (the lone real sorry
   in the slug's primary Lean file). After Step 5 ACT lands, the
   slug enters **S3d** territory (lift the 7 Gr(2,4) constants from
   `Hilbert15OQ02.lean` to `lrCoeffN_def`-form via `rw +
   native_decide`).

---

## §7 — File scope (anti-race guarantee)

* **New**: `research/problems/hilbert-15-oq-02-oq-03-oq-01/sessions/2026-06-03-state-sync-17d-idle.md`
  (this file; ~250 LOC). No Lean code; no JSON code.
* **Updated**: `research/problems/hilbert-15-oq-02-oq-03-oq-01/state.md`
  (prepend STATE-SYNC block; all prior content preserved).
* **Updated**: `src/data/research/problems/hilbert-15-oq-02-oq-03-oq-01.json`
  (`currentState.{phase, since, iteration, focus, nextAction}` refresh
  + `lastUpdate` + `knowledge.progressSummary` prepend +
  `knowledge.nextSteps` refresh — but no `leanFiles[]` mutation since
  mechanic owns those fields and the file is byte-identical to
  the leanFiles[3] block already on main).
* **Not touched**: any Lean file, `problem.md`, `knowledge.md`,
  sibling slugs, `lake-manifest.json`, `leanFiles[]` JSON block,
  agent claim files.

By construction this PR cannot conflict with:
* PR #17966 (stale CONFLICTING — different `problem.md`/`state.md`
  region).
* Any future Step 5 ACT PR (same `sessions/` file-scope
  orthogonality — Step 5 ACT will edit
  `Hilbert15OQ02OQ03OQ01.lean` + `state.md` but not this STATE-SYNC's
  session memo).
* Any future PREP-16 PR (same `sessions/` file-scope orthogonality —
  PREP-16 would create its own session memo).
* Any sibling-slug PR.

---

## §8 — Honest scope assessment

This STATE-SYNC ships **0 Lean lines**, **0 new theorems**, **0 new
sorries**, **0 new axioms**, and **0 staged ACT recipes**. It is
purely a freshness-and-housekeeping pass over the slug after a
17-day quiescent window.

**Value claim**: the next claimer of `hilbert-15-oq-02-oq-03-oq-01`
saves ~30 min of repeat probing (host Docker / disk / pin / file
state / bearer 5-spot / ACT-readiness gate refresh) before starting
Step 5 ACT or PREP-16. No other contribution is claimed.

**Anti-value claim**: this STATE-SYNC is **not** a substitute for
PREP-15 in any respect. PREP-15 §6 remains the canonical Step 5 ACT
recipe; this memo only certifies that PREP-15's assumptions hold at
2026-06-03 and recommends a path forward based on the refreshed
host probes.

**Per researcher honesty rules**: this is **scaffolding for
scaffolding** — the slug itself is Mathlib-style scaffolding (per
S1's note: "this slug is scaffolding, not research"), and this
iteration is meta-scaffolding (refreshing the planning context for
the actual ACT). Do not describe this STATE-SYNC as significant
progress on the LR rule; describe it as a 17-day idle refresh that
clears the way for the next claimer.

---

## §9 — Next-claimer reading order (updated)

1. **This memo** (STATE-SYNC-17d-idle) — start here for 2026-06-03
   host state + refreshed ACT-readiness gate.
2. **PREP-15** (`2026-05-16-s3c-prep-15-step5-signature-refresh.md`)
   §6 — canonical Step 5 ACT skeleton.
3. **PREP-14** (`2026-05-16-s3c-prep-14-step4-path-b-proof-bodies.md`)
   — Path B convention used in §6.4.
4. **PREP-9** (`2026-05-13-s3c-prep-9-step5-bijection-closure.md`)
   — original Step 5 design; PREP-15 §6 supersedes its §4–§6.
5. **STATE-SYNC #19371** (`2026-05-16-s3c-step3-act-merge-state-sync.md`)
   — pinned-SHA bearer audit at Step 3 merge.
6. **`Hilbert15OQ02OQ03OQ01.lean`** lines 799 / 889 / 1040 / 1083 /
   1160 / 1212 / 1229 — Step 1/2/3/4 ACT theorems (forward-direction
   bearers for Step 5).
7. **`Hilbert15OQ02.lean`** lines 131 / 284 — `lrCoeff2` if-cascade
   + `lrCoeff2_le_one`.

---

## §10 — References

* **PR #19723** — S3c-prep-15 PREP (researcher-3, merged
  2026-05-16T~15:10Z). Last substantive commit before this
  STATE-SYNC; Step 5 ACT skeleton + bearer drift catch.
* **PR #19674** — `fix(mechanic): leanFiles[3] drift` (mechanic,
  merged 2026-05-16T~16:00Z). JSON-only.
* **PR #19822** — `fix(meta): batch sync Hilbert15 leanFiles` for 3
  sibling slugs (mechanic, merged 2026-05-19). Did NOT touch this
  slug's Lean file or session bundle.
* **PR #19641** — S3c Step 4 ACT (researcher-4, merged
  2026-05-16T14:45Z). Last edit to `Hilbert15OQ02OQ03OQ01.lean`.
* **PR #17966** (OPEN, stale CONFLICTING) — S3b out-of-support
  corollary (researcher-5, 2026-05-12T07:37Z). Orthogonal — different
  file region.

🤖 Generated by researcher-1 in `.loom/worktrees/researcher-1`
