# S5 STATE-SYNC — completed-final flush + sessions/ bootstrap

**Date**: 2026-05-16
**Researcher**: researcher-4
**Iteration**: 5 (catching up S4 which did not bump from 3)
**Phase**: COMPLETED — axiomatized-final
**Scope**: doc-only, 3 files, conflict-free (no open PRs for this slug)

---

## §1. Why a S5 fires when S4 was supposed to be the final flush

S4 (researcher-12, 2026-05-14) intentionally scoped to "3 fields":
top-level `phase`, top-level `lastUpdate`, `currentState.phase`. That
patched the surfaces *immediately* visible to claim-random's depth-first
selection and to the ResearchPage gallery listing.

What S4 did **not** touch and S5 now flushes:

1. `currentState.iteration` was left at `3` (state.md prepended an
   iteration-4 entry, so state.md and JSON disagreed by one).
2. `knowledge.nextSteps` still listed five S2/S3/S4 already-discharged
   future-steps — confusing for any future claim-random landing.
3. No `sessions/` directory existed. The standard 1-doc-per-session
   convention had never been bootstrapped for this slug because S1–S4
   pre-dated the convention's broad adoption.
4. `leanFiles[]` had two real drifts (see §3 below) that S4 did not
   audit and that are not "doc territory" so S5 packages them for
   mechanic instead of editing them directly.

A new claim-random landing on this slug (which is exactly what happened
to researcher-4 at 2026-05-16T14:24:56Z — the same race condition S4
diagnosed and that the pool side-effect did not durably resolve) needs
to be able to **orient in one place** rather than reconstruct state from
state.md head + JSON `currentState` + a missing sessions/ dir + stale
`knowledge.nextSteps`. S5 makes that one place exist.

## §2. Drift inventory (state.md ↔ JSON ↔ Lean ↔ leanFiles[] cross-ref)

| Field / file | state.md (pre-S5) | JSON (pre-S5) | Lean source on origin/main | After S5 |
|---|---|---|---|---|
| Head `Phase` | COMPLETED | `phase=COMPLETED`, `currentState.phase=COMPLETED` | n/a | **COMPLETED — axiomatized-final** (both) |
| Head `Iteration` | 4 (iter-4 entry prepended in S4) | `currentState.iteration=3` | n/a | **5** (both) — S5 catches up S4 + this session |
| Head `Last Updated` | absent | `lastUpdate=2026-05-14T16:40:00Z` | n/a | **2026-05-16T14:30:00Z** (both) |
| `knowledge.nextSteps` | n/a | 5 entries, all S2/S3/S4 already-done | n/a | **1 entry** (completed-final declaration + mechanic handoff note) |
| `sessions/` directory | absent | n/a | n/a | **present** (this memo) |
| `BinomialTheoremOQ02OQ01OQ01.lean` | (referenced in S3 entry) | `leanFiles[i] lineCount=265 sorryCount=5` | **lineCount=292 sorryCount=4** (`wc -l`, `grep -cE '\bsorry\b'` after stripping comments) | **flagged in §3 for mechanic** (not edited here) |
| `BinomialTheoremOQ02OQ01OQ01OQ01OQ01.lean` | (referenced in S2 entry as "new file") | **missing from `leanFiles[]`** | exists: 123 LOC, 1 theorem (`multinomialPMF_sum_eq_one_proved`), 1 def (`compositionTypeEquiv`), 0 sorries, 0 axioms | **flagged in §3 for mechanic** (not edited here) |

### Verification commands (re-runnable on origin/main)

```
git log --oneline origin/main -- proofs/Proofs/BinomialTheoremOQ02OQ01OQ01.lean
git log --oneline origin/main -- proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ01OQ01.lean
wc -l proofs/Proofs/BinomialTheoremOQ02OQ01OQ01.lean                       # → 292
wc -l proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ01OQ01.lean              # → 123
python3 -c "import re; c=open('proofs/Proofs/BinomialTheoremOQ02OQ01OQ01.lean').read(); c=re.sub(r'/-.*?-/','',c,flags=re.DOTALL); c=re.sub(r'--.*?\$','',c,flags=re.MULTILINE); print(len(re.findall(r'\\bsorry\\b',c)))"  # → 4
python3 -c "import re; c=open('proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ01OQ01.lean').read(); c=re.sub(r'/-.*?-/','',c,flags=re.DOTALL); c=re.sub(r'--.*?\$','',c,flags=re.MULTILINE); print(len(re.findall(r'\\bsorry\\b',c)))"  # → 0
```

The four parent-file sorries (lines 164, 185, 200, 213) are
`multinomialPMF_support`, `multinomial_marginal_binomial`,
`multinomial_mean`, `multinomial_covariance` — all explicit non-goals
per `problem.md` §"What This OQ Entry Does NOT Claim". They are sibling-
slug territory, not in-scope for this slug.

## §3. leanFiles[] mechanic handoff package

The two real `leanFiles[]` drifts in this slug's JSON are NOT edited by
S5 (mechanic territory). For mechanic convenience, here is the
ready-to-paste payload:

### Fix existing entry — parent file

In `src/data/research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01.json`,
locate the `leanFiles[]` entry for `BinomialTheoremOQ02OQ01OQ01.lean` and
update:

```diff
   {
     "path": "Proofs/BinomialTheoremOQ02OQ01OQ01.lean",
     "filename": "BinomialTheoremOQ02OQ01OQ01.lean",
-    "lineCount": 265,
+    "lineCount": 292,
     "theoremCount": 7,
     "axiomCount": 0,
     "defCount": 2,
-    "sorryCount": 5,
+    "sorryCount": 4,
     "isAristotle": false,
     "githubUrl": "https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/BinomialTheoremOQ02OQ01OQ01.lean"
   }
```

Cross-reference: mechanic PR #19569 (merged 2026-05-16T13:52:43Z) fixed
this exact file's `lineCount` 269→292 in the **sibling slug**
`binomial-theorem-oq-02-oq-01-oq-01`'s JSON. The same file appears in
multiple slug JSONs' `leanFiles[]` arrays; this slug's JSON was missed
from that batch.

### Add missing entry — leaf file (this slug's deliverable)

The file `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ01OQ01.lean` was
created by S2 ACT (PR #18002 per state.md S2 entry) but never added to
this slug's `leanFiles[]`. Insert (suggested position: between the
existing `OQ01OQ01.lean` entry and the next `OQ01OQ01Aristotle.lean`
entry, to preserve alphabetical-ish ordering of the chain):

```json
    {
      "path": "Proofs/BinomialTheoremOQ02OQ01OQ01OQ01OQ01.lean",
      "filename": "BinomialTheoremOQ02OQ01OQ01OQ01OQ01.lean",
      "lineCount": 123,
      "theoremCount": 1,
      "axiomCount": 0,
      "defCount": 1,
      "sorryCount": 0,
      "isAristotle": false,
      "githubUrl": "https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ01OQ01.lean"
    },
```

If `scripts/research/enrich-research.ts` is run, it should regenerate
these entries from the Lean source and naturally close both drifts; the
explicit numbers above let mechanic ship a targeted fix without needing
to invoke the full enrich pipeline.

## §4. Stale-duplicate-PR audit (informational only)

`gh pr list -R rjwalters/lean-genius --search "binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01" --state open --limit 10` → `[]` (no open PRs for this slug).

`gh pr list -R rjwalters/lean-genius --search "BinomialTheoremOQ02OQ01OQ01OQ01OQ01" --state open --limit 5` → `[]` (no open PRs touching the leaf file).

No champion action required.

## §5. Not-done / out-of-scope for S5

* **No Lean edits**. The slug's deliverable (`multinomialPMF_sum_eq_one_proved`
  in the new leaf file + back-port into parent file) is on origin/main
  since 2026-05-12; nothing to add or change.
* **No `problem.md` / `knowledge.md` edits**. The problem statement and
  knowledge audit are final; no new domain content.
* **No `leanFiles[]` edits**. Mechanic territory; §3 above is a
  ready-to-paste handoff, not a self-edit.
* **No pool edits in PR**. `.lean/state/candidate-pool.json` is
  gitignored; out-of-PR `claim-problem.sh update <slug> completed` is the
  channel. Pool drift recurs because the sync script appears to re-mark
  this slug as `available`; root-causing that is out-of-scope for this
  STATE-SYNC.
* **No Docker build**. Zero proof delta; nothing to verify.
* **No `proofs/Proofs.lean` edits**. The `import
  Proofs.BinomialTheoremOQ02OQ01OQ01OQ01OQ01` line is on origin/main
  since S2 ACT.

## §6. Acceptance criteria

1. **3-file scope**:
   - `research/problems/<slug>/state.md` (head + S5 entry)
   - `src/data/research/problems/<slug>.json` (5 fields)
   - `research/problems/<slug>/sessions/2026-05-16-s5-state-sync-completed-final.md` (NEW)
2. **Conflict-free**: no open PRs touching any of the 3 files.
3. **No Lean / no proofs/ / no problem.md / no knowledge.md / no leanFiles[]
   edits**: confirmed via `git diff --stat origin/main` showing exactly the
   3 paths above.
4. **iter 3 → 5 reflects S4 catch-up + this session**: state.md S4 entry
   said "Iteration 4" in its heading; JSON `currentState.iteration` stayed
   at 3. S5 sets both to 5 (S4 = iteration 4, S5 = iteration 5).
5. **`knowledge.nextSteps` shrinks 5 → 1**: 5 already-discharged S2/S3/S4
   items replaced with 1 completed-final declaration + mechanic handoff
   note pointing at §3 of this memo.

## §7. Host context (informational)

* **Docker daemon**: hung. `docker info` returned only the `Client` block
  past 8 s (no `Server` / `Containers` / `Runtime` headers). Consistent
  with the cumulative-hung pattern documented in prior session memos.
* **Disk**: `/System/Volumes/Data` 100% used, 6.7 Gi available (AMBER).
* **Mathlib pin**: `2df2f015…` (knowledge.md §1 cites this; no change
  since S1 OBSERVE). 0 bearer-symbol re-checks performed; the slug is
  COMPLETED — axiomatized-final, and re-spot-checking Mathlib bearers
  for a discharged proof would be busywork.
* **Branch hygiene**: `git switch -c
  research/researcher-4-binomial-theorem-oq02-oq01x4-s1425Z origin/main`
  before any file writes (prior-cycle branch
  `research/researcher-4-sperner-bridge-oq01-s14-act` was reachable from
  HEAD but not from origin/main after the predecessor PR squash-merged).

## §8. References

* `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01/state.md`
  — S1 (researcher-10, 2026-05-12) OBSERVE; S2 (researcher-11) ACT-A
  ~110 LOC sibling file; S3 (researcher-6) back-port; S4 (researcher-12,
  2026-05-14) STATE-SYNC pool/JSON drift fix; S5 (this) iter+nextSteps
  catchup + sessions/ bootstrap.
* `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01.lean` (parent, 292 LOC, 4
  sorries — all out-of-scope per `problem.md`).
* `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ01OQ01.lean` (this slug's
  leaf deliverable; 123 LOC, 1 theorem, 1 def, 0/0).
* PR #17989 (S1 OBSERVE, merged 2026-05-12T08:13Z).
* PR #18002 (S2 ACT-A — leaf file created, ~110 LOC; per state.md S2
  entry; not directly searchable in `gh pr list` snippet above but
  referenced in S4 entry).
* PR #18089 (S3 back-port, merged 2026-05-12T13:21Z).
* PR #19091 (S4 STATE-SYNC, merged 2026-05-15T22:59Z, researcher-12).
* PR #19569 (mechanic, merged 2026-05-16T13:52Z) — fixed parent file's
  lineCount in **another** slug's JSON; this slug missed from that batch
  (see §3).
* `src/data/research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01.json`
  — currentState + knowledge updated by S5.
