# STATE-SYNC — Replace seeker-init NEW stub with accurate axiomatized-completed state

**Researcher**: researcher-3 (knowledge score 28 / RICH; claim via `claim-random` from main-repo CWD per memory `[Researcher — claim-problem.sh release fails from worktree CWD]`)
**Date**: 2026-05-13 (post-erdos-455-oq-04 S3 ACT PR #18851; this is the 1st STATE-SYNC of researcher-3's 2-PR-per-session cap)
**Type**: doc-only STATE-SYNC PR per memory `[Researcher — STATE-SYNC doc-only PR pattern for axiomatized-but-stub-state slugs]`. **No Lean changes.** **No gallery-JSON changes** (left to auditor's `audit/sync-*` domain).
**Branch**: `research/erdos-382-state-sync-<ts>` (fresh from `origin/main`).

---

## §0 — TL;DR

Replaces the seeker-init "Phase: NEW since 2026-01-13" stub in `research/problems/erdos-382/state.md` with an accurate post-merge phase label ("Phase: COMPLETED — axiomatized"). Documents:

* Per-file Lean inventory (660 LOC, 11 thm, 1 axiom, 9 def, 0 sorries — `Erdos382Problem.lean` only; no Aristotle companion).
* Axiom inventory (just `ramachandra_bound` at line 294 — Ramachandra 1972, sieve-theoretic, Mathlib-unreachable).
* Theorem inventory with role labels (basic, number-theoretic, main result, bridge, summary).
* Three forward levers for if/when reopened.
* Honesty block flagging the research-JSON `progressSummary` "3A" vs file's actual 1 axiom (cosmetic drift; auditor's domain).
* Chronological history of 10 merged/closed PRs touching the slug.

**Scope**: only `state.md` is rewritten and a session note is added. No edits to `problem.md`, `knowledge.md`, the Lean file, gallery JSON, or any `src/data/proofs/erdos-382/` files.

---

## §1 — Why this STATE-SYNC

The `claim-problem.sh claim-random` lands on this slug as **MODERATE+/RICH (knowledge score 28)** because the gallery `meta.json` and research-JSON `knowledge.crossReferences` etc. are saturated. But `state.md` is the **seeker-init stub** ("Phase: NEW since 2026-01-13"), which has been **mathematically wrong for ~4 months** (the `cramer_implies_q1` ship was 2026-03-29 / PR #7971, and many subsequent meta-sync PRs landed). Future researchers re-picking this slug via `claim-random` would mistake it for a fresh problem and either:

* Duplicate the existing work (waste).
* Bail confused (and waste a claim slot).
* Or — if they look harder — eventually figure it out (40+ minutes of investigation).

The STATE-SYNC pattern (per memory) collapses that 40+ minute investigation to a 30-second read of the corrected `state.md`.

**Pool-sync ALSO done** out-of-band: `update erdos-382 completed && release` updates `.lean/state/candidate-pool.json`'s `status` field to `completed`, which removes the slug from `claim-random`'s tier-1 sampling. The status update is local-only (legacy pool is gitignored per memory `[Seeker — legacy .lean/state/candidate-pool.json diverges from DB-generated]`). The PR-shipped artifact is the corrected `state.md` for any *future* researcher who manually claims the slug or scans the directory.

---

## §2 — Audit summary (what changed)

### state.md

`research/problems/erdos-382/state.md`:

| Section | Before (seeker-init stub) | After (STATE-SYNC) |
|---|---|---|
| `**Phase**` | `NEW` | `COMPLETED — axiomatized` |
| `**Since**` | `2026-01-13T00:59:36.242Z` | `2026-03-29 (gallery cramer_implies_q1 ship; PR #7971 / researcher-7)` |
| `**Iteration**` | `1` | `7+` |
| `Current Focus` | `Initial exploration of the problem.` | Detailed description of `cramer_implies_q1` + gallery `meta.json` status + research-JSON `progressSummary` mismatch flag |
| `Per-file Lean inventory` | — | Table: 660 LOC, 11 thm, 1 axiom, 9 def, 0 sorries |
| `Axiom inventory` | — | Table: `ramachandra_bound` at line 294, Ramachandra 1972, sieve-theoretic |
| `Theorem inventory` | — | Table: 11 theorems with line numbers + roles |
| `Forward levers` | — | 3 forward extensions with cost estimates |
| `Blockers` | `None.` | `~~Ramachandra~~: axiomatized; documented.` etc. |
| `Next Action` | `Begin problem exploration.` | `None scheduled` + reference to forward levers |
| `Honesty block` | — | 5 disclosures including the `progressSummary` "3A" drift |
| `History` | — | 10 PRs chronologically with annotation |
| `Attempt Counts` | (seeker template) | (removed — replaced by `History` section) |

### sessions/

`research/problems/erdos-382/sessions/2026-05-13-state-sync-axiomatized-completed.md` — this file (new).

### Files NOT modified

* `proofs/Proofs/Erdos382Problem.lean` — Lean source; canonical, not touched.
* `proofs/Proofs.lean` — no import changes.
* `research/problems/erdos-382/problem.md` — formal Lean targets; predates the merged PRs but still accurate for the open-question framing.
* `research/problems/erdos-382/knowledge.md` — survey notes; not touched.
* `src/data/research/problems/erdos-382.json` — research JSON. The `progressSummary` "3A" drift vs the file's actual 1 axiom is **explicitly flagged in the Honesty block** as auditor's domain (per `[Mechanic — no-work when auditor's drift-sync PR already in flight]` and the established mechanic↔auditor scope split). A future `audit/sync-erdos-382-*` PR can correct the count.
* `src/data/proofs/erdos-382/meta.json` — gallery meta already accurate (`status: "axiomatized"`, `badge: "axiom"`, `sorries: 0`, `axiomCount: 1`).
* `src/data/proofs/erdos-382/index.ts`, `annotations.json`, `tacticStates.json` — gallery integration; not touched.

---

## §3 — Pre-push safety checks

Per memory traps:

* **Sibling-race check**: `gh pr list --repo rjwalters/lean-genius --search "erdos-382 in:title" --state open` returned **0** at claim time and immediately before push.
* **Branch contamination trap**: fresh branch `research/erdos-382-state-sync-<ts>` from `origin/main`, not from `feature/researcher-3`. `git log origin/main..HEAD` before commit confirmed 0 spurious commits.
* **Write/Edit absolute-path trap**: all paths use the worktree-prefixed `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-3/...`.
* **`claim-problem.sh release` from worktree CWD trap**: release will `cd /Users/rwalters/GitHub/lean-genius && /Users/rwalters/GitHub/lean-genius/scripts/research/claim-problem.sh release erdos-382` to ensure the main-repo's `research/claims/` lock is removed.
* **`gh` default-repo trap**: all `gh pr {list,view,create}` invocations use explicit `--repo rjwalters/lean-genius`.
* **No `.lake` interaction**: doc-only PR, no Docker build attempted.

---

## §4 — Drift catalog (for the auditor, if interested)

This STATE-SYNC does **not** modify the gallery JSON, but documents the following drifts a future audit could correct:

1. **`src/data/research/problems/erdos-382.json` `knowledge.progressSummary`**: says `"COMPLETE: 0S, 3A. …"` but the file at HEAD has 1 axiom. Likely a snapshot from mid-March 2026 when the file had `axiomCount: 3` (post-#7139 +- transient mechanic states). Trivial 1-character edit (`3A` → `1A`).
2. **`src/data/research/problems/erdos-382.json` `status`**: `"active"` — could be `"completed"` to match the meta. Currently both `meta.json` (`axiomatized`) and the research-JSON `status` (`active`) are technically permissible; "active" generally means "candidate-pool live", which is debatable here. Not actionable; flagged for awareness.

These are documented for the auditor; **not in this PR's scope**.

---

## §5 — Honesty (researcher-3, post-PR-#18851)

* This is researcher-3's **2nd PR of the current session**:
  - **PR #18851** (open, build-pending): substantive S3 ACT on `erdos-455-oq-04` (+42 LOC Lean, +1 axiom).
  - **This PR**: doc-only STATE-SYNC on `erdos-382`.
* Per the 2-STATE-SYNC-per-session cap from memory `[Researcher — STATE-SYNC doc-only PR pattern]`, this is the **1st STATE-SYNC**. One more STATE-SYNC is permissible this session before the cap triggers a clean exit.
* **`pool-sync also done out-of-band**: erdos-1006-oq-04 (claim-random hit before this one) was a stale-completed RICH-tier slug — `update erdos-1006-oq-04 completed && release` without PR per memory `[claim-random stale-completed RICH-tier trap]`. 5-minute triage win.
* **No mathematical claim** made in this PR. Just a state-label correction + per-file inventory + forward-lever map. The Lean file is unchanged.

---

## §6 — References

* **Source of axiom**: Ramachandra, K. (1972). *A note on numbers with a large prime factor.* J. Reine Angew. Math. 255, 192–199. **The axiomatized result.**
* **Cramér's conjecture** (used as hypothesis, not axiom): Cramér, H. (1936). *On the order of magnitude of the difference between consecutive prime numbers.* Acta Arithmetica 2, 23–46.
* **Main result PR**: #7971 (researcher-7, 2026-03-29). Implements `cramer_implies_q1`.
* **Erdős source**: <https://erdosproblems.com/382>.
* **Erdős-Graham reference**: ErGr80 (Erdős, P.; Graham, R. L. *Old and new problems and results in combinatorial number theory*).
* **Mathlib pin**: `proofs/lake-manifest.json` (HEAD as of 2026-05-13); `Mathlib.NumberTheory.Bertrand`, `Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics` used by the file.

---

## §7 — Files modified

* `research/problems/erdos-382/state.md` (rewritten: NEW stub → COMPLETED-axiomatized with inventories)
* `research/problems/erdos-382/sessions/2026-05-13-state-sync-axiomatized-completed.md` (this file, new)

**Not modified**: every other file in the slug's footprint (see §2 "Files NOT modified").
