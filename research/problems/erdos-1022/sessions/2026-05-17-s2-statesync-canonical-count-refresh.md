# S2 STATE-SYNC — Canonical Count Refresh (doc-only)

**Date**: 2026-05-17
**Agent**: researcher-11
**Mode**: REVISIT (post-S1 stale narrow-grep drift)
**Outcome**: doc-only STATE-SYNC — 5 numeric fields aligned with canonical gallery meta.json
**Iteration**: 5 → 6
**Phase**: AXIOMATIZED (unchanged)

---

## §0 — Diagnostic Trail

Claim landed on **erdos-1022** (Tier MODERATE+, knowledge score 9, AXIOMATIZED).
Initial scan caught off-by-one drift between the research JSON registry and the
canonical gallery `meta.json` counts.

### S1 predecessor (PR #18886, 2026-05-13, merge author: Robb Walters)

S1 was a first-commit STATE-SYNC that fixed the JSON `[Problem Title]` placeholder
and populated `problemStatement` and `knownResults` for the first time. It also
populated `currentState` and `leanFiles[]` based on the heads of the three Lean
files at that commit (`141cc572f20`).

**S1's reported counts** (state.md status table + JSON `leanFiles[]`):

| File | S1 Lines | S1 Theorems | S1 Defs |
|------|---------:|------------:|--------:|
| `Erdos1022Problem.lean` | 600 | 26 | 6 |
| `Erdos1022OQ01.lean` | 165 | 8 | 3 |
| `Erdos1022OQ03.lean` | 420 | 21 | 8 |
| **Total** | **1185** | **55** | **17** |

**Actual counts at commit 141cc572f20** (matches current `origin/main` byte-for-byte;
file content unchanged since): the line counts were already 599/164/419, and the
canonical inclusive theorem regex
`^(protected|private|noncomputable )*(theorem|lemma) ` gives 28/8/21 (the 2 extra
on Problem.lean are `private lemma card_constOn_le` line 397 and
`private lemma card_monochromatic_on_le` line 416), and the canonical inclusive
def regex `^(noncomputable )?(def|abbrev|structure|class|inductive|instance) `
gives 7/3/8 (the 1 extra on Problem.lean is `private def IsMonochromaticOn`
line 388).

### Diagnostic command

```bash
wc -l proofs/Proofs/Erdos1022*.lean
# 599 Erdos1022Problem.lean
# 164 Erdos1022OQ01.lean
# 419 Erdos1022OQ03.lean
```

S1 reported 600/165/420 — `wc -l` returned 599/164/419 at the same commit
(`git show 141cc572f20:proofs/Proofs/Erdos1022Problem.lean | wc -l → 599`).
The off-by-one is most likely a manual round-up or copy from an editor that
displays "lines including trailing newline" rather than `wc -l` convention.

The narrow theorem-regex miscount is the same convention drift documented
in the broader `_postship_pivot_to_act_phase_slug_where_predecessor_state_sync_miscounted_lean_files_via_narrow_grep` pattern: pre-canonical
researchers used `^theorem ` and missed `private lemma`, `private theorem`,
and `noncomputable theorem` decls. The canonical regex was standardized by
mechanic batches in PRs #19934 / #19816 / #19818.

---

## §1 — Canonical numbers (S2 ground truth)

The canonical mechanic regex convention is already in place at
`src/data/proofs/erdos-1022/meta.json` (set by some prior mechanic batch):

```json
"meta": {
  "lineCount": 599,
  "theoremCount": 28,
  "definitionCount": 7,
  "axiomCount": 1
}
```

And `src/data/proofs/erdos-1022-oq-01/meta.json`:

```json
"meta": {
  "lineCount": 164,
  "theoremCount": 8,
  "definitionCount": 3,
  "axiomCount": 0
}
```

There is no `src/data/proofs/erdos-1022-oq-03/meta.json` (OQ-03 is research-only
and unwired to a gallery entry, contrary to S1's "are separately wired" claim).

**S2 canonical reconciliation**:

| File | S2 Lines | S2 Theorems | S2 Defs | Axioms | Sorries |
|------|---------:|------------:|--------:|-------:|--------:|
| `Erdos1022Problem.lean` | 599 | 28 | 7 | 1 | 0 |
| `Erdos1022OQ01.lean` | 164 | 8 | 3 | 0 | 0 |
| `Erdos1022OQ03.lean` | 419 | 21 | 8 | 1 | 0 |
| **Total** | **1182** | **57** | **18** | **2** | **0** |

---

## §2 — S2 changeset (3 files, doc-only)

### File 1: `src/data/research/problems/erdos-1022.json`

Surgical 5-field + 4-field meta repair:

- `leanFiles[0]` (OQ01): `lineCount` 165 → 164
- `leanFiles[1]` (OQ03): `lineCount` 420 → 419
- `leanFiles[2]` (Problem): `lineCount` 600 → 599; `theoremCount` 26 → 28;
  `defCount` 6 → 7
- `currentState.iteration`: 5 → 6
- `currentState.focus`: refreshed with canonical totals and S2 note
- `currentState.attemptCounts.total`: 5 → 6
- `lastUpdate`: 2026-05-13T13:00:00Z → 2026-05-17T05:35:00Z

### File 2: `research/problems/erdos-1022/state.md`

- Head `Iteration`: "5+ shipped (exact count unrecorded; see …)" → "6 shipped
  (S1 STATE-SYNC #18886 2026-05-13, S2 STATE-SYNC 2026-05-17)"
- Status table: 3 row updates + total row + new prose note explaining canonical
  regex convention and S1→S2 delta
- Gallery-meta cross-reference correction: state.md previously claimed
  "no `src/data/proofs/erdos-1022/`" — incorrect; the gallery dir exists.
  Also corrected "erdos-1022-oq-03/ are independent gallery entries" — OQ-03
  has no gallery dir.
- New **Iteration Ledger** table with iter 1–6 history
- Honesty §: replaced S1's snapshot prose with S2 canonical numbers + INFRA
  snapshot

### File 3: `research/problems/erdos-1022/sessions/2026-05-17-s2-statesync-canonical-count-refresh.md`

This file (new).

---

## §3 — INFRA Snapshot (G7 / G8 / G9)

Concurrent with **erdos-301 S3 STATE-SYNC** (PR #20145, T-30m, same researcher-11
session). All three RED carry forward unchanged.

| Gate | State | Evidence | Bearing on S2 |
|------|-------|----------|---------------|
| G7 (host disk) | **RED** | `df -h /Users` → 4.5 GiB avail (below 5 GiB soft floor; same as erdos-301 S3) | doc-only insensitive |
| G8 (docker server) | **RED** | `docker ps` hung at 5s timeout; daemon socket exists but daemon unresponsive | doc-only insensitive |
| G9 (.lake host-rooted) | **GREEN** | `.lake` symlink resolves to a host path (not self-cycle); irrelevant since no build attempted | doc-only insensitive |

Doc-only PR has no Docker/build dependency, so all three REDs are non-blocking.
Path-A window continues from the erdos-301 S3 cycle.

---

## §4 — Race detection

```bash
gh pr list --search "erdos-1022 in:title" --state open --json number,title
# []
gh pr list --search "erdos-1022" --state open --json number,title | head
# []
```

No open PRs touching this slug. Safe to ship.

Concurrent open PR #20145 (erdos-301 S3, same researcher-11) touches a
disjoint slug and a disjoint research JSON; no merge conflict possible.

---

## §5 — S3 picker matrix (for any future iteration)

(This section advisory; S2 closes the doc-only window. No active claim
required.)

| Option | Cost | Value | Risk | Notes |
|--------|------|-------|------|-------|
| **A. Discharge `lll_propertyB` at $t=3, d=1$ via combinatorial proof** | medium (~150 LOC) | high (eliminates 1 axiom from gallery axiomatized inventory) | low (the `lll_condition_t3_d1` numerics already check; just need a clean combinatorial 2-coloring of an intersection-degree-1 3-uniform family — direct application of greedy / Lovász matching argument) | LLL becomes vacuous at $d=1$ since each edge depends on no other (intersection-degree 1 means a single shared element, so independence in the LLL sense fails to bite). A direct constructive proof should fit in ≤200 LOC. |
| **B. Formalize $c(3) \geq 1$ result (1-sparse 3-uniform ⇒ Property B)** | medium (~200 LOC) | high (first non-trivial sparsity-conjecture small-case result) | medium (sparsity is a global constraint; needs Finset.sum_comm' or double-counting argument similar to `degree_bounded_implies_sparse`) | Strictly generalizes the matching case, brackets the answer between `matching_has_propertyB` and `erdos_first_moment_bound`. |
| **C. Sparsity-aware OQ-01 hierarchy** | high (~300 LOC) | medium (extends OQ-01 to sparsity regime) | medium-high (B_k machinery; existence of $c(t,k)$ is open) | Mostly framework work; the actual generalization theorem statement is open-ended. |
| **D. Wire OQ-03 to a gallery entry** | low (~60 LOC content + index.ts wiring) | low (visibility for LLL infrastructure work) | low | Doc-only; mostly meta.json and annotations. Useful only if the LLL bridge gets discharged (option A). |

**Recommended sequencing**: A (concrete, axiom-eliminating, near-term) →
D (cheap visibility win after A succeeds) → B (extends matching case
non-trivially) → C (last; framework-heavy with open ending).

---

## §6 — Cross-slug INFRA cross-validation

Concurrent T-30m to T-60m cycle:

- **erdos-301 S3 STATE-SYNC** (PR #20145, researcher-11, this same cycle):
  same 3-RED snapshot (G7 4.5 GiB, G8 Docker hung, G9 GREEN). Doc-only.
- Same Mathlib pin `2df2f0150c…` byte-stable. No infra change in this window.

---

## §7 — Pool flip decision

erdos-1022 status is `active` in `src/data/research/problems/erdos-1022.json`
and the candidate-pool status is `in-progress` (per claim-random output).
**Do NOT flip to completed**: the problem is `AXIOMATIZED` (open conjecture
+ open LLL bridge), not solved. The active claim from `claim-random` will
expire via TTL (90 min). No `claim-problem.sh update` call needed.

---

## §8 — Files modified

```
research/problems/erdos-1022/sessions/2026-05-17-s2-statesync-canonical-count-refresh.md  | NEW
research/problems/erdos-1022/state.md                                                     | ~30 lines
src/data/research/problems/erdos-1022.json                                                | 6 fields
```

---

## §9 — Outcome

- 5 numeric drift fields surgically corrected (lineCount on 3 files, theoremCount + defCount on Problem.lean)
- 4 meta fields refreshed (iteration, focus, attemptCounts.total, lastUpdate)
- Iteration ledger and Honesty section in state.md aligned with S2 ground truth
- Gallery-meta cross-reference corrected (erdos-1022/ exists; erdos-1022-oq-03/ does not)
- Future-iteration S3 picker matrix recorded for reference
- INFRA 3-RED carry-forward documented; no build attempted

No Lean changes. No gallery `meta.json` changes. Doc-only.
