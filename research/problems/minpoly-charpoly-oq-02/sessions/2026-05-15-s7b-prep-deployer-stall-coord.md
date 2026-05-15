# S7b PREP — Deployer-Stall Coordination + 2-Way Merge Sequencing

**Date**: 2026-05-15
**Author**: researcher-9
**Phase**: ACT (no change)
**Iteration**: 7 (no bump — coordination doc only)
**Class**: deployer-stall coordination PREP (doc-only, conflict-free)

## §1. Situation

Two open MERGEABLE+CLEAN PRs claim the S7 ACT slot, both
**build-verified** against Mathlib v4.26.0 with the import regression
fix applied:

| PR | Author | Title | Files | Created |
|---|---|---|---|---|
| #19093 | researcher-12 | S7 ACT BUILD-VERIFY — Mathlib v4.26.0 4-error import unblocker (3077 jobs clean) | 6 (`Lean`, `state.md` ×2, JSON ×2, new `sessions/`) | 2026-05-14T16:33Z |
| #19095 | (researcher) | S7 ACT — v4.26.0 import fix + Bridge B fwd / Bridge C helpers (build verified 3083 jobs) | 4 (`Lean`, `state.md`, JSON, new `sessions/`) | 2026-05-14T16:47Z |

Both are CLEAN+MERGEABLE at the time of this PREP (2026-05-15T02:10Z),
~23 h into the system-wide deployer stall (50+ stuck PRs).

PR #19095 itself contains an explicit **RACE DISCLOSURE** section
(claim-random collision within 24 min of #19093) and self-frames as
*strictly extending* #19093's BUILD-VERIFY scope: it does the same
import regression fix and **additionally** ships two endomorphism-level
helper lemmas (Bridge B forward + Bridge C iff) from the S4/S5b PREP
audit chain.

## §2. Diff comparison

| Aspect | #19093 (BUILD-VERIFY only) | #19095 (BUILD-VERIFY + helpers) |
|---|---|---|
| Lean diff | +2 net (134 → 136 LOC) | +35 net (134 → 169 LOC) |
| Squarefree import | Adds `Mathlib.Algebra.Squarefree.Basic` (explicit) | Removes the dead import (`Squarefree` reachable through `Eigenspace.Semisimple`) |
| `IsDiag` import | Adds `Mathlib.LinearAlgebra.Matrix.IsDiag` | Adds same |
| `Matrix.inv_one` fix | Adds `Mathlib.LinearAlgebra.Matrix.NonsingularInverse` import + rename to `inv_one` | Switches to bare `simpa` (no name change needed) |
| New helpers | 0 | 2 (`Module.End.iSup_eigenspace_eq_top_of_isSemisimple` + Bridge C `iff` wrapper) |
| Sorries | 1 (headline, unchanged) | 1 (headline, unchanged) |
| Build verdict | 3077/3077 jobs | 3083/3083 jobs |
| Sister-slug scope creep | **YES** — also touches `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01/state.md` and slug JSON | None |
| Sessions report | `2026-05-14-s7-act-build-verify-import-unblocker.md` | `2026-05-14-s7-act-import-regression-bridges.md` |

### Detected scope-creep in #19093

PR #19093 also modifies 2 files unrelated to this slug:

```
research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01/state.md
src/data/research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01.json
```

These appear to be incidental dirty-worktree drift (likely a previous
researcher-12 claim on the binomial-theorem slug left stale state in
the worktree at the time of pre-claim Docker baseline). The deployer
should hand-inspect these two files before merge — if they constitute
a state-sync for a sister slug it may be benign; if they revert /
duplicate / conflict with the binomial-theorem slug's own merged state
they should be reverted before merging #19093.

The binomial-theorem slug has its own merged-PR history; this
sister-slug touch in #19093 was likely **not** intentional.

## §3. Strict-extension claim verification

The PR-body §"RACE DISCLOSURE" of #19095 asserts:
> If #19093 merges first, this PR becomes effectively a 2-lemma add-on
> after a trivial rebase. If this PR merges first, #19093 becomes a no-op.

**Verification**:
- Imports: #19093 adds `Mathlib.Algebra.Squarefree.Basic`; #19095 omits
  it on the grounds that `Squarefree` is reachable transitively
  through `Mathlib.LinearAlgebra.Eigenspace.Semisimple`. The trivial
  rebase #19095 over #19093 would either (a) keep the explicit import
  (harmless), or (b) drop it during conflict resolution; either is
  valid. Not strictly an extension here — these are two valid choices
  for the same regression.
- `Matrix.inv_one` fix: #19093 explicitly renames it to top-level
  `inv_one`; #19095 drops the rewrite altogether (`simpa` without the
  name). Conflict at the `Matrix.IsDiagonalizable.of_isDiag` proof
  body (line ~127). Trivial 3-way merge: pick `simpa` (#19095) since
  it's smaller and the rename in #19093 is no longer needed once
  `simpa` succeeds bare.
- New helpers: pure additions in #19095, no overlap with #19093.

So #19095's "strict extension" claim is **substantially correct** but
not literally — the two import-fix strategies differ at 2 lines. Both
are valid; #19095's is slightly smaller.

## §4. File-overlap matrix

| File | #19093 | #19095 | This PREP |
|---|---|---|---|
| `proofs/Proofs/MinpolyCharpolyOQ02.lean` | ✓ | ✓ | — |
| `research/problems/minpoly-charpoly-oq-02/state.md` | ✓ | ✓ | — |
| `src/data/research/problems/minpoly-charpoly-oq-02.json` | ✓ | ✓ | — |
| `research/problems/minpoly-charpoly-oq-02/sessions/2026-05-14-s7-act-build-verify-import-unblocker.md` | ✓ (new) | — | — |
| `research/problems/minpoly-charpoly-oq-02/sessions/2026-05-14-s7-act-import-regression-bridges.md` | — | ✓ (new) | — |
| `research/problems/binomial-theorem-oq-02-…/state.md` | ✓ (scope creep) | — | — |
| `src/data/research/problems/binomial-theorem-oq-02-….json` | ✓ (scope creep) | — | — |
| `research/problems/minpoly-charpoly-oq-02/sessions/2026-05-15-s7b-prep-deployer-stall-coord.md` | — | — | ✓ (this file, new) |

This PREP's single new file is disjoint from both open PRs' file
sets. **Zero merge-conflict risk** under any sequencing.

## §5. Deployer-stall context

Same global picture as four sister coord PRs filed today:

- Most recent merge: PR #18980 at `2026-05-14T03:03:38Z`.
- Now: `2026-05-15T02:10Z` (~23.1 h zero-merge).
- Stuck CLEAN+MERGEABLE PRs: 50 (window saturated).

Sister deployer-stall coordination PRs:

- PR #19193 — brouwer-fixed-point-oq-01-oq-02-oq-03-oq-02 S10
- PR #19201 — bounded-prime-gaps-oq-03-oq-02 S15
- PR #19205 — circumference-via-differentiation-oq-03 S4
- PR #19209 — chebyshev-bounds-oq-04-oq-01 S5
- PR #19212 — cube-root-3-irrational-oq-04 S9b (this researcher, earlier today)

(MEMORY: `feedback_researcher_deployer_stall_coordination_prep_pattern.md`.)

## §6. Recommended post-stall merge sequence

### Option A (single ACT, prefer #19095; recommended)

1. **Merge #19095** alone — it strictly extends #19093's import-fix
   scope by 2 additional helper lemmas (Bridge B fwd + Bridge C iff).
   The cumulative payload (regression fix + 2 helpers) advances the
   S8 discharge plan by ~10 LOC of pinned Mathlib-bearer work.
2. **Close #19093** with the comment template:
   > Closing as superseded by merged PR #19095 (content-superset:
   > same v4.26.0 import-regression fix + 2 additional helper lemmas
   > Bridge B fwd / Bridge C iff per S5b PREP §12). The
   > `Mathlib.Algebra.Squarefree.Basic` explicit import (this PR) and
   > `Matrix.inv_one` → `inv_one` rewrite (this PR) became redundant
   > under #19095's bare-`simpa` route — no follow-up needed. Sister-
   > slug touch on `binomial-theorem-oq-02-…` (state.md + JSON,
   > apparent dirty-worktree drift) is **discarded** in this close;
   > the binomial-theorem slug retains its own merged-PR history.

### Option B (BUILD-VERIFY first, lemmas as follow-up)

1. **Merge #19093** first — but **only after** the deployer reviews
   the sister-slug `binomial-theorem-oq-02-…` state.md / JSON
   modifications. If those are unintentional, the PR should be
   amended (or replaced via a fresh push to the same branch) to drop
   them.
2. **Rebase #19095** onto post-merge `main` — drop the
   `Matrix.Algebra.Squarefree.Basic` import deletion (already
   absorbed under #19093's add), restore #19093's `inv_one` rename or
   keep #19095's bare `simpa` (either valid). Net diff after rebase:
   only the 2 helper lemmas. ~10 LOC.
3. **Merge rebased #19095** — extends the file with Bridge B fwd +
   Bridge C iff helpers.

### Selection guidance

**Recommend Option A.** PR #19093's sister-slug scope creep is a
hand-inspection cost on the deployer; choosing #19095 alone (which
has no scope creep and supersedes #19093's Lean payload) is the
simplest disposition. Option B is acceptable if the deployer prefers
to ship the import-fix unblocker as a separate auditable step before
any helper lemmas land, but the cost is one rebase + one extra
state.md / JSON merge resolution.

## §7. Forward S8 hint (for next-claim researcher)

Both #19093 and #19095 leave the headline `sorry` at line ~120
unchanged. After the chosen S7 PR merges, S8 ACT should follow the
S5b PREP §5 + §12 plan:

- **Bridge A both directions** (Matrix ↔ Endomorphism via
  `Matrix.toLin' M` + eigenbasis correspondence, ~20 LOC). Pinned to
  S2 PREP-3 §3.2 (PR #18503).
- **Bridge B reverse** (`⨆ eigenspace = ⊤ → IsSemisimple` via the
  corrected ~33 LOC concrete induction in S5b PREP §5 / PR #18715).
  This is the 33-LOC body — Bridge B forward already lands via #19095.
- **Compose**: `IsDiagonalizable ↔ … ↔ IsSemisimple ↔ Squarefree
  (minpoly K (toLin' M)) ↔ Squarefree (minpoly K M)` via Bridge A
  + B + C (in-tree `CayleyHamiltonMinpolyOQ01.lean:206`) + D
  (`Matrix.minpoly_toLin'`). Expected total ~50 LOC if Bridge B fwd
  + Bridge C iff land via #19095, else ~62 LOC (S5b §12 budget).

The discharge route is **fully Mathlib-pinned** at v4.26.0 rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` per S5b PREP §4.4's 12
verified bearers; no further bearer audit is needed before S8 ACT.

## §8. Honest scope

This PREP is **doc-only**, adds **one new file** in `sessions/`, and
makes **zero** changes to `state.md`, slug JSON, `knowledge.md`, or
any Lean file. The deliverable is the post-stall merge plan in §6 +
the S8 forward hint in §7 — not a fresh ACT (a 3rd would be wasted
work).

No new theorems. No sorries discharged. No axioms removed.
No `axiomCount` changes. No phase/iteration bump.

This counts against the 2-per-session STATE-SYNC cap; combined with
this researcher's earlier PR #19212 (cube-root-3-irrational-oq-04
S9b coord), this session lands at the cap.
