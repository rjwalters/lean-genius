# 2026-05-13 — S4 PREP companion: meta.json Stanley formula arithmetic fix

**Researcher**: researcher-3
**Branch**: `research/ehrhart-cube-proven-oq-03-fix-stanley-meta-1778646327`
**Phase**: S4 PREP companion (doc/JSON-only fix recommended by PR #18447 §11.2)
**Parent PREP**: #18447 — S4 PREP Stanley formula arithmetic correction (merged 2026-05-13T02:06Z)

## TL;DR

Patches the four meta.json sites flagged by S4 PREP (#18447) §1 with the
arithmetically-correct Stanley hypersimplex formula. No Lean / state.md /
problem.md / knowledge.md / annotations.json edits.

| Site (current line) | Field            | OLD (wrong)                                   | NEW (correct)                                              |
|---------------------|------------------|-----------------------------------------------|------------------------------------------------------------|
| L72                 | historicalContext | `Σ_j (-1)^j C(d, j) C(n(k-j) + d - 1, d - 1)` | `Σ_{j=0}^{d} (-1)^j C(d, j) C(nk - j(n+1) + d - 1, d - 1)` |
| L74                 | proofStrategy (S4+ horizon) | `\sum_{j=0}^{k} ... \binom{n(k-j) + d - 1}{d - 1}` | `\sum_{j=0}^{d} ... \binom{nk - j(n+1) + d - 1}{d - 1}` |
| L80                 | keyInsights[4]   | `\sum_j ... \binom{n(k-j) + d - 1}{d - 1}`    | `\sum_{j=0}^{d} ... \binom{nk - j(n+1) + d - 1}{d - 1}`    |
| L94                 | openQuestions[0] | `\sum_{j=0}^{k} ... \binom{n(k-j) + d - 1}{d - 1}` | `\sum_{j=0}^{d} ... \binom{nk - j(n+1) + d - 1}{d - 1}` |

Each site also now carries the truncation convention "`C(m, r) = 0` for
`m < 0`" so the `j` upper bound `d` (vs the wrong `k`) is unambiguous.
The two equivalent algebraic forms (PREP §1) are
`nk - j(n+1) + d - 1` (this PR's choice) and `n(k-j) + (d-1-j)` (PREP §1
parenthetical alternative) — both differ from the old `n(k-j) + d - 1`
by the missing `−j` correction.

## Why this fix is safe

**No Lean file changes**. PREP §8.5 confirms: the two stated theorems in
`Proofs/EhrhartCubeProvenOQ03.lean` (`hypersimplex_count_k_one`,
`hypersimplex_palindrome_k_d_minus_1`) do not invoke the bad formula —
they state specific specialisations that are independently correct. The
arithmetic error was purely in human-facing meta.json documentation that
described the S4 horizon, never in any compiled `.lean` code.

**Verification reproduces PREP §3 numeric table**.

| `(d, k, n)`  | Lean `decide` value | Wrong formula | Corrected formula |
|--------------|---------------------|---------------|-------------------|
| `(2, 1, 2)`  | 3                   | 1 ✗           | 3 ✓               |
| `(3, 1, 1)`  | 3                   | 0 ✗           | 3 ✓               |
| `(3, 2, 1)`  | 3                   | 0 ✗           | 3 ✓               |
| `(3, 1, 2)`  | 6                   | 3 ✗           | 6 ✓               |
| `(4, 2, 1)`  | 6 (manual)          | 0 ✗           | 6 ✓               |

The corrected formula matches `decide`-anchored values at every test
point; the wrong formula misses on every point.

## Files touched

- **Modified**: `src/data/proofs/ehrhart-cube-proven-oq-03/meta.json`
  — four arithmetic patches (L72, L74, L80, L94).
- **Added**: `research/problems/ehrhart-cube-proven-oq-03/sessions/2026-05-13-s4-companion-meta-stanley-fix.md`
  — this file.

**No edits** to: `problem.md`, `knowledge.md`, `state.md`,
`annotations.json`, `index.ts`, any `.lean` file under `proofs/`.

## Race-check log

- **2026-05-13 04:21 UTC** Pre-claim probe:
  - `gh pr list --search "ehrhart-cube-proven-oq-03 in:title" --state open` → `[]`.
  - Most-recent merge: PR #18498 (preamble + imports enrichment, 2026-05-13T03:06Z) — 75 min ago, well past the memory's 30-min-post-merge release-and-retry threshold.
  - Sister-PR PREPs #18394, #18403, #18447 all merged 2026-05-13T02:06–02:10Z — none touch meta.json.
- **JSON validity**: `jq -e .` passes after every edit.
- **Wrong-formula sweep**: `grep -oE "n\(k - j\)|n\(k-j\)"` returns 0 matches after patching; `grep -oE "nk - j\(n.1\)"` returns 4 matches.

## Out-of-scope (deliberately deferred)

- **`crossReferences[?]` description (L119)** — contains the formula
  `Σ_j A(d-1, j) · C(n - j + d - 1, d - 1)` attributed to "Stanley's
  general hypersimplex formula". This is actually the *Worpitzky-style
  identity for the unit cube* (right-hand side has no `k` dependence),
  not Stanley's hypersimplex formula. PREP #18447 §1 explicitly limited
  scope to the four inclusion-exclusion sites (L72/L74/L80/L94); the
  cross-reference description is a separate mis-attribution that would
  benefit from a follow-up enrichment PR rather than a doc-fix PR.

- **State machine update** — not advanced. `state.md` is independently
  stale (still shows "Phase: S1 OBSERVE / Iteration: 1" despite many
  S2/S3/S4 PREPs merging since). Phase advancement and iteration
  counter resync should ride with the next ACT discharge (S2.A or
  S2.B), not this small companion fix.

- **PREP §11 step 3+ items** (S2.A ACT, S2.B ACT, S4 ACT) — independent
  follow-up work; this PR strictly closes step 2 of the recommended
  follow-up sequence.

## Honesty disclosures

1. **No Lean build run.** This PR adds zero Lean code and does not
   touch any `.lean` file. Per the project's "do NOT run `lake build`
   directly" rule and the absence of `.lean` edits, no build was
   attempted; nothing in the build-graph could have changed.

2. **No first-principles re-derivation in this PR.** The arithmetic
   correction reuses verbatim the PREP #18447 §2 derivation and §3
   numeric table; this PR is a mechanical application of an already-
   reviewed-and-merged design memo.

3. **Choice of normal form.** I chose `nk - j(n+1) + d - 1` over the
   equivalent `n(k-j) + (d-1-j)` because (a) it matches PREP §1's
   primary-form display and §3 hand-computation conventions, and (b)
   it makes the `−j(n+1)` substitution explicit, which corresponds
   directly to the IE step in any future Lean discharge.

## Decision log

- **2026-05-13 S4-companion**: Decision to patch meta.json without
  also fixing the L119 cross-reference. Reason: scope discipline —
  PREP #18447 explicitly drew the boundary at the four inclusion-
  exclusion sites; the L119 issue is a separate mis-attribution
  (Worpitzky labelled as Stanley) and deserves its own enrichment
  triage rather than being silently bundled.

- **2026-05-13 S4-companion**: Decision to add the truncation
  convention "`C(m, r) = 0` for `m < 0`" inline at every patched
  site. Reason: the upper-bound change `j=0..k → j=0..d` adds
  potentially-negative binomial arguments at high `j`; without the
  convention being adjacent the reader cannot verify the formula
  evaluates correctly at the (3, 2, 1) test point.

- **2026-05-13 S4-companion**: Decision NOT to update state.md.
  Reason: state.md drift (Phase / Iteration counter) is a
  cross-cutting issue spanning 8+ merged PRs, not specific to this
  arithmetic fix; resyncing it here would mix concerns and invite
  conflicts with the next ACT PR.

## End of S4 PREP companion
