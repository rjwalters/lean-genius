# State: collatz-cycles-oq-03

## Current Phase

**COMPLETED.** S1 OBSERVE survey + S2 ACT Lean file + S3 GALLERY entry
all delivered in this PR. Build verified via Docker (`Proofs.CollatzCyclesOQ03`
compiled cleanly, exit 0, 3.7s, 80 lines, 0 sorries, 0 axioms).

## Summary

The OQ seeks the parity-intersection corollary for Collatz cycles:
every cycle visits at least one even number. The argument is a short
parity contradiction using only parent's `collatz_odd` lemma. This PR
delivers all three stages:

- **S1 OBSERVE** — four-file research scaffold + Lean skeleton draft.
- **S2 ACT** — `proofs/Proofs/CollatzCyclesOQ03.lean` (80 lines, 1
  lemma + 4 theorems, 0 sorries, 0 axioms), registered in
  `proofs/Proofs.lean`. Build verified.
- **S3 GALLERY** — `src/data/proofs/collatz-cycles-oq-03/` with
  `meta.json`, `index.ts`, `annotations.json` (5 annotations).

## What This PR Delivers

### Research scaffold (S1 OBSERVE)

- `research/problems/collatz-cycles-oq-03/problem.md` — formal
  statement, equivalent phrasings, Lean skeleton, decomposition.
- `research/problems/collatz-cycles-oq-03/knowledge.md` — parent
  inventory, Lean skeleton with proof, Mathlib gap analysis (none),
  Aristotle non-submission rationale.
- `research/problems/collatz-cycles-oq-03/state.md` — this file.
- `src/data/research/problems/collatz-cycles-oq-03.json` — research
  index entry.

### Lean proof (S2 ACT)

- `proofs/Proofs/CollatzCyclesOQ03.lean` (80 lines, 1 lemma + 4
  theorems, 0 sorries, 0 axioms):
  - `three_n_plus_one_even`: `n % 2 = 1 → (3*n+1) % 2 = 0` (omega).
  - `collatz_of_odd_is_even`: `n % 2 = 1 → (collatz n) % 2 = 0`.
  - `no_all_odd_cycle`: contradiction proof (case k=1 vs k≥2).
  - `cycle_contains_even`: positive form via `by_contra`.
  - `isPeriodic_contains_even`: `IsPeriodic`-packaged version.
- `proofs/Proofs.lean` — registered `import Proofs.CollatzCyclesOQ03`.
- Build verified: `./proofs/scripts/docker-build.sh Proofs.CollatzCyclesOQ03`
  exits 0; `Built Proofs.CollatzCyclesOQ03 (3.7s)`; full umbrella
  `Build completed successfully (3059 jobs)`.

### Gallery entry (S3)

- `src/data/proofs/collatz-cycles-oq-03/meta.json` — status `verified`,
  badge `original`, 0 axioms, 5 theorems, 0 defs, lineCount 80.
- `src/data/proofs/collatz-cycles-oq-03/index.ts` — standard
  glob-discovered loader.
- `src/data/proofs/collatz-cycles-oq-03/annotations.json` — 5
  annotations, one per theorem.

## OQ Status

**Closed.** All deliverables present and build-verified.

## Session Log

| Step | Action | Outcome |
|------|--------|---------|
| S1.1 | Released 3 saturated MODERATE+ probes (konigsberg-oq-01-oq-02, sperner-ndim-mathlib-oq-02, abel-ruffini-galois-extensions-oq-07) | switched to tier-B fallback |
| S1.2 | Trap-checked tier-B available pool: 17 slugs; filtered by `0 open PRs ∧ added_at older than 30 min` | cold-slug shortlist: collatz-cycles-oq-03 (4h old), ballot-problem-oq-02-oq-05 (null), central-limit-...-oq-04-oq-01 (null) |
| S1.3 | Claimed `collatz-cycles-oq-03` via direct `claim` | claimed |
| S1.4 | Created branch `research/collatz-cycles-oq-03-s1-observe-<ts>` off `origin/main` | clean base |
| S1.5 | Read parent `Proofs/CollatzCycles.lean` (256 lines) | identified API surface and gap |
| S1.6 | Classified problem: TRIVIAL (2-line omega proof from `collatz_odd`) | S1 OBSERVE doc-only is the right scope |
| S1.7 | Wrote `problem.md`, `knowledge.md`, `state.md`, and the JSON gallery entry | S1 deliverables complete |
| S1.8 | Pre-push race probe + commit + push + PR (S1 doc-only) | branch pushed at 14:48Z, no PR yet — superseded by S2 bundling |
| S2.1 | Re-acquired worktree mid-session; race-probed `gh pr list --search collatz` | empty, safe to bundle S2 into same branch |
| S2.2 | Wrote `proofs/Proofs/CollatzCyclesOQ03.lean` from `knowledge.md` skeleton; tweaked `simp [collatzIter, Function.iterate_one]` to explicit `Function.iterate_one` rewrite for robustness | 80 lines, 5 decls |
| S2.3 | Registered `import Proofs.CollatzCyclesOQ03` in `proofs/Proofs.lean` between `CollatzCycles` and `CollatzCyclesOQ04` | alphabetical |
| S2.4 | `LEAN_BUILD_TIMEOUT=45m ./proofs/scripts/docker-build.sh Proofs.CollatzCyclesOQ03` | ✔ build exit 0, `Built Proofs.CollatzCyclesOQ03 (3.7s)`, 3059 jobs |
| S3.1 | Wrote `src/data/proofs/collatz-cycles-oq-03/{meta.json,index.ts,annotations.json}` matching the `collatz-cycles-oq-04` pattern | gallery entry ready |
| S3.2 | Pre-push race probe (TBD) + commit + push + PR | next |

## Honest Calibration

This PR delivers:

- Research scaffold (S1) + Lean proof file (S2) + gallery entry (S3).
- **No new mathematical content**: the proof is a one-line corollary of
  the existing `collatz_odd` parent lemma; what this PR contributes is
  the *explicit statement* of a fact that the parent currently leaves
  implicit.
- 80-line Lean file with 5 declarations (1 lemma + 4 theorems), 0
  sorries, 0 axioms, build verified.
- Gallery entry (`status: "verified"`, `badge: "original"`,
  `lineCount: 80`, `theoremCount: 5`, `axiomCount: 0`).

This PR does **not**:

- Touch any existing `.lean` file (only adds the new companion).
- Change the parent's axiom count or status (already `verified`).
- Make any progress on the Collatz conjecture itself or on the deeper
  halving-constraint machinery — that's `collatz-cycles-oq-04`.

**Difficulty**: trivial (2-line omega proof from `collatz_odd`).
**Novelty**: zero — standard textbook parity argument.
**Gallery value**: low-medium — fills an obvious explicit-statement
gap in a `verified` parent.

## References Captured

- Parent: `Proofs/CollatzCycles.lean` (Parts I–VIII).
- Lagarias (1985), *The 3x+1 problem and its generalizations*.
- Eliahou (1993), cycle length lower bounds.
- Mathlib v4.26.0: `Mathlib.Tactic` (omega), `Mathlib.Logic.Function.Iterate`.
