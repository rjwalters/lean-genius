# State: collatz-cycles-oq-03

## Current Phase

**OBSERVE → ORIENT bridge.** S1 OBSERVE survey complete (this PR).
S2 ACT is mechanically derivable from the Lean skeleton in `knowledge.md`.

## Summary

The OQ seeks the parity-intersection corollary for Collatz cycles:
every cycle visits at least one even number. The argument is a 2-line
parity contradiction using only parent's `collatz_odd` lemma. S1 has
produced the four-file scaffold; S2 should add a ~50-line Lean
companion file `Proofs/CollatzCyclesOQ03.lean` with three theorems
(`collatz_of_odd_is_even`, `no_all_odd_cycle`, `cycle_contains_even`)
and 0 sorries.

## What S1 Delivered (this PR)

- `research/problems/collatz-cycles-oq-03/problem.md` — formal
  statement, equivalent phrasings, recommended Lean skeleton,
  decomposition table.
- `research/problems/collatz-cycles-oq-03/knowledge.md` — parent
  inventory, Lean skeleton with proof, Mathlib gap analysis (none),
  Aristotle non-submission rationale.
- `research/problems/collatz-cycles-oq-03/state.md` — this file.
- `src/data/research/problems/collatz-cycles-oq-03.json` — research
  index entry.

**No Lean changes** in S1.

## What S1 Did NOT Do

- Did NOT add `Proofs/CollatzCyclesOQ03.lean`.
- Did NOT register a new file in `proofs/Proofs.lean`.
- Did NOT modify the parent (`CollatzCycles.lean`).
- Did NOT create a gallery entry (`src/data/proofs/collatz-cycles-oq-03/`).

These are all S2 / S3 deliverables.

## Next Action: S2 ACT (any researcher)

**Goal**: deliver the Lean companion file with the three parity theorems.

1. Branch off fresh `origin/main`.
2. Race-probe `gh pr list --search "collatz-cycles-oq-03" --state open`
   (mid-write and pre-push). Memory's seeker-fresh-slug saturation
   window does not apply here since the slug is now 4h+ old, but a
   second-actor probe is still wise.
3. Create `proofs/Proofs/CollatzCyclesOQ03.lean` with the body in
   `knowledge.md`'s skeleton section (50 lines total, 0 sorries).
4. Add `import Proofs.CollatzCyclesOQ03` to `proofs/Proofs.lean` (or
   confirm the auto-glob picks it up — check the file's pattern).
5. `./proofs/scripts/docker-build.sh Proofs.CollatzCyclesOQ03` — should
   build in 5-10 minutes after Mathlib cache is warm.
6. Commit + push + PR.

S3 GALLERY (optional, can be combined with S2): create
`src/data/proofs/collatz-cycles-oq-03/` with `meta.json` (status
`verified`, badge `original`, 0 axioms, 3 theorems, 1 def, line count
from the new file), `index.ts`, `annotations.json`.

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
| S1.8 | (pending) Pre-push race probe + commit + push + PR | next |

## Honest Calibration

S1 produces:

- Four documentation files.
- **No new mathematical content**: the proof is a one-line corollary of
  the existing `collatz_odd` parent lemma; what S1 contributes is the
  *explicit statement* of a fact that the parent currently leaves
  implicit.
- A drop-in S2 Lean skeleton that should compile in one shot.

S1 does **not**:

- Touch any `.lean` file.
- Change the parent's axiom count or status (already `verified`, 0 axioms).
- Discharge any sorry (the slug has no Lean file yet).

The realistic estimate for **closing the OQ** is **1 additional session**
(S2 = Lean file + S3 gallery, easily combinable), delivering a clean
`verified` gallery entry with 0 axioms, 0 sorries, 3 theorems, 1 def.

## References Captured

- Parent: `Proofs/CollatzCycles.lean` (Parts I–VIII).
- Lagarias (1985), *The 3x+1 problem and its generalizations*.
- Eliahou (1993), cycle length lower bounds.
- Mathlib v4.26.0: `Mathlib.Tactic` (omega), `Mathlib.Logic.Function.Iterate`.
