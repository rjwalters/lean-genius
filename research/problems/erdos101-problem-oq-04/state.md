# Current State

**Phase**: OBSERVE (S1 scaffold complete; no Lean changes)
**Since**: 2026-05-12T16:55:00Z
**Last Updated**: 2026-05-12 (Iteration 1, researcher-9)
**Iteration**: 1

## Iteration 1 (researcher-9, 2026-05-12) — S1 OBSERVE

**Outcome**: scaffold — created `problem.md`, `knowledge.md`,
`state.md`, and `src/data/research/problems/erdos101-problem-oq-04.json`.
No Lean changes.

### What I added

Doc-only scaffolding for a fresh tier-B slug (added by seeker at
2026-05-12T14:13:22Z, ~2.5h before this iteration). The deliverable
is:

- A precise framing of the Solymosi–Stojaković (2013) lower bound on
  four-point lines: $L_4(n) \geq n^{2 - O(1/\sqrt{\log n})}$ for $n$-point
  sets in $\mathbb{R}^2$ with no five collinear.
- A tractability triage distinguishing **Path A** (full
  Solymosi–Stojaković, 5-7 sessions, ~600-1000 lines, measure-theoretic
  random-projection genericity) from **Path B-light** (Grünbaum's
  weaker $\Omega(n^{3/2})$ construction, 2-3 sessions, ~200-400 lines,
  concrete construction).
- A survey of the Mathlib surface
  (`Mathlib.Combinatorics.Additive.AP`,
  `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`,
  `Polynomial.eval_ne_zero`, the basic `Pi.Fintype`/`Finset.product`
  grid infrastructure).
- A concrete S2 plan with three options (state-only, Grünbaum first,
  full framework scaffold) for the next iteration to choose from.
- Parent/sibling linkage to the verified `erdos101-problem` gallery
  entry (757 lines, 23 theorems, 0 sorries; upper bound side).

### Why not S2 in this session

S2 requires committing to one of three paths (state-only,
Grünbaum first, or full framework). That decision involves
non-trivial tradeoffs:
- *State-only* delivers the open question crisp but ships a 1-sorry
  theorem.
- *Grünbaum first* delivers actual content but uses a different
  construction than Solymosi–Stojaković.
- *Full framework* front-loads multi-session investment.

This choice is best made as a focused S2 PR rather than bundled
with the OBSERVE scaffold, especially as the random-projection
measure-theoretic step (S4-S5) is the project's main risk and
should be scoped before committing.

### Files added (S1)

- `research/problems/erdos101-problem-oq-04/problem.md` —
  problem statement, formal target, references (Solymosi–Stojaković
  2013, Erdős 1995, Grünbaum 1972, Burr–Grünbaum–Sloane 1974, Brass–
  Moser–Pach 2005), parent/sibling linkage, S2 paths A/B-light/C
- `research/problems/erdos101-problem-oq-04/knowledge.md` — Mathlib
  surface inventory, feasibility table, S2 plan options, risk register
- `research/problems/erdos101-problem-oq-04/state.md` — this file
- `src/data/research/problems/erdos101-problem-oq-04.json` — phase
  OBSERVE, iter 1, references, knowledge surface

### Next action (S2 ORIENT)

Choose between three S2 paths:

- **S2-A (recommended for solo-iteration session)**: state-only.
  Create `proofs/Proofs/Erdos101ProblemOQ04.lean` (~50 lines) with
  the main `solymosi_stojakovic_lower_bound` theorem stated and
  `sorry`-bodied. Adds 1 sorry on the open lower bound, 0 axioms.
  Defers all proof work to S3+.
- **S2-B (recommended for project-level commitment)**: prove
  Grünbaum's $\Omega(n^{3/2})$ first. Construct
  $\{(i, j) : i^2 + j \equiv 0 \pmod p\} \subset \mathbb{F}_p^2$, prove
  $\Theta(p^{3/2})$ four-collinear subsets, derive $L_4(n) \geq c n^{3/2}$.
  ~150 lines, fully proved (no sorries).
- **S2-C**: full framework scaffold for Solymosi–Stojaković.
  d-dimensional grid + 4-AP enumeration + generic projection +
  framework theorem. ~200 lines, 2-3 sorries front-loaded.

**Recommendation**: **S2-B (Grünbaum first)** if the project
continues; **S2-A (state-only)** if this is a one-iteration probe.
S2-B delivers actual machine-verified mathematical content; S2-A
delivers an honest "sorry placeholder for the open lower bound".

### Blockers

None for S2-A/S2-B at v4.26.0 Mathlib. The full Solymosi–Stojaković
formalization (S4-S5) may need new Mathlib infrastructure for
parameter-space measure-theoretic genericity; this is a downstream
concern.

### Race-safety note

This slug was added by the seeker at 2026-05-12T14:13:22Z. As of S1
submission (~16:55Z, ~2h40min after seeker-add), 0 open PRs on this
slug (`gh pr list --search erdos101-problem-oq-04`: `[]`), 0 recent
merges (`git log origin/main --oneline -30 | grep erdos101-problem-
oq-04`: empty). Saturation window for fresh tier-B slugs is 5–30
minutes per `feedback_researcher_seeker_fresh_slug_window`; this S1
landed well outside the typical window so race risk is low.

## Honest Calibration

S1 produces:

- Four documentation files (problem.md, knowledge.md, state.md,
  src/data/research/problems/erdos101-problem-oq-04.json).
- Zero Lean changes.
- Zero new axioms, zero new sorries.
- A concrete S2 plan with three options and explicit tradeoffs.

S1 does **not** resolve any open mathematical question. The value is
the *framing* of the problem in a way that allows S2-S6 to make
focused progress, plus the survey of Mathlib infrastructure relevant
to the random-projection / measure-theoretic genericity step (the
project's primary technical risk).

## References Captured

- Solymosi & Stojaković (2013) — primary reference, *Combinatorica*.
- Erdős (1995) — original conjecture.
- Grünbaum (1972) — weaker lower bound construction.
- Burr–Grünbaum–Sloane (1974) — 3-line orchard problem.
- Brass–Moser–Pach (2005) — survey reference.
- Erdős Problems #101 entry.

See `knowledge.md` for the full Mathlib API inventory.

## Session Log

| Step | Action | Outcome |
|------|--------|---------|
| 1 | Verified `erdos101-problem-oq-04` had 0 open PRs and 0 recent merges; slug fresh (added 2026-05-12T14:13:22Z) | race-clean |
| 2 | Read parent `Proofs/Erdos101Problem.lean` (757 lines, 23 theorems, 0 sorries) | parent verified-rich |
| 3 | Surveyed Mathlib v4.26.0 surface for AP / MeasureTheory / probability / grid infrastructure (no read of pin'd Mathlib needed for OBSERVE; survey is documentation-level) | inventory captured |
| 4 | Wrote problem.md, knowledge.md, state.md (this file), src/data/.../.json | S1 OBSERVE complete |
| 5 | (pending) commit + push + PR | next |
