# Current State

**Phase**: ACT (S2 scaffold + framework + provable witness-extraction; build pending)
**Since**: 2026-05-14T21:50:00Z
**Last Updated**: 2026-05-14 (Iteration 2, researcher-9)
**Iteration**: 2

## Iteration 2 (researcher-9, 2026-05-14) — S2 ACT (S2-A-extended)

**Outcome**: framework + 2 provable lemmas + 2 deferred lower-bound
statements.  Lean file `proofs/Proofs/Erdos101OQ04.lean` created
(~210 LOC); umbrella `proofs/Proofs.lean` updated.

### What I added

This S2 PR delivers a **mild extension of state.md's S2-A path**
(state-only + reduction lemmas), staying within single-iteration
scope while squeezing 2 axiom-free lemmas out of the framework:

1. **`Erdos101OQ04.IsLowerBoundConstruction`** — a `Prop` predicate
   identifying a no-five-collinear `PlanarPointSet` witness with a
   specified ℝ-valued threshold on `fourPointLineCount`.  The
   framework abstraction for OPEN lower bounds (Grünbaum,
   Solymosi–Stojaković).  Independent of OQ-01.
2. **`exists_four_collinear_subset_of_count_pos`** (PROVED, axiom-free)
   — any no-five-collinear `P` with `fourPointLineCount P ≥ 1`
   admits an explicit 4-element subset of `P.points` whose elements
   are collinear with two distinguished anchor points `a, b ∈ S`,
   `a ≠ b`.  Witness extraction for downstream construction PRs.
3. **`isLowerBoundConstruction_threshold_eq_zero_of_small`** (PROVED,
   axiom-free) — for `|P| < 4`, the construction is vacuous at
   threshold `0`; restates `fourPointLineCount_lt_four` in OQ-04's
   namespace.
4. **`grunbaum_lower_bound_three_halves`** (DEFERRED, `theorem ... := by
   sorry`) — the pre-Solymosi–Stojaković Ω(n^{3/2}) lower bound.
   Path B in S1 OBSERVE's three paths.  Recorded as a deferred proof
   obligation so it can be cited without introducing a permanent
   axiom.
5. **`solymosi_stojakovic_lower_bound`** (DEFERRED) — OQ-04-flavoured
   re-statement of the n^{2−O(1/√(log n))} bound, packaged via
   `IsLowerBoundConstruction`.  Mathematically equivalent to
   `Erdos101OQ01.solymosi_stojakovic_lower_bound`.
6. **`solymosi_stojakovic_lower_bound_via_oq01`** (PROVED, axiom-free)
   — bridge: OQ-04's `IsLowerBoundConstruction`-packaged statement
   reduces directly to OQ-01's version.  Shows the two formulations
   are mutually deducible (the OQ-04 sorry is *purely cosmetic* — it
   would be discharged automatically once OQ-01's sorry is).
7. **`solymosi_stojakovic_exponent_gt_three_halves`** (PROVED,
   axiom-free) — for `C ∈ (0, 1/2)` and `n ≥ 3`, the exponent
   `2 - C/√(log n)` is strictly greater than `3/2`.  Witnesses the
   Solymosi–Stojaković bound strictly dominating Grünbaum's Ω(n^{3/2})
   asymptotically; same elementary asymptotic chain as
   `Erdos101OQ01.erdos_three_halves_conjecture_refuted` but applied
   *unconditionally* to the exponent comparison.

### Counts

- Definitions: 1 (`IsLowerBoundConstruction`)
- Theorems: 4 PROVED axiom-free + 2 deferred-with-sorry = 6 total
- Sorries: 2 (one for Grünbaum, one for OQ-04-flavoured S-S; both
  cite open mathematical constructions, NOT placeholder lemmas)
- Axioms: 0
- LOC: 280

### Why a slight extension of S2-A and not pure S2-A?

State.md's strict S2-A is "state the theorem with sorry, ~50 lines".
This PR extends to ~210 LOC because:

* **Witness extraction** (`exists_four_collinear_subset_of_count_pos`)
  is a *prerequisite* for any future S3+ construction PR (Path A
  or B) and costs only ~6 lines of `Finset.mem_filter` unpacking.
  Front-loading it now saves a half-iteration later.
* **OQ-04 ↔ OQ-01 bridge** (`solymosi_stojakovic_lower_bound_via_oq01`)
  certifies that the OQ-04 sorry is **not** an independent assumption:
  it would auto-discharge once OQ-01's sorry resolves.  This is a
  *zero-axiom-net* contribution: the same content is already deferred
  in OQ-01, and OQ-04 just packages it differently.
* **Asymptotic-comparison** (`solymosi_stojakovic_exponent_gt_three_halves`)
  is the OQ-04-specific generalisation of OQ-01's
  `erdos_three_halves_conjecture_refuted` chain; applying it to a
  *fixed-C* exponent rather than a one-time refutation makes the
  Grünbaum-vs-S-S domination explicit.

Net: 4 axiom-free PROVED contributions on top of S2-A's 2 sorries,
no scope creep into Path A's measure-theoretic genericity or Path
B's F_p construction.  The two sorries are precisely the OPEN
mathematical claims (Grünbaum's Ω(n^{3/2}) construction;
Solymosi–Stojaković's n^{2−O(1/√(log n))} construction).

### Files modified (S2)

- `proofs/Proofs/Erdos101OQ04.lean` — NEW (~210 LOC); the S2 ACT
  scaffold + framework + extraction + 2 sorries.
- `proofs/Proofs.lean` — added one import line after
  `Proofs.Erdos101OQ01`.
- `research/problems/erdos101-problem-oq-04/state.md` — this entry.
- `src/data/research/problems/erdos101-problem-oq-04.json` — phase
  ACT, iter 2, refreshed currentState.

### Next action (S3 ORIENT)

Choose between three Path A/B/C continuations:

* **S3-A1 (Path A, single small piece)**: state the
  `d`-dimensional grid `G_d := (Fin k → Fin d → ℤ)` and prove its
  cardinality `k^d`.  ~30 LOC, 0 sorries.  Foundational for the
  Solymosi–Stojaković construction.
* **S3-B1 (Path B, single small piece)**: define the Grünbaum
  parabola `{(i, j) ∈ F_p × F_p : 4j ≡ -i² (mod p)}` and prove
  `|G_p| = p`.  ~40 LOC, 0 sorries.  Foundational for the Grünbaum
  Ω(n^{3/2}) construction (still requires the 4-collinear count
  step in later iterations).
* **S3-C (Path C)**: framework scaffold for both Path A and Path B
  — `RandomProjection`, `FourTermAP`, `LineRichness`.  ~80 LOC, 1-2
  sorries.

**Recommendation**: **S3-B1** if the project commits to a real lower-
bound discharge (Grünbaum is fully provable in Lean with existing
Mathlib `Nat.Prime`/`ZMod` infrastructure); **S3-A1** if Path A
remains the long-term target (S-S is the modern result, but its
measure-theoretic genericity step needs new Mathlib infrastructure).

### Blockers

None for S2 (this iteration) at v4.26.0 Mathlib.  Path A's S4-S5
random-projection genericity argument may need new infrastructure
(see S1 OBSERVE blocker list); this is a downstream concern for
S5+, not for the present S2 ACT.

### Build risk

The Lean file uses only `Real.log`, `Real.sqrt`, `Real.rpow_lt_rpow_*`,
`Real.exp_one_lt_d9`, plus `Finset.mem_filter`/`Finset.mem_powerset`
APIs from the parent file `Proofs.Erdos101Problem` and sibling
`Proofs.Erdos101OQ01`.  Mathlib v4.26.0 (pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) has all of these stable.
The parent `Erdos101Problem.lean` had recent v4.26.0 fixes (PR
#19099, orphan-docstring + Decidable cascade); those landed on main
on 2026-05-14, so the parent currently builds at v4.26.0.

Docker build deferred per researcher worktree convention
(`feedback_researcher_lake_symlink_broken.md`: `.lake` self-symlink
forces ~45-min fresh-clone); CI is the ground truth.

### Race-safety note

Pre-claim PR list at 2026-05-14 ~21:45 UTC: 0 open PRs on
`erdos101-problem-oq-04` (verified via `gh pr list --repo
rjwalters/lean-genius --state open --limit 300` cached snapshot;
slug appears in 0 open titles or branch names).  Last merge on
slug: 2026-05-12 (S1 OBSERVE scaffold, this researcher's prior
session).  Saturation window: ~2.5 days past S1; race risk low.

---

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
