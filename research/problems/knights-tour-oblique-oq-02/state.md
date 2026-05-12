# Current State

**Phase**: OBSERVE (S1 scaffold complete; no Lean changes yet)
**Since**: 2026-05-12T10:10:00Z
**Last Updated**: 2026-05-12 (Iteration 1, researcher-1)
**Iteration**: 1

## Iteration 1 (researcher-1, 2026-05-12) — S1 OBSERVE

**Outcome**: scaffold — created `problem.md`, `knowledge.md`, `state.md`,
and `src/data/research/problems/knights-tour-oblique-oq-02.json`. No Lean
changes.

### What I added

Doc-only scaffolding for a fresh tier-B slug. The deliverable is:

- A precise framing of "what is the distribution of oblique counts" as a
  function `obliqueDistribution : ℕ → ℕ` that maps `k` to the number of
  closed knight's tours with exactly `k` oblique turns.
- A tractability triage that distinguishes the **histogram values** (not
  feasible in Lean — requires enumerating ~1.3 × 10^13 tours) from the
  **structural symmetries** (feasible — D4 invariance, reversal symmetry,
  winding-parity, support bounds).
- A survey of the parent infrastructure (`Proofs/KnightsTourOblique.lean`,
  2469 lines, 1 axiom) that the OQ-02 work can directly re-use:
  `obliqueCount`, `tourMoves`, `turnAngle`, `tour_winding_zero`,
  `no_turn_angle_4_all`.
- A concrete S2 plan: build a new `Proofs/KnightsTourObliqueOQ02.lean`,
  define `obliqueDistribution`, re-export the minimum theorem as a
  support lemma, defer D4 invariance to S3.

### Why not S2 in this session

S2 ORIENT requires resolving the `Fintype ClosedTour` instance question
(the parent file uses `Classical.choice` to express tours; an explicit
`Fintype` instance needs `ClosedTour` recast as a subtype of `Vector
Square 64`). That refactor touches the parent file and is best done as a
focused S2 PR rather than bundled with the OBSERVE scaffold.

### Files added (S1)

- `research/problems/knights-tour-oblique-oq-02/problem.md` — problem
  description with tractability triage, references, parent linkage
- `research/problems/knights-tour-oblique-oq-02/knowledge.md` — parent
  infrastructure survey, feasibility table, S2 plan
- `research/problems/knights-tour-oblique-oq-02/state.md` — this file
- `src/data/research/problems/knights-tour-oblique-oq-02.json` — phase
  OBSERVE, iter 1, references, knowledge surface

### Next action (S2 ORIENT)

Create `proofs/Proofs/KnightsTourObliqueOQ02.lean` with:

1. A `Fintype` instance for `ClosedTour` (either as a `decEq` subtype of
   `Vector Square 64`, or via a separate definition aligning with the
   parent's structure).
2. `def obliqueDistribution : ℕ → ℕ`.
3. `theorem obliqueDistribution_zero_below_four : ∀ k < 4,
   obliqueDistribution k = 0` (one-line lift from parent's minimum
   theorem).
4. Stubs for the D4 invariance and reversal-symmetry theorems to be
   filled in S3.

Estimated S2 ACT size: ~100-150 lines, 0 sorries on the support lemma,
1-2 sorries on the D4 / reversal stubs (deferred to S3).

### Blockers

None for the structural-skeleton portion. The histogram values are
out-of-scope (require external enumeration).
