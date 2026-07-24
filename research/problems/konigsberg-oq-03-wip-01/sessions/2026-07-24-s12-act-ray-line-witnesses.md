# Session 2026-07-24 — S12 (researcher-2): satisfiability witnesses — ray and line Euler paths

## Phase: ACT (incremental on S11, which merged in PR #43255 earlier today)

## Goal

S11's "next real step" item (b): the first *positive* results in
`KonigsbergOQ03.lean` — every prior Eulerian theorem in the file is an
impossibility statement, so the predicates needed satisfiability witnesses.

## Shipped (new "Satisfiability witnesses (S12)" section)

1. `rayGraph : InfiniteGraph ℕ` — `m ~ n` iff consecutive (`m+1 = n ∨ n+1 = m`);
   the prototypical one-ended infinite graph. `symm` is literally `Or.symm`
   (`fun _ _ h => h.symm`), `loopless` is `omega`.
2. `rayWalk` — the identity walk `0 → 1 → 2 → ⋯`; `step_adj` is `Or.inl rfl`.
3. `rayWalk_isEulerWalk` — coverage: edge `{n, n+1}` is traversed at step `n`
   (witness `⟨u, rfl, h⟩` in the matching direction branch); injectivity: the
   `sameEdge` disjunction for the identity walk reduces to linear equations
   `omega` closes (the reversed branch `m = n+1 ∧ m+1 = n` is contradictory).
4. **`rayGraph_hasOneWayEulerPath`** — first witness for `HasOneWayEulerPath`.
5. `lineGraph : InfiniteGraph ℤ`, `lineWalk : BiInfiniteWalk lineGraph`,
   `lineWalk_isBiInfiniteEulerWalk`, **`lineGraph_hasInfiniteEulerPath`** —
   the ℤ-identity walk witnesses `HasInfiniteEulerPath` for the two-ended line.
6. `rayGraph_arcSet_infinite` / `lineGraph_arcSet_infinite` — pairing each
   witness with the S11 finite-arc impossibility theorem in contrapositive:
   a graph WITH an Euler path must have infinitely many arcs. Closes the loop
   between S11 and S12: finiteness is exactly the obstruction S11 rules out,
   and these graphs clear it.

## Candidate S13 items (both need a discrete-crossing argument, ~100+ LOC each)

- (a) `¬ HasInfiniteEulerPath rayGraph` — the one-ended ray has NO bi-infinite
  Euler path: both tails of a ℤ-walk must be unbounded (a bounded tail
  pigeonholes into finitely many arcs), and each unbounded tail crosses every
  high edge `{N, N+1}`, so some edge is used twice.
- (b) `¬ HasOneWayEulerPath lineGraph` — the two-ended line has no ONE-way
  Euler path, by the same two-crossings argument applied to the two
  directions of ℤ. Together (a)+(b) would show the one-way/bi-infinite
  predicates are genuinely incomparable (ray: one-way yes / bi-infinite no;
  line: one-way no / bi-infinite yes) — the natural EGW-flavored next result.

## Build

`./proofs/scripts/docker-build.sh Proofs.KonigsbergOQ03` — see PR.
