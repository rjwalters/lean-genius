# Research State: erdos-816-oq-01

## Current State
**Phase**: ORIENT (was OBSERVE / 0 knowledge)
**Path**: full
**Since**: 2026-06-14 (researcher-1, Session 1)
**Iteration**: 1

## Current Focus
Fresh OQ: lower/remove Chen–Ma's `n ≥ 600` threshold for the stronger #816 result
(`≥ n²+n` edges ⇒ equal-degree P3 pair, unique exception `K_{n,n+1}`).
Build-free empirical ORIENT (both backends down).

## Findings (Session 1)
- **n = 1**: stronger result is FALSE (degenerate — `2n+1=3 < 4` so no P3 exists;
  triangle `K_3` is a non-`K_{1,2}` counterexample). Threshold cannot go below `n = 2`.
- **n = 2**: TRUE, `K_{2,3}` unique exception. Exhaustive (386 graphs).
- **n = 3**: TRUE, `K_{3,4}` unique exception. Exhaustive (695 860 graphs, 10.6 s).
- ⇒ true threshold is very likely `n ≥ 2`; `n ≥ 600` is a proof-method artifact.

## Active Approach
Exhaustive labelled brute force with early-exit + `K_{n,n+1}` detector
(`scripts/verify_threshold.py`). Fully reproducible on host `python3`.

## Blockers
- Docker daemon down (cannot build Lean).
- Aristotle MCP `prove` → "Resource not found" (backend down).
- `n ≥ 4` infeasible by naïve enumeration (needs isomorph-rejection / structure).

## Next Action
- (ACT, build host) Optionally formalize the `n = 2, 3` base cases as decidable
  finite checks in a companion file once Docker/Aristotle returns.
- (Math) Extend empirical check to `n = 4, 5` via `nauty`-style canonical
  enumeration to further pin the threshold.
- The general-`n` removal of the restriction is the Chen–Ma-level open content and
  remains `axiomatized` in the gallery.

## Attempt Count
- Total attempts: 0 Lean builds (build-free survey)
- Approaches tried: 1 (exhaustive small-n brute force — conclusive for n ≤ 3)
