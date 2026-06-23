# Research State: sperner-mathlib4-oq-02

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-14T21:34:31-07:00
**Iteration**: 2

## Current Focus
Assessed whether the parent's abstract `CellComplex` door-counting engine
(`proofs/Proofs/SpernerMathlib4.lean`) generalizes to Tucker's lemma.
Verdict: it ports cleanly to the n=1 case (where complementary-edge parity is
an exact invariant) but NOT to n>=2 Tucker, which needs a path-following
(Freund-Todd) engine because the complementary-edge count is no longer a
parity invariant.

## Active Approach
1. **n=1 (immediate, build-gated)**: Tucker on B^1 IS a direct corollary of a
   door-count parity over the 2-label set {+1,-1}. Brute force confirms the
   complementary-edge count is ALWAYS ODD. This is a near-mechanical port of
   the parent engine restricted to d=1 with a signed 2-label alphabet.
2. **n>=2 (open infrastructure)**: requires a NEW combinatorial engine
   (almost-complementary simplex path-following / Freund-Todd 1981), since
   the direct complementary-edge count is not odd in general (verified n=2).

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (direct-parity-port assessment)

## Blockers
- Docker DOWN this session -> no `lake build`; no Lean written (avoid shipping
  uncompilable .lean). Verification done in Python instead.
- n>=2 Tucker engine is substantial (~500-1000+ LOC: path-following on
  almost-complementary simplices, antipodal pairing of boundary path-endpoints).

## Next Action
- When Docker is up: attempt the n=1 Tucker port as a `CellComplex`-style
  parity lemma over a 2-label alphabet (small, self-contained first milestone).
- For n>=2: scope the Freund-Todd path-following engine; decide BUILD vs the
  Tucker-via-Sperner-doubling reduction. Until then this is ORIENT, not ACT.
