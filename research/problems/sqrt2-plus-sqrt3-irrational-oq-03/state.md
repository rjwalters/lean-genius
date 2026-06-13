# Research State: sqrt2-plus-sqrt3-irrational-oq-03

## Current State
**Phase**: ACT (proof complete in source; pending Docker build verification)
**Path**: full
**Since**: 2026-06-13
**Iteration**: 1

## Current Focus
STATE-SYNC: the tracker was frozen at OBSERVE / 0 attempts, but a complete
403-line proof already exists at `proofs/Proofs/Sqrt2PlusSqrt3IrrationalOQ03.lean`
(added in #22746). This entry now reflects the actual source state.

## Active Approach
Minimal polynomial of α = √2 + √3 over ℚ is f(X) = X⁴ − 10X² + 1.
The Lean file establishes:
- `aeval_sqrt2_plus_sqrt3` — α is a root of f (α² = 5 + 2√6, α⁴ = 49 + 20√6).
- `minpoly_sqrt2_plus_sqrt3` — f is the minimal polynomial (monic + irreducible
  via rational-root + quadratic-factor analysis, `minpoly.eq_of_irreducible_of_monic`).
- `adjoin_sqrt2_plus_sqrt3_finrank` — [ℚ(√2+√3) : ℚ] = 4.
- `sqrt2_plus_sqrt3_irrational` — Irrational (√2 + √3).

Static scan (comment-stripped) of the source: 0 sorries, 0 `axiom` declarations,
8 theorems/lemmas. Gallery meta records status=`formalized`, badge=`mathlib`,
sorries=0, axiomCount=0, theoremCount=8.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
Docker build infrastructure is down (verification blackout, 2026-06-13), so the
source cannot be machine-checked this session. Status promotion is gated on a
successful build.

## Next Action
When Docker is restored, run `./proofs/scripts/docker-build.sh
Proofs.Sqrt2PlusSqrt3IrrationalOQ03`. If it compiles cleanly (0 sorries,
0 axioms), promote the gallery meta status `formalized` → `verified`
(badge `verified`/`original`) — it is currently verify-ready. Do not promote
to verified until a build confirms compilation.
