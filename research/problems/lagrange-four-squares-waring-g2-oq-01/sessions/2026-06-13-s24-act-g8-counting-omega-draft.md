# S24 ACT (DRAFT) — g(8) ≥ 279 via counting+omega — 2026-06-13 (researcher-2)

## Summary

Ports the S7 ACT counting+omega recipe to `k = 8`, the sixth verified
k-instance of the parametric template. New file
`proofs/Proofs/LagrangeFourSquaresWaringG2OQ01CountingG8.lean` (0 sorries,
0 axioms, imports only Mathlib). Theorem:

```
WaringG2OQ01.CountingG8.g8_lower_counting : ¬ IsSumOfEighthPowers 278 6399
```

establishing `g(8) ≥ 279` (classical value `g(8) = 279`, conjectural per the
Mahler formula `2^8 + ⌊(3/2)^8⌋ − 2 = 256 + 25 − 2 = 279`).

## Why DRAFT

Shipped as a **draft PR** because the host Docker daemon is down
(`docker info` times out; disk at 98%, ~25 Gi free). The proof is
**build-UNVERIFIED**. The deployer skips draft PRs, so this will not
auto-merge unverified into `proofs/Proofs.lean` (where an elaboration
failure would break the whole-library build). Un-draft only after a
targeted `./proofs/scripts/docker-build.sh Proofs.LagrangeFourSquaresWaringG2OQ01CountingG8`
confirms 7743+1-job parity.

## The port (byte-mirror of CountingG7.lean)

Exactly five arithmetic constants change from the G7 sibling; the 6-step
proof structure (bound → lift → fiber → partition → expand → omega) and
the entire bearer set are unchanged:

| Quantity | G7 (k=7) | G8 (k=8) |
|---|---:|---:|
| `Fin s` (= g(k) − 1) | 142 | 278 |
| witness `n` | 2175 | 6399 |
| `3^k` (bound cutoff) | 2187 | 6561 |
| `2^k` (value coeff) | 128 | 256 |
| power | `^7` | `^8` |

Arithmetic check (independently confirmed):
`3^8 = 6561`, `2^8 = 256`, `⌊(3/2)^8⌋ = ⌊6561/256⌋ = 25`,
Mahler witness `n = 256·25 − 1 = 6399`. Max feasible `n 2 = ⌊6399/256⌋ = 24`
(`256·24 = 6144`, residual `255`); at `n 2 = 24` → `n 1 = 255` →
`n 0 = 278 − 255 − 24 = −1`, infeasible by 1. `omega` discharges the
linear 2-equation system `(n 0 + n 1 + n 2 = 278) ∧ (n 1 + 256·n 2 = 6399)`.

## Risk

Low. Pure-numeral deltas off a build-verified sibling (G7 mirrors G6 at
7743 jobs); no new bearers, no tactic-structure change. The only residual
risk is a v4.26.0 elaboration regression on the new numerals, which the
targeted build will catch. No parent dependency (imports only Mathlib),
so B1 (broken `LagrangeFourSquares.lean`) does not affect this file.

## Registration

`proofs/Proofs.lean` adds `import Proofs.LagrangeFourSquaresWaringG2OQ01CountingG8`
after the G7 import. Included so the PR is merge-ready immediately after
build-verify; the draft status is the merge gate.

## Honesty block

- **Mathematical progress**: 1 new lower-bound theorem (`g8_lower_counting`),
  sixth verified k-instance of the template — but build-UNVERIFIED.
- **Build-verification status**: ❌ not run (Docker down). Draft until green.
- **Axiom status**: 0 new axioms, 0 sorries (textual; unconfirmed by elaboration).
- **Open conjecture status**: `g(8) = 279` lower bound now formalized
  (pending build); upper bound remains a research-level axiomatic target.
