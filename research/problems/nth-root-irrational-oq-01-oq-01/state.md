# Research State: nth-root-irrational-oq-01-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-15T00:57:04-07:00
**Iteration**: 5

## Current Focus
Cyclotomic / real-subfield irrationality is COVERED across S1–S4 (all merged but
left UNREGISTERED in Proofs.lean). This session registers the four completed
files so the import manifest includes them.

## Active Approach
Registration-only (build-free; Docker + Aristotle blackout). Added to
`proofs/Proofs.lean`, after personally name-checking each file (0 sorry/0 axiom,
standard v4.26 Mathlib identifiers):
- `NthRootIrrationalOQ01OQ01`       (S1 #24349) — cyclotomic roots not rational; rational roots of unity = ±1.
- `NthRootIrrationalOQ01OQ01Real`   (S2 #24403) — ζ+ζ⁻¹ = 2cos(2π/n) irrational for φ(n)≥3 (abstract).
- `NthRootIrrationalOQ01OQ01Cos`    (S3 #24427) — Niven: Irrational(cos(2π/n)) for φ(n)≥3.
- `NthRootIrrationalOQ01OQ01CosRational` (S4 #24466) — rational half: cos(2π/n) rational iff n∈{1,2,3,4,6}.

## Attempt Count
- Total attempts: 5
- Current approach attempts: 1
- Approaches tried: 2

## Blockers
- Docker + Aristotle blackout: cannot locally build to confirm; registration is
  deployer-build-gated (a failing build blocks the merge, not main).

## Next Action
On a Docker-up session: `docker-build.sh Proofs.NthRootIrrationalOQ01OQ01{,Cos,CosRational,Real}`;
fix any v4.26 drift. Genuinely-open remaining direction: the explicit degree
φ(n)/2 minimal polynomial of 2cos(2π/n) (the full real-subfield minpoly), beyond
the divisibility/degree bound used in the Real/Cos files.
