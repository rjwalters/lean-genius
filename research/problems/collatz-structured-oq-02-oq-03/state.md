# Research State: collatz-structured-oq-02-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-27T19:00:00-07:00
**Iteration**: 6

## Current Focus
ACT — completed de-risk **component (1)**: the residue-drop engine now AUTO-DERIVES the
parity vector from `(b, r)` for power-of-two moduli (`deriveVec`/`autoDropCert`), so the
caller supplies only the modulus exponent and residue, not a hand-built vector. Built
offline (Docker unresponsive), REAL_EXIT=0, axiom-free (`propext, Quot.sound`; kernel
`decide`, not `native_decide`).

## Active Approach
Deep result stays a single documented axiom (`tao_2019`); the elementary residue-dynamics
core is now a fully turnkey decidable engine. `deriveVec` simulates the affine pair from
`(2^b, r)` reading each forced parity off the constant `d`; `affValidB_deriveVec` proves
the derived vector is unconditionally valid; `autoDropCert_attainsBelow` certifies a
residue family in one `by decide`.

## Attempt Count
- Total attempts: 6
- Approaches tried: statement + explicit families; n≡1 mod 4 family; colMin bridge;
  mod-16/32/128 refinements; general density lemma + decidable `dropCert` (vector supplied);
  **auto-derived parity vector `deriveVec`/`autoDropCert` (this session — no vector supplied)**

## Blockers
- Full proof of Tao (2019) remains BLOCKED (3-adic transport/concentration + Fourier; >> 1000 lines).
- Build host: Docker `docker info` hangs (unresponsive). Verified offline via
  `LAKE_UNSAFE=1 ./bin/lake env lean` against the worktree's cached Mathlib oleans (REAL_EXIT 0).
- **Worktree hazard**: a hard reset (`git reset --hard HEAD`) ran mid-session and wiped
  uncommitted edits. Commit immediately after editing in this worktree.

## Next Action
Remaining genuine lever: a *uniform* drop theorem (one inductive statement covering all
determined classes through the `3^a < 2^b` criterion), then Terras/Korec natural-density-1
stopping time toward Tao's bound. Further dyadic density levels (mod 256+) are diminishing
returns. Tao axiom stays BLOCKED.

## Deliverable (this session)
`proofs/Proofs/CollatzStructuredOQ02OQ03.lean` — Part VII added (1468→1568 lines, 52→54
theorems, 10→12 defs, 1 axiom unchanged, 0 sorries):
- `deriveVec` (auto-derives the residue-determined parity vector from `(b, r)`);
- `affValidB_deriveVec` (the derived vector is unconditionally a valid `AffValid` certificate);
- `autoDropCert` / `autoDropCert_attainsBelow` (one-line residue-family certification from
  `(b, r)` alone), validated on `n≡3 (mod 16)`, `n≡11 (mod 32)`, `n≡7 (mod 128)`.
Verified REAL_EXIT 0 offline; new theorems axiom-free (`propext, Quot.sound`).
