# Research State: desargues-theorem-oq-02-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-04T20:10-07:00
**Iteration**: 5
**Status**: VERIFIED (2026-07-04, session 7, researcher-14) — machine-checked,
0 sorry / 0 axiom / 0 native_decide.

## Session 7 (researcher-14) — VERIFIED + blackout bypassed
The verification blackout was BYPASSED, not waited out. Root diagnosis refined:
the 98%-full host disk corrupted only the Mathlib `.ltar` download cache and
`.trace` metadata — the extracted `.olean` artifacts are intact. So building with
**`LEAN_SKIP_CACHE=true ./proofs/scripts/docker-build.sh <target>`** skips the
failing `lake exe cache get` decompression and compiles directly against the good
oleans. This is the standing fleet-wide workaround while the host disk stays full
(Aristotle MCP still 404, independent channel).

That build surfaced three REAL compile errors the prior hand-check missed:
`Dep`'s implicit `R` occurs only inside its `∃ a b c : R` binder, so at the
argument-only call sites in `cross_dep` and in `desargues`'s return type Lean
could not infer `R` (`Module ?R M` stuck); `desargues` then failed to elaborate,
so the Part IV quaternion `example` reported `desargues` as an unknown identifier.
Fix: pin `Dep (R := R)` at both sites. After the fix:
`✔ Built Proofs.DesarguesTheoremOQ02OQ03Verify` (reproduced 2/3 runs; one SIGBUS
exit-135 was transient disk-pressure flake). File promoted into the gallery glob
at `proofs/Proofs/DesarguesTheoremOQ02OQ03Verify.lean` and the research copy
synced to match. Lesson: "hand-checked line-by-line" ≠ verified — the elaboration
bug was invisible to reading.

## Current Focus
Forward direction formalized (division ring ⇒ Desargues, commutativity unused).
Session 3 added the **algebraic converse hinge**: the forward proof's sole use of
invertibility (`smul_ne_zero'`) is proved *equivalent* to `R` having no zero
divisors, with the explicit failure exhibited when a zero divisor exists. This
closes the iff at the exact algebraic spot; the full geometric converse (Hilbert
coordinatization) remains deferred as a large multi-session task.

Session 4 (researcher-6) made the dichotomy **non-vacuous with concrete finite
witnesses** (Part V): `ZMod 6` (a non-domain, `2*3=0`) realizes the negative side
— `smul_ne_zero'` provably fails and `zero_divisor_breaks_normalization` fires on
explicit numbers — while `ZMod 5` (a field) realizes the positive commutative
side. With the Quaternion example (non-commutative division ring) this spans the
full classification. All four Part-V facts are `decide`-checked, so they are the
one self-certifying part of the file even under the build blackout.

## Active Approach
Linear-algebra / coordinate proof (approach 1 of problem.md), scalars kept on the
left throughout so non-commutativity is a non-issue. Converse hinge reads `R` as a
module over itself (the coordinate line).

## Attempt Count
- Total attempts: 3
- Current approach attempts: 3
- Approaches tried: 1

Session 5 (researcher-14, iter 4): fixed a build-blocking elaboration bug in the
Part IV quaternion `example` — `R` was unpinned on both `Dep` and `desargues`, so
`Dep`'s implicit `R` (appearing only inside its `∃`-binder) could not be inferred
and `Module ?R (Fin 3 → Quaternion ℝ)` failed to synthesize. Pinned
`(R := Quaternion ℝ)` on both. Kept the richer `ZMod 6`/`ZMod 5` Part-V witnesses
from main. Re-tested infra: BOTH channels still down (details below).

## Blockers
Verification blackout persists but its SHAPE CHANGED as of 2026-07-05
(researcher-14, session 6). The containerd content-store corruption is GONE:
`docker run lean4-arm64:v4.26.0` executes, `docker image inspect` succeeds, and
`docker-build.sh` now proceeds all the way into `lake exe cache get` (downloads
all 7727 mathlib cache files from Azure). The failure has moved DOWNSTREAM to
cache extraction: dozens of `/root/.cache/mathlib/*.ltar: expected value at line
1 column 1` errors → `leantar failed with error code 1` during "Decompressing
7727 file(s)". "expected value at line 1 column 1" = the downloaded `.ltar`
files hold non-ltar content (empty / error-page / truncated), so the archives
are corrupt at rest. This recurs IDENTICALLY at 11Gi AND at 24Gi free — so it is
not purely instantaneous free-space at the `df` endpoints; likely the host disk
(still 98–99% full, churned by concurrent agents) momentarily hits 100% during
the ~90s download window and truncates writes, or the CDN returns bad content.
Either way it is host-level (disk cleanup / cache re-seed), out of agent scope.
`docker builder prune -f` freed 3.97GB but net free space DROPPED (other agents
consume it as fast) — confirming systemic host disk pressure. Aristotle MCP
`prove` STILL returns 404 "Resource not found" (independent channel, also down).
Lean file UNVERIFIED but hand-checked line-by-line against Mathlib v4.26.0 (all
elementary tactics; Part V is `decide`-only). Fleet-wide implication: verification
is blocked for ALL researchers until host disk is freed (target <90%) and/or the
mathlib cache volume is re-seeded; containerd repair is NO LONGER needed.

## Next Action
DONE (session 7): the Verify target builds clean and is now committed into
`proofs/Proofs/DesarguesTheoremOQ02OQ03Verify.lean` (verified gallery proof).
Remaining follow-ups for a future session:
  1. Add a gallery data entry `src/data/proofs/desargues-theorem-oq-02-oq-03/`
     (meta.json: status `verified`, badge `verified`/`original`, axiomCount 0,
     link to Moulton-plane counterexample `desargues-theorem-oq-02`) so the
     result surfaces on the site — verify `pnpm build` afterward.
  2. Strengthen to intersection-uniqueness (general position).
  3. Attempt the full geometric converse (ternary ring: minor Desargues ⇒
     additive group, major Desargues ⇒ multiplicative group).
