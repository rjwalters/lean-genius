# Research State: desargues-theorem-oq-02-oq-03

## Current State
**Phase**: REFLECT
**Path**: full
**Since**: 2026-07-04T20:10-07:00
**Iteration**: 5

## Session 5 (researcher-8): VERIFIED
The build blackout is over. The Lean file now **builds cleanly via Docker**
(Lean v4.26.0, `./proofs/scripts/docker-build.sh Proofs.DesarguesTheoremOQ02OQ03`,
7743 jobs, 0 errors/warnings, 0 `sorry`, 0 `axiom`, 0 `native_decide`). Two
build-blocking elaboration bugs were fixed: `Dep`'s ring `R` appears only inside
its `∃`-binder, so a bare `Dep (a-b) (b-c) (c-a)` left `Module ?R M` stuck — `R`
is now pinned `(R := R)` in the statements of `cross_dep` and `desargues`. The
hand-checked math was sound; only these annotations were needed. Status upgraded
from UNVERIFIED → verified.

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
A build-attempt copy already exists at `proofs/Proofs/DesarguesTheoremOQ02OQ03Verify.lean`
(UNTRACKED — mathematically identical to the research/ version; kept so any
future healthy-infra session can `docker-build.sh Proofs.DesarguesTheoremOQ02OQ03Verify`
instantly). It MUST NOT be committed to the gallery glob while UNVERIFIED — an
unverified file under `proofs/Proofs/` risks breaking the gallery build. When
infra returns: (1) build that Verify target; (2) if clean, promote to a gallery
proof entry and only THEN commit it into `proofs/Proofs/`. Then strengthen to
intersection-uniqueness (general position) and attempt the full geometric
converse (ternary ring: minor Desargues ⇒ additive group, major Desargues ⇒
multiplicative group).
