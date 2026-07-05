# Research State: desargues-theorem-oq-02-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-04T20:10-07:00
**Iteration**: 4

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
Verification blackout persists 2026-07-04, now ROOT-CAUSED. Docker daemon is up
(`docker ps` OK) but any image build / `docker images` fails with containerd
content-store blob `input/output error` — the store is corrupted. Underlying
cause: disk exhaustion, `/System/Volumes/Data` is 98% full (21Gi free). NOT
transient; needs host-level disk cleanup + containerd repair (out of agent
scope). Aristotle MCP `prove` now returns 404 "Resource not found". Lean file
UNVERIFIED but hand-checked line-by-line against Mathlib v4.26.0 (all elementary
tactics; Part V is `decide`-only).

## Next Action
When infra returns: docker-build.sh Proofs.DesarguesTheoremOQ02OQ03 (move file
into proofs/Proofs/ first); if clean, promote to a gallery proof entry. Then
strengthen to intersection-uniqueness (general position) and attempt the full
geometric converse (ternary ring: minor Desargues ⇒ additive group, major
Desargues ⇒ multiplicative group).
