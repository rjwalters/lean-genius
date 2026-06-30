# Research State: inclusion-exclusion-oq-01-oq-03

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-06-15
**Iteration**: 3
**Last Updated**: 2026-06-15 (researcher-1 — BUILD GREEN, verified)

## Current Focus
Classical (divisor-form) Möbius inversion `f(n)=Σ_{d|n}g(d) ⟺ g(n)=Σ_{d|n}μ(d)f(n/d)`.
Mathlib already proves it in ANTIDIAGONAL form (sum_eq_iff_sum_mul_moebius_eq);
contribution is the textbook divisor-sum presentation via Nat.sum_divisorsAntidiagonal.

## Active Approach
Build-free ORIENT (Docker + Aristotle blackout). All-pass verifier
verify_moebius_inversion.py (both directions, μ sanity, φ anchor). Build-pending
UNREGISTERED Lean theorem moebius_inversion_divisors bridging the two Mathlib lemmas.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
- None. Build verified GREEN this session (quiet window, 1 peer build).

## Next Action
**DONE — verified.** `docker-build.sh Proofs.InclusionExclusionOQ01OQ03` completed
successfully (3058 jobs, 0 err, ~8.4s for our module after cache get). Flipped gallery
`meta.json` status formalized→verified, badge wip→verified; registry → completed. The
prior S-verify OOM was pure contention (5 concurrent builds); at 6 GB cap in a quiet
window the build is trivial.

## Iteration log
* **S1** (2026-06-15, researcher-9, ORIENT): identified Mathlib's antidiagonal
  Möbius inversion + the Nat.sum_divisorsAntidiagonal bridge; build-pending
  textbook-form theorem; all-pass verifier.

* **S-verify** (2026-06-15, researcher-4, ACT/verify): Docker UP; ran
  single-file `docker-build` twice — both OOM-killed at 32 GB during Mathlib
  dependency phase under heavy concurrent-build contention (host ~25 GB free,
  5 lean-build containers). Could not produce a green build ⇒ left status
  `formalized`/`wip` (no overclaim to `verified`). OQ complete + registered;
  meta/annotations covered by enricher PR #24637. Retry build in a quiet window.

* **S3** (2026-06-15, researcher-1, ACT/verify): **BUILD GREEN.** Quiet window (1
  concurrent build vs S-verify's 5). `LEAN_MEMORY_LIMIT=6144 docker-build.sh
  Proofs.InclusionExclusionOQ01OQ03` → "Build completed successfully (3058 jobs)",
  our module built in 8.4s after `lake exe cache get`. Flipped gallery meta
  status formalized→verified, badge wip→verified; registry → completed. Confirms
  S-verify's diagnosis that the prior OOM was contention, not the proof.
