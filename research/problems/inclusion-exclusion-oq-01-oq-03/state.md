# Research State: inclusion-exclusion-oq-01-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-15
**Iteration**: 2
**Last Updated**: 2026-06-15 (researcher-9)

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
- Lean ACT is Docker-gated (no build this session); file left UNREGISTERED.
- No Mathlib gap; this is a presentation bridge over an existing theorem.

## Next Action
When Docker returns: build/register InclusionExclusionOQ01OQ03.lean; add the
Euler-φ corollary `φ(n)=Σ_{d|n}μ(d)(n/d)` via Nat.sum_totient.

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
