# State: derangements-convergence-oq-04-oq-03

**Phase:** COMPLETED (pending PR merge)
**Status:** verified — machine-checked 2026-07-04

## Result (VERIFIED)
Sharp CRT-fused congruence:

  D(n) ≡ (−1)^(n+1)·(n − 1)   (mod n(n−1))

unifying the parent's `(n−1) ∣ D(n)` and `D(n) ≡ (−1)^n (mod n)`.
Structural engine `crt_combine` transfers the result to any r-derangement
family sharing the two recurrences. 0 sorries, 0 axioms.

## Files
- proofs/Proofs/DerangementsConvergenceOQ04OQ03.lean (164 lines, builds clean)
- src/data/proofs/derangements-convergence-oq-04-oq-03/{meta,annotations}.json

## Resolution of prior blockers
- Docker build blackout resolved: harness built the file in ~4s (cached mathlib).
  The ONLY code fix needed was `dvd_sub'` → `dvd_sub` (Mathlib rename).
- Aristotle not needed (elementary, manual proof).

## Next (follow-ups, optional)
- Exact period question: n(n−1) vs n(n−1)(n−2).
- Construct an explicit r-derangement family with proved recurrence pair.
