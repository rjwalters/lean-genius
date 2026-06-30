# Research State: euler-totient-oq-01-oq-03

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-06-15
**Iteration**: 2
**Last Updated**: 2026-06-18 (researcher-11)

## Current Focus
COMPLETE / VERIFIED + MERGED. Verified RSA with the Carmichael function λ(n).
Correctness theorem: for n=p·q (distinct primes) and e·d ≡ 1 (mod λ(n)),
m^(e·d) ≡ m (mod n) for ALL m. Proof = CRT (ZMod(p·q) ≃ ZMod p × ZMod q) +
per-prime Fermat fixed point. Squarefree is necessary (fails for p²).

## Active Approach
None — work is shipped and machine-verified. `EulerTotientOQ01OQ03.lean` (239L,
0 sorry / 0 axiom) and companion `EulerTotientOQ01OQ03Minimal.lean` (54L) are
registered in `proofs/Proofs.lean:2317-2318`; `meta.json` status=verified,
badge=original. Docker build of `Proofs.EulerTotientOQ01OQ03` completed (7744
jobs), first 2026-06-15 and re-verified 2026-06-18 after the constructive
key-generation theorems were added. Build-free certificate `verify_rsa_lambda.py`
all-pass.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
None. Earlier "Docker-gated / UNREGISTERED" blockers are resolved (#24706 merged).

## Next Action
None. Problem is complete and merged. Any further work is optional polish only.
Do NOT re-build/re-prove/pad.

## Iteration log
* **S1** (2026-06-15, researcher-9, ORIENT): RSA-λ correctness theorem + CRT/Fermat
  proof + squarefree necessity; all-pass verifier; sorry-free build-pending Lean.
* **S2** (2026-06-18, researcher-11, RECONCILE): confirmed merged-complete on
  origin/main — both Lean files registered (`proofs/Proofs.lean:2317-2318`),
  0 sorry / 0 axiom, meta verified/original re-verified 2026-06-18, registry
  graduated/COMPLETED (#24706, #24633). Stale ORIENT state.md + candidate-pool
  `in-progress` entry had recycled the slug into the available pool; reconciled
  both to COMPLETED. No Lean changed.
