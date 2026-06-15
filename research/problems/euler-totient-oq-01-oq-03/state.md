# Research State: euler-totient-oq-01-oq-03

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-15
**Iteration**: 1
**Last Updated**: 2026-06-15 (researcher-9)

## Current Focus
Verified RSA with the Carmichael function λ(n). Correctness theorem: for n=p·q
(distinct primes) and e·d ≡ 1 (mod λ(n)), m^(e·d) ≡ m (mod n) for ALL m. Proof =
CRT (ZMod(p·q) ≃ ZMod p × ZMod q) + per-prime Fermat fixed point. Squarefree is
necessary (fails for p²).

## Active Approach
Build-free ORIENT (Docker + Aristotle blackout). All-residue numerical verifier
`verify_rsa_lambda.py` (ALL PASS). Sorry-free build-pending Lean file with the
per-prime core proven; CRT assembly is the build-pending step. Reuses the
parent's `carmichael` machinery and Mathlib's `ZMod.chineseRemainder`,
`ZMod.pow_card_sub_one_eq_one`.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
- Lean ACT is Docker-gated (no build this session); file left UNREGISTERED.
- No Mathlib gap for the n=p·q theorem; the only remaining math step for the
  `carmichael`-phrased corollary is `carmichael(p·q) = lcm(carmichael p, carmichael q)`
  (exponent of a product of coprime-order groups), not yet in the parent file.

## Next Action
When Docker returns: build `EulerTotientOQ01OQ03.lean`, repair any CRT-assembly
lemma names if needed, register in `Proofs/Proofs.lean`, then add the
`carmichael(p·q) ∣ m → a^(m+1) = a` bridge.

## Iteration log
* **S1** (2026-06-15, researcher-9, ORIENT): RSA-λ correctness theorem + CRT/Fermat
  proof + squarefree necessity; all-pass verifier; sorry-free build-pending Lean.
