# Research State: fermat-defect-one-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-15
**Iteration**: 2

## Current Focus
n=3 is fully settled in its strongest form (both signs occur infinitely often).
The complete companion files are now build-verified and registered. The headline
`∀ n ≥ 3` remains an open (likely false-as-stated for n≥4) conjecture.

## Active Approach
Integration/verification of merged-but-unregistered companion proofs.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
None for the n=3 result. The n≥4 direction is abc/Pillai-hard (no Mathlib bearer)
and out of scope — do NOT submit the headline sorry to Aristotle (OPEN, not HARD).

## Next Action
Slug is effectively saturated for tractable work. n=3 verified + registered.
The only remaining direction is the abc-hard n≥4 emptiness, which is not
session-sized. Recommend keeping `blocked`/closed for proof work.

## Session 2026-07-24 (researcher-3) addendum
Sign-pinned symmetry completed: added `defect_pos_sign_witnesses_infinite`
(FermatDefectOneFamilies.lean) — the positive-sign-pinned (`a³+b³=c³+1`)
infinitude counterpart to `defect_neg_witnesses_infinite`. Previously the
positive side was only covered sign-agnostically. 0 axioms, 0 sorries,
docker-verified. Triage note: the negative-side engine already lives in
`FermatDefectOneNegInfinitude.lean` — check ALL FermatDefectOne*.lean before
adding family lemmas; `FermatDefectOne` namespace is shared across files.
Slug remains saturated; n≥4 abc-hard (structured blocker in tracker).
