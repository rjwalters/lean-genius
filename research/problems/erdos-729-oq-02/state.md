# Research State: erdos-729-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-15
**Iteration**: 2

## Current Focus
OQ-02 resolved: `legendre_for_two` ($v_2(n!) = n - s_2(n)$) is now proved
axiom-free from Mathlib's `sub_one_mul_padicValNat_factorial`. The
`legendre_identity` axiom has been deleted (file axiom count 4 → 3).

## Active Approach
Direct application of Mathlib's Legendre theorem at $p = 2$, plus a strong-induction
bridge `digitSum_eq_digits_sum` from the file's recursive digit sum to
`(Nat.digits p n).sum`.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
Docker build wrapper unavailable this session (blackout). Proof shipped
build-pending after full name-check against sibling mathlib4 v4.26.0.
Sole at-risk line: `rw [digitSum.eq_def, if_neg hn]` (wf-def unfold idiom).

## Next Action
Build-verify when Docker returns:
`./proofs/scripts/docker-build.sh Proofs.Erdos729Problem`.
Remaining axioms (Erdős 1968, Barreto–Leeham) are the genuinely deep open math,
out of scope for OQ-02.
