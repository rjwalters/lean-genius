# Research State: erdos-18-wip-01

## Current State
**Phase**: OBSERVE
**Path**: full
**Since**: 2026-07-09T17:33:19-07:00
**Iteration**: 1

## Current Focus
Initial problem understanding. Read problem.md and gather context.

## Active Approach
None yet.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None.

## Next Action
Read problem.md thoroughly and acquire full context.
Then move to ORIENT phase to explore literature and related proofs.

## Status (researcher-1-9, 2026-07-22) — decide engines + hErdos 24 = 3, hErdos 30 = 4

Phase ACT. Shipped decide-powered exact-value engines (`hErdos_le_of_witnesses`,
`le_repLength_of_card`/`le_hErdos_of_card`) and exact values `hErdos 24 = 3`
(first strict subadditivity: `hErdos(4·6) = 3 < 2+2`, `hErdos_mul_lt_four_six`)
and `hErdos 30 = 4` (first value with no practical factorisation — engines are the
only route). All 0-axiom, host-verified. Deep Vose bound unchanged. See
knowledge.md for the exact-value table and next candidates.

## Status (researcher-1, 2026-07-23) — hErdos 18/20/28 + record-setters: least practical m with index t is 2^t (t ≤ 4)

Phase ACT. Engine session extending the exact table and answering the
minimal-m question the prior session posed (it asked for hErdos 16,18,20,28;
hErdos 16 = 4 was already available via hErdos_two_pow):

- `hErdos_eighteen : hErdos 18 = 3` — engine-only (18 = 2·3² has no practical
  factorisation, like 30); hard target k = 17.
- `hErdos_twenty : hErdos 20 = 4` — UNIQUE hard target k = 18 (10+5+2+1 forced).
  Theory data: 20 < 24 with hErdos 20 = 4 > 3 = hErdos 24 — the index is NOT
  monotone along practical numbers; and d(20) = 6 < 8 = d(24) with the larger
  index on the smaller divisor count.
- `hErdos_twentyeight : hErdos 28 = 4` — hard target k = 27 (14+7+4+2 forced).
- `hErdos_eight`, `hErdos_sixteen` — power-of-two formula specialisations.
- `hErdos_le_three_of_lt_sixteen` — every practical m < 16 has index ≤ 3
  (practicals below 16 are 1,2,4,6,8,12 with indices 0,1,2,2,3,3).
- `minimal_hErdos_two/three/four` — **IsLeast record-setters**: the least
  practical m with hErdos m = t is 2^t for t = 2, 3, 4.

Whether the record-setter is 2^t for ALL t is genuinely open here: it would
follow from hErdos m ≤ log₂ m (practical m), which is NOT greedy-provable —
practical numbers can have consecutive-divisor ratio > 2 (6 → 13 in 78), so the
halving argument breaks. Recorded as a question. Deep Vose bound unchanged.

Same-session addendum: t = 5 closed too — hErdos_thirtytwo = 5,
hErdos_le_four_of_lt_thirtytwo, minimal_hErdos_five (IsLeast ... 32). The
record-setter sequence is proved 2, 4, 8, 16, 32 for t = 1..5.
