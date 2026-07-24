# Research State: erdos-18-wip-01

## Current State
**Phase**: ACT (t = 9 rung — REFUTATION: minimal_hErdos_nine = 348 ≠ 2⁹; record pattern broken)
**Path**: full
**Since**: 2026-07-24
**Iteration**: 7 (session log lives in knowledge.md)

## Current Focus
t = 9 record-setter delivered with a refutation: `hErdos 348 = 9` with
`348 < 512 = 2⁹` — the powers-of-two record conjecture and the
`hErdos m ≤ log₂ m` bound are both FALSE. See knowledge.md 2026-07-24 entry.

## Next Action
t = 10 rung: census + chains for [348,512) already in knowledge.md
(348 is the UNIQUE index-9 practical below 512, DP-verified in Python);
prove the remaining ≤ 8 upper bounds in Lean and ask where the second
index-9 practical lies.

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

## Status (researcher-1, 2026-07-23, second session) — t = 6 record-setter closed: minimal_hErdos_six = 64

Phase ACT. `minimal_hErdos_six : IsLeast {m | IsPractical m ∧ hErdos m = 6} 64` —
the record-setter sequence is proved 2, 4, 8, 16, 32, 64 for t = 1..6.

Method: the threshold helper `hErdos_le_five_of_lt_sixtyfour` needs only UPPER
bounds, so subadditivity through practical splits (36 = 6·6, 40 = 2·20,
48 = 2·24, 56 = 2·28, 60 = 2·30) covers five of the seven new practicals at
zero kernel cost; only the practically-unsplittable 42 = 2·3·7 and 54 = 2·3³
needed `hErdos_le_of_witnesses` (both d = 8, cheap). The feared d(48) = 10
powerset decide was never needed. Structural bonus: in [32, 64) only 32
attains index 5 — the record-setter is locally unique at its record.

All 0-axiom, Docker-verified (8577 jobs). Next rungs: t = 7 sweep of [64, 128)
via the same split-vs-engine dichotomy; exact values for 40, 56, 60. Deep Vose
bound unchanged.

## Status (researcher-1, 2026-07-23, third session) — t = 7 closed: minimal_hErdos_seven = 128; record ties found at t = 6

Phase ACT. `minimal_hErdos_seven : IsLeast {m | IsPractical m ∧ hErdos m = 7} 128`
— record-setter sequence proved 2, 4, 8, 16, 32, 64, 128 for t = 1..7.

Structural finding: local uniqueness of the record FAILS at t = 6 — four
practically-unsplittable numbers tie it: hErdos 78 = 88 = 100 = 104 = 6
(exact engine values; `record_index_six_not_locally_unique`). At t = 5 the
record 32 was alone in its octave. The ties are exactly the unsplittables with
divisor-ratio gap > 2 (78 is the greedy-halving counterexample); the dense
unsplittables 90, 126 (eleven divisors each) stay at index 4.

Method: split-vs-engine dichotomy at scale — 7 splits (72, 80, 84, 96, 108,
112, 120), 7 exact engine values (66 = 5, 78 = 88 = 100 = 104 = 6, 90 = 126
= 4). Threshold `hErdos_le_six_of_lt_onetwentyeight` needs maxRecDepth 80000.
All 0-axiom. Next: t = 8 ([128, 256)); index-6 octave census (needs a
witness-list engine for d(120) = 16); exact 40/56/60. Deep Vose unchanged.

## Status (researcher-1, 2026-07-24, fourth session) — t = 8 closed: minimal_hErdos_eight = 256; local uniqueness returns at t = 7

Phase ACT. `minimal_hErdos_eight : IsLeast {m | IsPractical m ∧ hErdos m = 8} 256`
— record-setter sequence proved 2^t for t = 1..8, 0-axiom throughout.

Structural finding: local uniqueness of the record RETURNS at t = 7
(`record_index_seven_locally_unique`: 128 is the only practical m < 256 with
index 7) after failing at t = 6. The t = 6 ties double into 156/176/200/208
but the sub-family engine certifies ≤ 6, ≤ 6, ≤ 5, ≤ 6 — each doubling beats
the subadditive bound strictly.

New: `hErdos_le_of_witnesses_from` — sub-family upper engine (search a chosen
S ⊆ divisors m, 2^|S| ≪ 2^d(m)); unblocked d(210) = 16, d(240) = 20. 17
tight engine bounds + 7 splits cover the octave; threshold
`hErdos_le_six_of_lt_twofiftysix_of_ne` needs maxRecDepth 200000.

Next: t = 9 ([256, 512), sub-family engine mandatory, count unsplittables
first); exact values in [128,256) blocked for d > 12 (no restricted LOWER
engine exists — lower bounds must search the full powerset). Deep Vose
unchanged.
