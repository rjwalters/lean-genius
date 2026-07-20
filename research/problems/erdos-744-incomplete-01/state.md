# Current State

**Phase**: COMPLETED (served task) — bipartitionNumber sorry resolved upstream

**Since**: 2026-07-08
**Iteration**: 2

## Current Focus

Served slug (complete the `bipartitionNumber` definition-sorry) is already done
(PR #27334). No code change this session.

## Active Approach

None — phantom-complete. Recorded an integrity finding: the remaining
`rodl_tuza_theorem` axiom is trivially provable against the hardcoded placeholder `f`,
so converting it would overclaim `verified`. Left for mechanic/peer-reviewer.

## Blockers

Genuine Erdős #744 formalization needs `f` redefined as the true extremal min over
k-critical graphs + the deep Rödl–Tuza asymptotic (not in Mathlib). > 1000 LOC.

## Next Action

Mechanic/peer-reviewer decision on `f` redefinition vs axiom relabel. No researcher
action tractable without k-critical-graph infrastructure.

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 1
- Approaches tried: 1

## Session 2026-07-19 (researcher-1) — integrity finding + v4.31 clean re-verify

**Integrity finding (the important part).** The central function `f k n` in
`Erdos744Problem.lean` is a **placeholder**: it hardcodes the Rödl–Tuza value
`(k-1)(k-2)/2` and is *constant in `n`*, rather than the intended
`min { bipartitionNumber G : G k-critical on n vertices }`. Because of this:

- `axiom rodl_tuza_theorem` is **tautological** — provable by `unfold f` with
  `N₀ = 0`. It carries none of the real 1985 combinatorics content.
- `erdos_conjecture_false` and `erdos_744_statement` are **vacuous** with respect
  to the genuine `f_k(n)`.

The file is definitional theater, not a genuine formalization of #744. (The gallery
`meta.json` already, correctly, labels it `axiomatized` / `badge: axiom`.)

**Action taken (anti-laundering).** Added prominent in-file INTEGRITY WARNINGs on
`def f` and `axiom rodl_tuza_theorem` explicitly forbidding a future agent from
discharging the axiom via `unfold f` to claim "0-axiom verified" — that would
launder a stub into a false verification. Registered the genuine gap as a
structured `currentState.blockers` entry and corrected the tracker's prior
"COMPLETE" overclaim.

**v4.31 re-verify + clean** (host, `lake env lean`, EXIT 0, now zero warnings):
cleared 5 deprecations (2× `push_neg`→`push Not`; 3× `Finset.filter_card_add_filter_neg_card_eq_card`→`Finset.card_filter_add_card_filter_not`) and 2 unused-variable
lints. File previously built only under v4.26. Axiom/sorry counts unchanged (1 / 0).

**Pool status → `blocked`** (genuine formalization is deep-blocked on the real
Rödl–Tuza bound, absent from Mathlib).
