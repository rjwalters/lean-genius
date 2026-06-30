# Research State: divisibility-by-three-oq-01-oq-01

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-13
**Iteration**: 2

## Current Focus
SURVEY complete. The OQ ("automated tactic generating + verifying divisibility rules
for arbitrary d coprime to base b") is mostly already solved at the theorem level in
the gallery. Two concrete remaining pieces identified; both are build-gated.

## Active Approach
Resolve the OQ via existing gallery machinery + two additions:
- **Gap A**: `unified_osculator_base_b` — port the proven base-10 `unified_osculator`
  (`DivisibilityTruncationGeneralOQ01.lean`) to arbitrary base `b`. Mechanical (~15 lines);
  same identity `b·(n/b + c·(n%b)) = n + (b·c−1)·(n%b)`.
- **Gap B**: a `divisibility_rule b d` tactic (elab/macro) that computes the osculator
  `c = b⁻¹ mod d` (extended Euclid) or the period `k` (least k>0 with b^k%d=1), emits
  `unified_osculator_base_b` / `digit_block_rule_base_b`, and discharges side goals by
  `native_decide`.

Prior art already present:
- `DivisibilityRulesOQ01OQ01OQ01.lean` — `digit_block_rule_base_b`,
  `period_iff_orderOf_dvd_base_b`, `orderOf_base_b_is_minimal_period` (digit-block rule
  ALREADY general in base b).
- `DivisibilityTruncationGeneralOQ01.lean` — `unified_osculator`,
  `neg_osculator_from_unified` (osculator rule, base 10).

## Attempt Count
- Total attempts: 0 (survey only; no proof attempts)
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- **Build-gated (verification blackout, 2026-06-13).** Both Gap A and Gap B need a
  Docker `lake build` to confirm they compile (the tactic especially). Docker daemon
  down (`docker info` exit 124) and Aristotle backend 404 — both confirmed live this
  session. No Lean committed.

## Key insight
`orderOf (b : ZMod d)` is noncomputable, so the tactic cannot evaluate the period
directly. It must search for the least `k>0` with `b^k % d = 1` externally and discharge
`orderOf (b:ZMod d) ∣ k` via `period_iff_orderOf_dvd_base_b … (by native_decide)`. This
witness-and-verify pattern is already used by hand in the gallery
(`DivisibilityRulesOQ01OQ01OQ01.lean:150–165`).

## Next Action
When Docker recovers: implement Gap A (`unified_osculator_base_b`) first as the clean
build milestone, then Gap B (the `divisibility_rule` tactic). See knowledge.md for the
full design.
