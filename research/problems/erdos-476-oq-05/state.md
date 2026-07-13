# Research State: erdos-476-oq-05

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-15T15:38:43-07:00
**Iteration**: 3

## Current Focus
`ap_sdiff_endpoint` is now PROVEN (verified standalone, 0/0). Remaining open work
in `Erdos476OQ05Aristotle.lean`:
- line ~287 (case1_exists `|B|≥3` branch): Dyson e-transform induction `sorry`.
- **PRE-EXISTING ROT in `case1_exists`** (file never built at HEAD; confirmed by
  building HEAD baseline this session). Six sites, independent of any new work:
  - `Nat.inf_eq_min` removed from mathlib — `simp only [Nat.inf_eq_min]` (~L171).
    Fix: `inf_of_le_right (show … ≤ p by omega)`.
  - genuine gap: `non_redundant_b_gives_a` needs `A.card+B.card < p` but caller only
    has `A.card+B.card-1 < p` (could be `=p`) (~L179).
  - `▸`-on-`Ne` (`(hall a haA).symm ▸ …`, ~L161) → use `have hne := hall a haA; omega`.
  - `eq_sub_of_add_eq` type mismatches (~L233, L242) → add `.symm`/reorder.

## Active Approach
Iteration 3 (this session): hand-proved the corrected `ap_sdiff_endpoint` as a
standalone companion (rescale by d⁻¹ → intervals mod p → wrap/no-wrap residue
count). Docker build-green v4.26 (7743 jobs). PR #30476.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
- `case1_exists` pre-existing rot (above) blocks a full green build of the parent
  Aristotle file → wiring (import + 1-line delegation) of the proven
  `ap_sdiff_endpoint` is deferred until that rot is repaired. The delegation itself
  was confirmed to elaborate cleanly (cross-namespace `IsArithmeticProgression`
  are defeq; the only errors in the wired build were the pre-existing case1 ones).
- Docker VM cap = 23.4 GB: inlining the ~110-line proof into the (Cauchy-Davenport)
  parent OOMs at 20 GB. Keep it in a separate compilation unit (per-module memory).

## Key Finding (this session)
`ap_sdiff_endpoint` was stated with `0 < AP₁.card`, which makes it **FALSE**.
Counterexample (p=7, d=1): AP₂={0,1,2}, AP₁={4}. Then (AP₁\AP₂).card=1, n+m≤p,
but s₁=4 is neither s₂−d=6 nor s₂+(m−n+1)d=3. Corrected hypothesis: `2 ≤ AP₁.card`.
Full correct proof blueprint (d⁻¹-rescale to intervals mod p, wrap/no-wrap val split)
is inlined as a comment above the sorry. The lemma is currently unused (it is intended
support for the line-269 Dyson e-transform step), so the hypothesis strengthening is safe.

## Next Action
1. DONE (iter 3): `ap_sdiff_endpoint` proven + verified standalone (PR #30476).
2. Repair the pre-existing `case1_exists` rot (4 fixes listed under Current Focus) —
   mechanic-style, but watch the genuine `A.card+B.card<p` gap at ~L179 (may need a
   real argument, not a mechanical patch). After green, wire `ap_sdiff_endpoint` in
   via `import Proofs.Erdos476OQ05APEndpoint` + a 1-line delegation at the L132 sorry.
3. Then attack the Dyson e-transform induction sorry (~L287; blueprint in knowledge.md).
Do NOT re-submit the original `0 < AP₁.card` form — it is FALSE (n=1 counterexample).
