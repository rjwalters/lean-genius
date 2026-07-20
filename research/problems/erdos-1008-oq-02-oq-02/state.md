# Research State: erdos-1008-oq-02-oq-02

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-07-09T16:43:20-07:00
**Iteration**: 3

## Iteration 3 (researcher-1, 2026-07-20, triage — COMPLETED)
Re-served on the RICH depth-first tier. Triage found the problem **saturated and
complete**: `Proofs/Erdos1008OQ02OQ02.lean` is now 1400 lines / 63 theorems /
0 sorries / 0 axioms, covering the full OQ deliverable (parametric
`kst_quadratic_solve`, `kst_root_exact`, `c=1` Reiman specialization, `t`- and
`n`-direction monotonicity) **plus** a general K_{s,t} layer (`HasKst`,
`kst_star_count_*`, `kst_analytic_core`, `kst_general_edge_card_bound`,
`kst_leading_order_ratio_tendsto`). knowledge.md already records "The OQ
deliverable is complete and verified."
Host-verified under v4.31 (`import Mathlib` only): `lake env lean
Proofs/Erdos1008OQ02OQ02.lean` → **EXIT 0**, 0 errors, 0 sorries (only
deprecation / unused-section-variable warnings). No open work remains; marking
`completed` to stop re-serving. No new theorems added (piling onto a saturated
0-axiom file would be enumeration theater).

## Iteration 2 (researcher-9, 2026-07-11, VERIFIED offline)
The parametric K_{2,t} KST machinery in `Proofs/Erdos1008OQ02OQ02.lean` was already
saturated (699L, 0 sorries, 0 axioms, exact nested-radical bound + graph-level +
leading-order + `kst_exact_bound_mono_t`). Added the missing **`n`-direction monotonicity**
of the exact bound (2 axiom-free theorems), the companion to the existing `t`-monotonicity:
- `kst_exact_bound_mono_n (t) (ht:1≤t) {n n'} (hn:1≤n) (hnn':n≤n')`: the Reiman/KST RHS
  `n·(1+√(1+4(t-1)(n-1)))` is non-decreasing in `n` — both leading factor and radicand grow
  (radicand via `(t-1)≥0`), product of nonneg non-decreasing factors. `mul_le_mul`+`Real.sqrt_le_sqrt`+nlinarith.
- `kst_exact_bound_mono (t t') (ht) (htt') {n n'} (hn) (hnn')`: joint monotonicity in both
  `t` and `n`, `le_trans` of mono_n then mono_t.
Both depend only on `[propext, Classical.choice, Quot.sound]` (confirmed `#print axioms`).
File 699→736 lines, +2 theorems, 0 sorries/0 axioms unchanged. Verified `bin/lake env lean` EXIT 0.

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


## Iteration 3 (researcher-1, 2026-07-19, VERIFIED host lean v4.31 exit 0)
Extended the **leading-order asymptotic constant to general `K_{s,t}`, `s ≥ 2`** (the
existing `kst_leading_order_ratio_tendsto` covered only `s = 2`). Added to
`Proofs/Erdos1008OQ02OQ02.lean` (all 0-axiom `[propext, Classical.choice, Quot.sound]`):
- `kstGeneralLeadingBound s t n := ½(t-1)^{1/s}·n^{2-1/s} + ½(s-1)·n` — packaging of the
  `kst_general_edge_card_bound` RHS as a function of `n`.
- `kst_general_edge_card_bound_def` — `m ≤ kstGeneralLeadingBound s t n` restatement.
- `kst_general_leading_order_ratio_tendsto (s t) (hs : 2 ≤ s)`:
  `kstGeneralLeadingBound s t n / n^{2-1/s} → ½(t-1)^{1/s}` as `n → ∞`. The `½(s-1)·n`
  correction contributes `½(s-1)·n^{1/s-1} → 0` since `1/s - 1 < 0` for `s ≥ 2`
  (`tendsto_rpow_neg_atTop`, `y = 1 - 1/s > 0`). Discharges `ex(n; K_{s,t}) ≤
  (½(t-1)^{1/s} + o(1))·n^{2-1/s}` for every `s ≥ 2`; `s = 2` recovers Reiman/KST.

Upper-bound side now complete finite-`n` AND asymptotically for BOTH `K_{2,t}` and general
`K_{s,t}`. **Only the matching lower-bound (Füredi / projective-plane / algebraic) construction
remains open** — genuinely hard, needs incidence-geometry infrastructure not in Mathlib.
