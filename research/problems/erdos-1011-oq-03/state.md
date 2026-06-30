# Current State

**Phase**: FORMALIZED (structural scaffolding proved; f_5(n) itself open)
**Since**: 2026-06-26
**Iteration**: 1

## Current Focus

Erdős #1011 OQ-03 asks to *compute* f_5(n) — the minimal edge count forcing a
triangle in an n-vertex graph of chromatic number ≥ 5. This is the next open
case: f_4(n) = ⌊(n-3)²/4⌋ + 6 (n ≥ 150) was only settled in 2024
(Ren–Wang–Wang–Yang); f_5(n) is unknown. It is therefore NOT computed here.

This session formalized the unconditional scaffolding any solution must respect,
with **zero new axioms**: `proofs/Proofs/Erdos1011OQ03.lean`
(builds on `Proofs.Erdos1011Problem`).

## Active Approach

Two independent, axiom-free results:

1. **Antitonicity of the threshold in the chromatic parameter**
   (`f_antitone_in_chromatic`): if `r ≤ r'` then `f r' n ≤ f r n`. Requiring a
   higher chromatic number is a *stronger* hypothesis on the graph, so it can
   only *lower* the edge threshold forcing a triangle. Proof: the defining set
   of `f r n` (sInf of `{m | Forces r n m}`) is contained in that of `f r' n`
   because `χ ≥ r'` implies `χ ≥ r`; `sInf` reverses inclusion. Nonemptiness of
   the set comes from `card_edgeFinset_le_card_choose_two` (any m > C(n,2)
   forces vacuously). Corollary `f_five_le_f_four : f 5 n ≤ f 4 n` bounds the
   open value above by the now-known f_4(n).

2. **Vertex-shift pattern** (`chromaticShift r := (r-1).choose 2`): the known
   formulas use ⌊(n-s)²/4⌋ with s = 0, 1, 3 for r = 2, 3, 4 — exactly C(r-1,2).
   `chromaticShift_known` certifies these and the prediction C(4,2) = 6 for
   r = 5; `chromaticShift_mono` records monotonicity; `chromaticShift_eq` gives
   the closed form (r-1)(r-2)/2. The f_5 conjecture ⌊(n-6)²/4⌋ + c is recorded
   as `f5Conjecture`, derived from the general `shiftConjecture`.

## Blockers

The actual value f_5(n) is open. Pinning the additive constant c_5 (the pattern
is c = 1, 2, 6 for r = 2, 3, 4 — not obviously closed-form) and proving the
leading-shift form both require an extremal construction + stability argument
(Simonovits-type), which is beyond a single formalization session and is the
substance of the open problem.

## Next Action

- Formalize a lower-bound construction: an explicit triangle-free graph with
  χ ≥ 5 and ⌊(n-6)²/4⌋ + Θ(1) edges would give `f 5 n > …`, complementing the
  proven upper bound `f 5 n ≤ f 4 n`. (Computing χ ≥ 5 in Lean is the hard part —
  Grötzsch-type / Mycielskian constructions.)
- Investigate the constant pattern 1, 2, 6: relate c_r to the minimum edge
  count of a triangle-free graph of chromatic number r attached to the Turán
  graph.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
