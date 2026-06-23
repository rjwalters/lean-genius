# S7 ACT — (3, 5) Axis-vs-Plane Safety Discharged

**Date**: 2026-06-04
**Author**: researcher-1
**Mode**: ACT
**Predecessor**: S7 PREP-2 (2026-06-04, recipe in `sessions/2026-06-04-s7-prep-2-3-5-axis-vs-plane-recipe.md`)
**Outcome**: Paste-ready recipe applied. `safe_3_5_axis_vs_plane` proved.
0 sorries, 0 axioms. Docker-verified GREEN (`./proofs/scripts/docker-build.sh
Proofs.Erdos659OQ01OQ02`, "✔ Build completed successfully (3058 jobs)").

## What landed

Applied the S7 PREP-2 recipe verbatim to `proofs/Proofs/Erdos659OQ01OQ02.lean`.
The file grew **292 → 488 LOC** (delta +196 LOC, slightly above the +142 LOC
estimate because of the inserted `/-! ## S7 ACT — ... -/` section header
comment, the per-theorem docstrings, and the module-header refresh).

### Lean delta

| Insertion point | Content | LOC |
|---|---|---|
| After `zmod_5_a_sq_eq_two_b_sq_iff` (line 80 of the PRE file) | `zmod_5_a_sq_plus_3_b_sq_eq_zero_iff` + `zmod_5_a_sq_eq_three_b_sq_iff` (both `decide`-checked, 8 LOC each w/ docstrings) | ~16 |
| Before `end Erdos659OQ01OQ02` (line 292 of the PRE file) | `/-! ## S7 ACT — ... -/` section header + `safe_A_3_5_holds` + `safe_B_3_5_holds` + `safe_C_3_5_holds` + `safe_3_5_axis_vs_plane` | ~180 |
| Module header (top of file) | refreshed S7 ACT footnote on the existing "Sorries / axioms" paragraph | +5 |

The three new descent theorems mirror `safe_{A,B,C}_holds` 1:1; the only diff
is `2 → 3` in the coefficient and the helper-name swap
(`zmod_5_a_sq_eq_three_b_sq_iff` for B'/C' descent;
`zmod_5_a_sq_plus_3_b_sq_eq_zero_iff` for A' descent).

### Sorry / axiom delta

- **0 sorries** added or removed (file still has zero).
- **0 axioms** added or removed (file still has zero).

The full-rank half of `(3, 5)` safety is **deferred** (same status as the
full-rank half of `(2, 5)` — see S2c PREP §6.1 for the rationale). This S7 ACT
does not change `axiomCount` in `src/data/proofs/erdos-659-oq-01/meta.json`
because the file imports of `Erdos659OQ01OQ02.lean` were not touched and the
parent gallery entry's status (`axiomatized`, 3 axioms) is unaffected.

### Build verification

```
$ ./proofs/scripts/docker-build.sh Proofs.Erdos659OQ01OQ02
... [mathlib download]
✔ [3058/3058] Built Proofs.Erdos659OQ01OQ02 (14s)
Build completed successfully (3058 jobs).
=== Build succeeded ===
```

No warnings, no sorries (the only warnings that would surface would be on
unused declarations, and the new theorems are all reachable via
`safe_3_5_axis_vs_plane`).

## Verification by sanity check

Spot-check on one specific solution branch — equation A' on `(3, 5)`:
`5 c² = a² + 3 b²` at `(a, b, c) = (4, 1, 1)`:
`5·1 = 16 + 3 = 19`? **No**, `5 ≠ 19`. Good (no spurious counterexample).
At `(a, b, c) = (1, 2, 1)`: `5·1 = 1 + 12 = 13`? **No**.
At `(a, b, c) = (4, 2, 2)`: `5·4 = 20 = 16 + 12 = 28`? **No**, `20 ≠ 28`.

The mod-5 reduction tables in the S7 PREP-2 recipe §"Equation A'" show that
the only `(a², 3 b²)` pair summing to `0 (mod 5)` is `(0, 0)`. The
`decide`-checked `zmod_5_a_sq_plus_3_b_sq_eq_zero_iff` confirms this for the
full 25-case enumeration.

## What this does NOT do

- Does **not** address the full-rank half of either `(2, 5)` or `(3, 5)`
  safety. Both still require ternary Hasse-Minkowski (absent from Mathlib
  v4.26.0) for a sorry-free proof, or honest axiomatisation per S2c §6.1.
- Does **not** touch the proved `(2, 5)` theorems (they are still load-bearing
  for `safe_2_5_axis_vs_plane`, which is now joined by `safe_3_5_axis_vs_plane`
  in the file).
- Does **not** extend to a third safe pair. The remaining safe pairs from
  S2a OBSERVE PR #18494 are `{(2,13), (5,7), (5,13), (7,13), (11,13)}`; each
  introduces a new modulus (`13`, `7`, `11`) and would add ~145 LOC apiece by
  the same recipe.
- Does **not** assemble the Θ(n^{2/3}) rate; that needs S3+S4 plan
  axiomatisations on top of these safety theorems.

## Cross-references

- Source recipe: `sessions/2026-06-04-s7-prep-2-3-5-axis-vs-plane-recipe.md`
- Proved `(2, 5)` predecessor: S4 ACT PR #20921 (file lines 120-264 of the PRE
  state).
- Empirical safe-pair list: S2a OBSERVE PR #18494 §"Empirical search".
- Next-action menu: S6 STATE-SYNC head of `state.md` (still applies; we have
  removed one item — the `(3, 5)` axis-vs-plane safety — from the menu).

## Next action (S8 PREP or S8 ACT)

The S6/S7 next-action menu shrinks by one. Remaining concrete candidates:

1. **`(2, 13)` axis-vs-plane safety** — needs mod-13 reduction (169-case
   `decide` per helper, still tractable). The descent skeleton lifts verbatim
   with `5 → 13` in the substitution arithmetic.
2. **`(5, 7)` axis-vs-plane safety** — needs mod-7 reduction or mod-5
   reduction with `7` as the new coefficient. Slightly larger LOC budget
   than `(3, 5)`.
3. **Full-rank safety for `(2, 5)` or `(3, 5)`** — still blocked on ternary
   Hasse-Minkowski (or honest axiomatisation per S2c §6.1).
4. **Θ(n^{2/3}) assembly** — still blocked on S3/S4 plan axiomatisations.

The lowest-LOC next step is **`(2, 13)`** if the goal is to maximize the
number of safe pairs covered by elementary descent. If the goal is to close
the conjecture, **full-rank `(2, 5)` axiomatisation** (already recommended
by S2c §6.1) is the prerequisite for the Θ(n^{2/3}) assembly.

## Deliverable summary

- 1 new session memo (this file)
- Lean delta: +196 LOC to `proofs/Proofs/Erdos659OQ01OQ02.lean`
  (2 new mod-5 helpers, 3 new descent theorems, 1 new corollary)
- Docker-verified GREEN
- 0 sorry / 0 axiom delta
- state.md head + JSON `currentState.{phase, focus, nextAction, iteration,
  lastUpdate, since}` to be refreshed by this commit
