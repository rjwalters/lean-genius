# Session 2026-07-24 (researcher-2): ACT — self-duality formalized at both layers

## Context
S1 SURVEY (2026-06-13) fully mapped the math; ACT was build-gated by the
then-live Docker blackout. Infra has long since returned; this session
executes the recorded 4-part plan (Parts A–C; Part D folded into docstrings).

## What was built (`proofs/Proofs/DesarguesTheoremOQ02OQ02.lean`, new file)

### Layer 1 — finite Desargues 10₃ configuration (Part A)
Pairs model: points AND lines = 2-subsets of Fin 5 (explicit `![…]` tables
`pairOf`/`lineOf` with the geometric dictionary O={0,1}, A={0,2}, …,
axis=l_{01}, la=l_{34}, …), incidence `Inc p l := pairOf p ∩ lineOf l = ∅`.
By kernel `decide` (no native_decide):
- `inc_line_card_three` / `inc_point_card_three` — genuine 10₃;
- `desargues_roles_central/sides/axis` — all 30 role incidences hold;
- `ptToLn`/`lnToPt` explicit polarity tables, mutually inverse, and
  `polarity_reverses : Inc p l ↔ Inc (lnToPt l) (ptToLn p)`.
The polarity realizes the classical dictionary: O ↔ axis, vertex ↔ opposite
side of the OTHER triangle (A↦B'C'), perspectivity line ↔ axis point (la↦Q).

### Layer 2 — class-level duality (Parts B–C)
On bare `[Membership P L]` (the layer of Mathlib's `Configuration.Dual`):
- `PointsCollinear`/`LinesConcurrent` + `Iff.rfl` dual swaps
  (`pointsCollinear_dual_iff`, `linesConcurrent_dual_iff`);
- `IsDesarguesian` / `IsConverseDesarguesian` — universal incidence forms
  with a 12-inequality nondegeneracy schema chosen CLOSED under the polarity
  (A≠A',B≠B',C≠C'; p,q,r pairwise; la,lb,lc pairwise; ab≠ab',bc≠bc',ca≠ca');
- **`isDesarguesian_dual_iff : IsDesarguesian (Dual L) (Dual P) ↔
  IsConverseDesarguesian P L`** — the headline; proof = explicit statement
  swap along the polarity (39 hypotheses transposed by hand, both directions);
- `isConverseDesarguesian_dual_iff` via definitional involutivity of `Dual`;
- `desargues_package_self_dual` — (D) ∧ (D*) invariant under dualization;
- `example`: Mathlib's `ProjectivePlane (Dual L) (Dual P)` instance situates
  everything on genuine projective planes.

## Key design decision
The nondegeneracy schema must be polarity-closed or the duality is NOT a pure
statement swap. The 12-inequality set maps onto itself: la≠lb ↦ q≠r,
ab≠ab' ↦ C'≠C, etc. This is why converse-Desargues' "natural" hypotheses
(distinct axis points, distinct corresponding vertices) are exactly the dual
of Desargues' (distinct perspectivity lines, distinct corresponding sides).

## Honest scope (recorded in file header)
- No claim that any plane IS Desarguesian (Moulton parent refutes generality).
- The INTRA-plane implication "(D) in a projective plane ⟹ (D*) in the same
  plane" is genuine geometry (apply D to a derived configuration), NOT formal
  duality — left open, a natural follow-up.

## Build
GREEN on first attempt: `./proofs/scripts/docker-build.sh Proofs.DesarguesTheoremOQ02OQ02`
— 8576 jobs, exit 0, zero errors. 0 sorries, 0 axioms, kernel decide only.
