# F3 whole-shape computational exclusion — pending independent closure review

The shape with edges 01,02,03,12,14,35,46 is exactly `cube_F7_t3`, mask
590151, under the identity relabelling recorded in `f3-root-mapping.json`.

## Complete chain

1. Accepted 2116 contains the complete F3 slice: 149 singleton-host bases and
   2,952 E/S graphs. Its enumeration completeness rests on accepted code audit,
   not an independent replay of that enumeration.
2. Accepted 2662 verifies all high-assignment sets: 330 E/S graphs have no
   assignment; 2,622 graphs admit 66,510 assignments in total.
3. Accepted 2664 covers all those assignments. The complete host pass rejects
   4,524 high inputs and leaves 704,382 host cases, with 21,470,252 certified
   prefix prunes. No UNKNOWN or unvisited input remains.
4. One residual pass covers every host case: 700,062 empty row domains and
   4,320 arc-consistency contradictions, totaling 704,382 negative endpoints.
   It completes in 87.015 seconds under the original 180-second / 100,000-op
   limits. No continuation, UNKNOWN, unvisited, or retained case exists.
5. `audit_residual.py` independently reconstructs each input directly from raw
   source records, joins every host mask and output key exactly, and checks
   every negative using the accepted independent row enumerator. It passes in
   33.398 seconds under its 90-second limit: 851,262 domains, 514,372 rows,
   7,651 arc-removal events, and 8,184 unsupported rows.

The generic row/arc code is byte-identical to the accepted 2111/2117 API used
for F9 and F2. A completion would supply a surviving row at every active
vertex. Each empty domain, or sequence of sound unsupported-row deletions
ending in an empty domain, contradicts such a completion. Independent peer
review of this final source-to-endpoint join is pending.

## Scope

After acceptance this excludes exactly the F3 structural graph subcase at
paper/computation level. Together with accepted F2 and F5, selected H7 scopes
would cover 15 of 28 roots, leaving 13 outside those scopes. This is not a
Lean kernel theorem, arbitrary-CNF UNSAT proof, whole H7 or H1 exclusion, or
a solution of Erdős 85. The frozen solver inventory is unchanged.

The host archive is committed at `4f1e7f5938` and byte-verified. All residual
evidence is frozen separately in `residual-pins.json`. Candidate wording here
is preserved when a later review records acceptance.
