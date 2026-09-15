# F5 whole-shape computational exclusion — pending independent closure review

The a7 F5 shape has edges 01,02,03,12,34,35,45 and isolated vertex6. This is exactly frozen root cube_F7_t5, mask360519, under the identity map in f5-root-mapping.json.

## Complete chain

1. Accepted source 2116: all28 F5 singleton-host bases complete,1500 E/S graphs. Source completeness rests on accepted enumerator code audit, not an independent source-enumeration replay.
2. Accepted high review2661:504 E/S graphs admit no pairing;996 admit6944 high assignments in total. Independent exhaustive7! check reproduces every pairing set.
3. Accepted host review2663:all6944 inputs COMPLETE,331484 host leaves,2697696 rejected prefixes,0UNKNOWN/unvisited. Separate coverage/endpoint verification passed. See frozen host-pins.json.
4. One residual pass using the byte-identical generic2111/2117 row/arc API checks all331484 host leaves. Exactly331204 have an empty row domain and280 have an arc-consistency contradiction. No retained, UNKNOWN, or unvisited leaf. Runtime40.774s under original90s aggregate/100000-operation-per-leaf cap; no continuation needed.
5. Independent increasing-index row enumeration and atomic arc-removal replay verified all331484 negative endpoints in 5.091s: 341004 domains, 35468 rows, 624 removal batches, 704 unsupported rows. The source export and complete ordered result join are asserted by the producer and verifier; independent peer join/closure review is pending.

An empty row domain contradicts any completion. An arc deletion removes only a row with no compatible row at another vertex (reciprocal adjacency or at-most-one common-neighbor condition); an empty domain therefore excludes all graph completions. The code and accepted validator are generic in the F shape; source/API hashes are pinned in launch.json.

## Scope

This candidate closes exactly cube_F7_t5 at paper/computation level after review acceptance. It is not a Lean kernel theorem, arbitrary-CNF UNSAT proof, whole H7/H1 exclusion, or a solution of Erdős85. Adding it to accepted F2 coverage gives14/28 selected H7 roots and14outside, if no concurrent new root is added. Historical capped records and solver queues are unchanged. All original producer caps were met.
