# Complete a7 source coverage from an exact finishing slice

Accepted review 2683. The original 2116 pass had 860 completed bases, one
wall-limited UNKNOWN and 449 unvisited bases. This separate pass visits
exactly the 450 unfinished bases, preserving every original record. All 450
completed in 15.690 seconds under the declared 120-second wall cap and
unchanged 100,000-node per-base cap (maximum used: 74,828).

The new slice supplies 28,837 graphs. Its disjoint union with the original
860 COMPLETE records covers all 1,310 bases with 74,549 graphs. The newly
completed shapes are F10: 48 bases/14,996 graphs; F11: 301/6,601; F13:
133/14,124. The coverage map identifies the precise source record for each
base. The original UNKNOWN record remains unchanged and is not inherited.

The traversal body is byte-identical to the accepted 2116 implementation.
Author and peer independently checked all new graph outputs and exact
source composition; the peer uses edge sets and counts common-neighbor
pairs. Exhaustive enumeration completeness rests on the accepted traversal
code audit, not independent exhaustive replay. This establishes source
coverage only; downstream high, host and residual checks remain required.
No whole-root, Lean, arbitrary CNF UNSAT or global conclusion follows.

Author/reviewer payloads are verbatim. BANK_PINS.json hashes every payload.
