# a6 F18 structural graph-cover exclusion

Accepted review 2692 excludes cube_F6_t16, mask 1085571, at the level of the
finite mathematical and computational argument. The explicit permutation
[0,5,6,2,1,3,4] maps this frozen root to source a6 F18 (a five-cycle and a
disjoint edge). Reviews 2118/2122/2125/2133 supply complete source, high,
quotient and host covers: 30,182 quotient inputs cover 38,074 raw high
assignments and leave 331,996 host leaves.

One residual pass using accepted 2120/2126 code completed in 56.162 seconds
under its declared 90-second / 100,000-node limits. Every leaf is negative:
252,219 INFEASIBLE_ROW and 79,777 INFEASIBLE_ARC. There are no retained,
UNKNOWN or unvisited leaves; 43,102,758 receipt bytes fit the 150 MB cap.

The author's raw-source and endpoint verification passed in 25.645 seconds.
Peer review separately checked the accepted host/input/survivor join and
all endpoints in 27.867 seconds: 3,044,414 complete domains, 13,779,596 rows,
240,146 arc batches and 296,274 unsupported removals. Source hashes and
nonidentity root relabelling were checked independently.

With the accepted F4 and F11 exclusions, selected H7 coverage is 21 of 28
roots, with 7 outside pending the next map overlay. This is not arbitrary
CNF UNSAT, a Lean kernel theorem, whole H7 closure or a solution of Erdős85.
Prior source and capped records remain unchanged.

All payloads are verbatim, including pre-review candidate wording. This
README records acceptance. BANK_PINS.json hashes every payload.
