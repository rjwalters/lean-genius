# Necessary quotients for N78, minimum degree9, semiregular Z13

Owner: codex-sol-3. This enumerates only six-by-six integer quotient matrices.
It does not enumerate graph lifts, invoke SAT, modify a CNF, or assume
regularity without proof. Accepted review2140 gives9-regularity below81.

The six equal13-vertex orbits give a symmetric integral quotient Q with row
sum9. Each internal graph is an odd-order circulant with degree0or2, since
degree at least4 yields a C4 from distinct noninverse shifts. Counting paths
of length two gives (Q²)_ii≤9+12=21 and (Q²)_ij≤13 for i≠j.

In fact every cross entry is at most3. Its square is at most21, so it is at
most4. If a cross entry is4 and internal degree is0, the other four cross
entries sum5 and their squares sum at least7, forcing (Q²)_ii≥16+7=23.
If internal degree is2, those four entries sum3 and their squares sum at least3,
forcing (Q²)_ii≥4+16+3=23. Both contradict21.

There are190 admissible ordered row profiles (internal0/2, five cross
entries0..3, row sum9, squared row norm≤21). Permuting the five other vertex
orbits sorts the first row, leaving nine initial cases. For each case the
recursion chooses complete row profiles matching the already fixed symmetric
prefix. Whenever a row is completed, its exact inner products with earlier
rows are checked against13. Thus every retained matrix satisfies all stated
conditions, and every admissible quotient is represented after permuting the
other five orbits. Further isomorphism deduplication is not needed for cover.

Original limits:100000 tested row assignments per first-row case and60seconds
aggregate. UNKNOWN is preserved with its retained prefix; unvisited cases
are recorded. No retry or increased cap is performed. Completeness of the
necessary quotient cover does not establish existence or nonexistence of lifts
unless all matrices are excluded by additional independently reviewed arguments.

Result: all nine first-row cases completed in0.0044s,4452tested assignments,
maximum1138percase; three representatives before full orbit reduction.
An independent edge-entry recursion includes values0..4 and uses convex
completion bounds, without importing producer profiles. Its759520states
recover exactly70labelled matrices in0.854s, two S6classes of sizes10and60.
All retained quotients satisfy Q²=9I+12J. The verification script had a syntax
typo corrected before its first execution; no research enumeration was retried.
