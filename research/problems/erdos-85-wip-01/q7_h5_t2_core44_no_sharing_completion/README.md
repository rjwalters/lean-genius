# Core44 no-sharing completion via own-colour normal form

All eight new normalized cases exhaust: node counts75,67,75,67 for the S3 type without f3-d3, and91,91,91,91 for the type with that edge. Total648 nodes, eight visited, zero caps. This is provisional until independent end-to-end review.

## Coverage

Reviewed2055 excludes all no-sharing bf1 cases, and reviewed2056 excludes af4/bf2. Hence only af3/bf2 remains. The within-colour perfect matching argument submitted as2054 yields two canonical37vertex graphs for this pair: the heavy-free vertices may be renamed independently inside each singleton colour, leaving two S3 matching types. canonical-source.json contains all eight af/bf/S3 configurations from that cover; the builder selects exactly the two af3/bf2 ones.

The reviewed2046 distinguished-empty cover yields four27vertex patterns, containing five highs, six heavies, twelve empties and a0,b0,b2,b4. four-pattern-source.json is byte-identical to that frozen source. Its original indices0..10 remain0..10, its empties11..22 map to37..48, and23..26 map by name to a0,b0,b2,b4 in the37vertex graph. Merge each pattern with each selected own-colour graph. All eight unions are directly C4-free.

These normalizations are compatible: the own-colour renaming moves only heavy-free singleton vertices, whereas the distinguished-empty normal form fixes the named specials and heavy vertices and renames only empties. Thus every full no-sharing graph is isomorphic to a completion of at least one of the eight unions. All high/heavy incidences are fixed; high degrees are8 and all low target degrees are7.

## Search necessity and completeness

check.py computes deterministic necessary forcing from the eight initial graphs. An absent low-low edge is available only when both endpoints have degree below7 and insertion creates no C4. Candidate edges can only disappear as a partial graph grows. A vertex with fewer candidates than its degree deficit is impossible; equality forces every candidate. A low vertex missing a high-colour common neighbour must acquire a candidate adjacent to that high vertex; zero candidates contradict BC=J, and one forces an edge. Each iteration adds only one forced edge and recomputes. This yields five forced edges in the first S3 type and two in the second, with no initial contradictions.

complete.py repeats these tests at each search node. If forcing stops, it picks either a missing-colour requirement or an entire residual degree row with the smallest number of candidate subsets. For a colour requirement it enumerates every one-element candidate choice; for a degree row it enumerates every subset of the required size. Each inserted edge is checked again against the updated graph. Every valid completion must occur in one of these branches. Recursive graph copies isolate state. Fully completed candidates would be checked for exact degrees, every common-neighbour bound, and every low/high BC entry; none is found.

The completion uses at most100000 nodes per new case and60seconds total, with UNKNOWN on limits. None reaches either limit. These cases fix an independently derived own-colour normal form and all ordinary heavy guests; they are a different domain from the historical capped F-star searches, whose original records remain unchanged. A final replay after replacing external paths by local frozen copies reproduced all eight exact node counts.

Run python3 check.py then python3 complete.py from this package. pins.json binds both input files, both scripts, both results and this explanation. No Lean theorem, solver receipt, queue change, sharing exclusion, wholecore44 exclusion, H5 closure or global Erdős85 result is claimed by this package alone.
