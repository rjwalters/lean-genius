# H7: every singleton meets an empty vertex

Assume the established H7 graph premises and accepted profile exclusions listed in endpoints.json. Choose any singleton S and its high neighbour as high0. The reviewed high0 matching/host covers2064/2066/2068 apply to this choice without any maximal-degree assumption. S becomes one of the two singleton hosts, and its number of empty neighbours is the corresponding entry in the normalized host-count profile. If S had no empty neighbour, that profile would have a zero among its first two empty counts.

The exact22profile table has this property only for twin4,twin6,crossed9,crossed10,crossed11,crossed14. All six entire assignment domains are now excluded by accepted reviews2084,2074+2075,2082,2077,2078,2076 respectively. Thus S cannot have zero empty neighbours. This argument applies to every singleton, not merely to singleton hosts at a maximum-degree high vertex.

Every singleton has at most two empty neighbours: if e counts its empty neighbours, the low-degree/common-high identities give e+1 pair neighbours and5-2e singleton neighbours. Nonnegativity implies e<=2. Therefore all14singletons have one or two empty neighbours.

An empty vertex of empty degree d has d pair neighbours and7-2d singleton neighbours. Hence the total singleton-empty incidence count is49-4a, where a counts empty-empty edges. If z singletons have two empty neighbours and l have one, z+l=14 and2z+l=49-4a. Consequently z=35-4a and l=4a-21. For a6/7/8 this gives(z,l)=(11,3),(7,7),(3,11).

check.py verifies the exact six-profile set and arithmetic against the frozen original profile table and accepted prerequisite review snapshots. endpoints.json binds each accepted exclusion to its original manifest hash; the reviewers already checked those complete assignment domains, not merely a sample or partial projection. Independent review of this final inference is requested. The older conditional preparation remains unchanged in /tmp/erdos85-sol1-h7-singleton-positive.

This proves a necessary structure of remaining H7 graphs at the paper/independently checked finite-computation level. It does not exclude all H7 graphs, discharge a Lean premise, change the frozen queues or solve Erdős85.
