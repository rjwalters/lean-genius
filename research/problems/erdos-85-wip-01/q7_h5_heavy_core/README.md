# H5 finite heavy-support core reduction

This bounded census gives 1,665 / 249 / 13 candidate induced heavy-support cores
for T0 / T1 / T2. It does not assign singleton or empty-support neighbours,
exclude any sector, change a SAT queue, or establish a Lean theorem.

Use the established H5 block identities BC=J, C1=7−t and Ct=5, and canonical
support systems from Erdos85OrderFortyNineSmallHighProfileMasks.lean. There are
(14,20,10,0), (13,23,7,1), (12,26,4,2) low vertices of weights 0,1,2,3.
The triple masks are respectively [], [012], [012,034]; pair masks are the
high pairs not contained in a triple. Singleton multiplicity at colour i is
4 plus the number of triples through i. Thus the heavy cores have 10,8,6
vertices, not ten pair vertices in every sector.

For any low vertex v, BC=J says the nonempty supports of its low neighbours
partition the five high colours. If its heavy neighbours have total weight w
and number d, exactly 5−w singleton neighbours remain. Its required number of
empty neighbours is (7−t_v)−d−(5−w)=2−t_v+w−d. Consequently the induced heavy
core must have w≤5, disjoint neighbour supports, and 2−t_v+w−d≥0. Every heavy
neighbour has weight at least two, so its maximum degree is two. Triangles in
the heavy core are impossible: three heavy supports would be mutually
disjoint and need at least six high colours. Four-cycles are excluded by C4.

For distinct low vertices x,y, the full common-neighbour count is their
support intersection size plus the number of common low neighbours. It is
at most one. The incremental edge check in core_census.py enforces this for
all current heavy vertices, including the high common neighbours. It does
not assume that adjacent vertices themselves have disjoint supports.

Let e_ij count edges between weight classes, with e_ii counting edges once;
write a=e22, b=e23, c=e33. For each i the degree and weighted equations are

    2 e_ii + sum(j != i) e_ij = (7−i)n_i,
    2i e_ii + sum(j != i) j e_ij = 5 n_i.

Solving gives:

| edge | T0 | T1 | T2 |
|---|---|---|---|
| e00 |14+a|12+a+2b+4c|10+a+2b+4c|
| e01 |70−4a|68−4a−7b−12c|66−4a−7b−12c|
| e02 |2a|2a+2b|2a+2b|
| e03 |0|b+4c−1|b+4c−2|
| e11 |4a|15+4a+6b+9c|30+4a+6b+9c|
| e12 |50−4a|35−4a−3b|20−4a−3b|
| e13 |0|5−2b−6c|10−2b−6c|

T0 has b=c=0 and T1 has c=0. Nonnegative edge counts are necessary.
The census does not yet use all aggregate singleton/empty edge conditions;
its candidate set may therefore contain additional impossible cores.

Enumeration chooses the forward neighbours of vertex u after all earlier
vertices are settled. It enumerates every subset fitting the weight/degree
budget, rejects a newly created forbidden common-neighbour pair, and checks
u's remaining empty demand once its neighbourhood is complete. This gives
each labeled induced graph exactly once. At a leaf it computes the least
upper-triangular edge bitset over all permutations of the five high colours
preserving the triple system. These groups have orders 120,12,8. Their
induced action on the unique heavy supports supplies exactly the required
colour-preserving equivalence; singleton permutations do not change this core.

| sector | search nodes | labeled cores | normalized cores | complete |
|---|---:|---:|---:|---|
|T0|715505|179994|1665|yes|
|T1|9964|2578|249|yes|
|T2|211|52|13|yes|

All runs used a 30-second limit and a 100,000-normalized-core stop limit.
Actual T0 runtime was about 7.3 seconds; others below 0.03 seconds. A stop
sets complete=false; no truncated run is reported exhaustive. Stored bitsets
use itertools.combinations(range(number_of_heavy_vertices),2) order.

Replay each sector with `python3 core_census.py --sector N --seconds 30
--output /tmp/h5-core-N-new.json`. Compare all fields except elapsed_seconds.
Next step is singleton host assignment respecting BC=J and common-neighbour
capacities, followed by singleton and empty completion. No such feasibility
or exclusion claim is included here. This is computational evidence pending
independent review, not a formal exhaustive theorem.
