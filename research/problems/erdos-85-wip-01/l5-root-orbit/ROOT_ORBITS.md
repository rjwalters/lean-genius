# Additional necessary root-orbit divisibility

Let sigma be a labeled three-root graph type and s an outside-neighbor
count vector. Its multiplicity counts ordered triples of distinct vertices.
The subgroup H of Aut(sigma) fixing s acts freely on these triples: a
nonidentity permutation cannot fix an ordered tuple of distinct vertices.
Therefore the multiplicity is divisible by |H|. Multiplicities of states
in the same Aut(sigma) orbit are also equal.

The supplied uniform-local certificate passes the latter invariance check
but fails divisibility. At q16, empty-root states0 and7 are fixed by all
six root permutations. Their supplied weights are7028 and11069824, neither
divisible by6. Exact checks at every k=4,...,12 show the same two failures.
These finite checks do not constitute a proof of failure for all k.

This additional condition is not among the constraints certified by
UNIFORM_LOCAL.md, which explicitly disclaims root-orbit divisibility. The
scoped review PASS stands. The supplied weights cannot be actual ordered
root-state counts; other decompositions, different cycle counts, or modified
rounding rules have not been excluded. This is not graph nonexistence.

Reproduce with check_root_orbits.py; root-orbit-check.json records each
tested count, stabilizer and failure. The argument above proves necessity
independently of the certificate implementation.
