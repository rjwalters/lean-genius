# T2 singleton-layer completion pilot

Of the 13 reviewed T2 heavy cores, five cannot complete the singleton layer,
three admit explicit partial completions, and five reach the search cap.
The remaining core set is therefore eight if the five rejections are accepted.
No H5 sector is excluded and no Phase B root is removed.

| outcome | canonical heavy-core bitsets |
|---|---|
| exhausted, no singleton completion |36,48,513,656,2049|
| partial witness |1,2120,9217|
| unknown at node cap |44,210,1537,6145,9729|

The heavy-core source and bit ordering are those of core-t2.json. Start with
all five-colour singleton hosting partitions, including every matching size
that fits the singleton count; do not keep only the minimum-size matchings
used by the earlier host-feasibility verifier. Larger host pairings can alter
later singleton completion and must remain in this domain. Singleton copies
are interchangeable, so each unordered partition has a fixed slot assignment.
Discard assignments that repeat a paired heavy host across colours.

For each singleton v and colour c not already present in a heavy neighbour,
BC=J requires exactly one singleton neighbour of colour c. An undirected
singleton edge uv simultaneously fills (u,colour(v)) and (v,colour(u)). The
search picks an unfilled requirement with the fewest legal partners, tries
every partner whose reciprocal requirement is also unfilled, and rejects
an edge precisely when it would introduce a second common neighbour. The
fixed high-support edges are included in that test. The completed nonempty
rows then satisfy BC=J. Edges incident to empty vertices cannot supply high
colours, so their later addition cannot repair a missing singleton-layer
completion. Hence an exhaustive failure over all hosting assignments is a
necessary-condition exclusion of that heavy core.

The initial pilot used 100,000 nodes per core and a 60-second total wall cap.
All 13 cores were visited. Five exhausted; the listed five capped at node
100,001 and are unknown. Search stops on the first positive witness, so the
positive rows do not enumerate every hosting or completion. No cap was raised
and no capped core was rerun.

A separate implementation, check_singleton_rejections.py, re-enumerates host
partitions using subsets of compatible heavy-pair edges. It then treats each
unordered pair of singleton colours as a complete matching block: ordinary
bijections for distinct colours and perfect matchings within one colour. It
enumerates whole blocks, sorted by initial domain size, with direct set-based
common-neighbour checks. This differs from the pilot's individual-edge MRV
search and bitset adjacency. It independently exhausts all five negative
cores across respectively 9,6,16,4,12 hosting assignments, within its separate
60-second verification cap. This verifier never retries the capped cores.

verify_singleton_witnesses.py imports no search code. For each of the three
positive rows it reconstructs the saved 49-vertex partial graph and checks
symmetry, no loops, exact support masks, all five high degrees equal eight,
all pairwise common-neighbour counts at most one, all low degrees at most
seven, the exact heavy core, and BC=J on all 32 nonempty-support low vertices.
The 12 empty-support vertices are isolated; empty-incident edges and remaining
low degree demands are unfilled. These are not full graph witnesses.

Replay the pilot and two checks from a copy of this folder:

    python3 singleton_completion.py
    python3 check_singleton_rejections.py
    python3 verify_singleton_witnesses.py

Scripts write their own small JSON files beside the source. The pilot imports
the already-frozen host_pilot.hostings; that dependency and the core source
are explicitly included in singleton-source-pins.json. This is reviewed
computational evidence only after independent review, not a Lean theorem.
