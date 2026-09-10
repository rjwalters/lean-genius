# T0/T2 singleton-host pruning

The five-colour singleton-host test leaves 761 of 1,665 T0 heavy cores and all
13 T2 cores. It excludes heavy-core candidates, not either H5 sector.
T1 singleton continuation is owned independently by codex-sol-1.

For colour c, every heavy vertex not already adjacent to a heavy support
containing c needs exactly one singleton neighbour of colour c (BC=J).
There are 4 + number_of_triples_through_c such singletons. A singleton can
host at most two heavy vertices since their weights sum to at most five.
Two vertices can share that host only when their high supports are disjoint
and they have no existing common heavy neighbour: otherwise adding the
singleton creates a second common neighbour. Conversely these conditions
suffice for the partial graph containing the fixed support edges, the heavy
core, and all heavy-to-singleton edges. Between colours, the same heavy
pair cannot share two singleton hosts, which would create a four-cycle.

`host_pilot.py` enumerates unordered partitions into singleton/pair groups
for each colour, subject to its singleton capacity. It then chooses one
partition per colour with no repeated paired group. Unused singleton slots
are empty groups. Permuting the identically supported singleton copies
preserves all feasibility, so fixing this group order loses no assignment.
The search is exhaustive on failure; it stops at the first positive witness.
Per-core cap 100,000 nodes and total wall cap 60 seconds were never reached.

| sector | input cores | fail one colour | fail joint colours | partial witnesses |
|---|---:|---:|---:|---:|
|T0|1665|407|497|761|
|T2|13|0|0|13|

`verify_hosts.py` imports no search code and checks every result independently.
If a colour needs r incidences and has s singleton slots, its hosting
matching needs at least k=max(0,r−s) pairs. It suffices to test exactly k:
splitting an extra pair into two singleton groups preserves the capacity
until k is reached, removes a possible conflict, and introduces no new paired-host conflict.
The verifier enumerates k-element subsets of allowed pair edges, keeps
vertex-disjoint subsets, and combines the five colours by bitset dynamic
programming prohibiting repeated edges. Its answer matches every one of the
1,678 input cores.

For every positive witness the verifier separately constructs the full
49-vertex partial adjacency matrix, with the exact high supports and empty
vertices added as isolated vertices. It checks all high degrees equal eight,
all low degrees are at most seven, every pair has at most one common
neighbour, and every heavy vertex has exactly one common neighbour with
each high vertex. It saves a graph digest for each witness.

These are partial graphs. Singleton-singleton, heavy-empty, singleton-empty
and empty-empty edges remain unassigned. A single partial witness is not a
complete graph, and failure to extend that particular witness would not
exclude its core unless all other hosting assignments are also covered.
No SAT instance, proof replay, Lean enumeration or queue change occurred.

Replay from this directory:

    python3 host_pilot.py --sector 0 --output /tmp/h5-hosts-t0-new.json
    python3 host_pilot.py --sector 2 --output /tmp/h5-hosts-t2-new.json
    python3 verify_hosts.py

The verifier consumes the archived hosts-t0/hosts-t2.json beside its source;
copy the folder for a full fresh rerun. Source and results are frozen in
host-source-pins.json, separately from the core review2022 pins.
