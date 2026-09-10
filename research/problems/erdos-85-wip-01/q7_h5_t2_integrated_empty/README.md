# T2 integrated empty-incidence pruning

This necessary-condition search exhausts cores 1 and 2120, while core 9217
reaches the unchanged 100,000-node limit and remains unknown. The domain is
exactly the three previously singleton-positive cores from review2026;
the five earlier capped cores are untouched. Subject to independent review,
T2 therefore has six open core classes instead of eight. No sector is excluded.

For a fixed heavy/singleton hosting assignment, the eventual empty-neighbour
demand is already fixed before singleton edges are chosen. A heavy vertex
of support weight t, with d heavy neighbours of total support weight w,
needs 2−t+w−d empties. A singleton with d heavy guests of total weight w
needs 1+w−d empties: its remaining 5−w colour requirements must be supplied
by singleton neighbours. The implementation computes the same quantity as
7 minus current total degree minus missing singleton colours. The weighted
sum of these demands is 60, corresponding to twelve empty rows of weight five.

An empty vertex's nonempty neighbours partition the five high colours. Its
guests must have positive residual demand and no existing common neighbour.
The initial domain enumerates every such partition, by its first uncovered
colour. Distinct empty vertices cannot use the same row, or share any guest
pair, because each row has at least two guests and a repeated guest pair
would form a four-cycle.

As a singleton edge uv is added, exactly the pairs (v,w), w in N(u), and
(u,w), w in N(v), gain a common neighbour. A row containing such a pair
becomes impossible. The search deletes exactly those rows and requires at
least twelve remaining rows and at least demand(v) rows containing each
positive-demand vertex. These tests are necessary, not sufficient. Existing
row incompatibilities cannot disappear as edges are added.

At every complete singleton layer, an exact row-at-a-time multicover search
chooses twelve distinct rows realizing all demands, rejecting repeated guest
pairs. Failure backtracks to alternative singleton completions and hosting
assignments. It does not stop after testing the first saved witness. Empty
labels are interchangeable. Empty-to-empty edges are not searched; this is
an incidence necessity test, so exhaustive failure excludes the core but
success would still be only a partial result.

All hosting sizes are retained. The node budget includes empty-row generation,
singleton search and multicover search, with a 60-second total wall cap. The
run visited all three cores in 16.3 seconds:

| core | result | nodes | host assignments tried |
|---|---|---:|---:|
|1|exhausted|43773|36|
|2120|exhausted|38261|2|
|9217|unknown at cap|100001|2|

No capped core was rerun or given a higher limit. No solver, Lean batch or
proof replay was used. The prior five unknown cores and this new unknown
remain unresolved. The script imports the banked host_pilot.hostings using
the recorded local path; source-pins.json records that dependency and the
reviewed core input explicitly. Run only in a scratch copy if replaying,
because pilot.py writes results.json beside itself.
