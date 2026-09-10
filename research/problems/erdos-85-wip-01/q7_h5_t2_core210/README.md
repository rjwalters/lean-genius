# T2 core 210: empty-first exclusion

Provisional pending independent review: core 210 cannot extend. This uses a
new empty-first decomposition. Its earlier singleton-search cap is preserved
as UNKNOWN; that search is not rerun or given a larger budget.

The T2 heavy masks in the reviewed order are 012,034,13,14,23,24. Core 210 has
edges (0,2),(0,5),(1,3),(1,4). For a heavy vertex of weight t with d heavy
neighbours of total weight w, BC=J forces 5−w singleton neighbours and hence
2−t+w−d empty neighbours. The six demands are (1,1,2,2,2,2).

There is no compatible pair of heavy guests at one empty vertex: each heavy
pair either shares a high support or already has a common heavy neighbour.
Adding a shared empty would then create C4. Thus every empty has at most one
heavy guest. Up to relabelling the twelve empty vertices, the incidence is
unique: one row for each triple, two for each pair, and two rows with no heavy
guest. pattern_audit.py re-derives this from the exact core, checks the pinned
pattern and joins the reviewed T2 core census.

For an empty row with d heavy guests of total weight w, exactly 5−w singleton
neighbours remain. Its empty-induced degree must therefore be 7−d−(5−w), or
2+w−d. The forced degrees are (4,4,3,3,3,3,3,3,3,3,2,2).

search.py enumerates all empty-induced graphs of those degrees, retaining the
fixed high/heavy/empty incidence on 23 vertices. At each step it chooses an
unfinished vertex and enumerates every subset of unfinished neighbours that
fills its residual degree, with direct C4 pruning. The final reviewed version
uses NO twin or other symmetry pruning; only the initial arbitrary labels of
identical empty rows are fixed. This labeling loses no full graph because
those empty vertices are interchangeable before their mutual edges are added.

A necessary singleton-host condition prunes partial empty graphs. For colour
c, every existing low vertex without a colour-c heavy neighbour must receive
exactly one singleton of colour c, by BC=J. There are (6,5,5,5,5) singleton
slots. A slot hosting d existing guests of total support weight w must have
w≤5 and d≤1+w: it still needs 5−w singleton neighbours, and its low degree is
six. No hosted guest pair may already share a neighbour. The test enumerates
all such groups and partitions the colour's required guest set into at most
the available slots. Different colours are tested independently, weakening
the condition safely. Current common neighbours can only increase when more
empty edges are added; required guest sets and weights stay fixed, so failure
also excludes every extension of the partial empty graph.

host_constraint.py enumerates compatible groups and solves a subset cover.
host_constraint_bins.py is a separate implementation: it assigns heavy guests
first, then empty guests, directly into interchangeable bins. Processing
heavies first makes its intermediate degree-capacity check sound: while there
are only heavy guests d≤1+w automatically; once empty guests begin, w cannot
increase. Both implementations exhaust core 210 in the same 23,489 graph nodes,
well below the 100,000-node / 60-second verification bounds. No capped case
was retried. The two variants share the empty-graph traversal, which still
requires independent completeness review.

This excludes one T2 core if reviewed, leaving five open cores. It is not a
whole-sector or Lean theorem and does not modify any SAT inventory.

Replay in a scratch copy:

    python3 pattern_audit.py
    python3 search.py
    python3 verify_search.py

The scripts write small JSON receipts beside themselves. The discarded
symmetry-pruned pilot is not part of this frozen package or its proof claim.
