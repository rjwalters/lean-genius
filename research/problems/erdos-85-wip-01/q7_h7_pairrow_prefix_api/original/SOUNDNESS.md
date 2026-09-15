# Optimistic pair-row pruning at a7 host prefixes

Status: implementation and fixture checks only; independent API review pending.
No host search, root exclusion, or Lean theorem is supplied by this package.

## Caller premises

1. The input B is the accepted a7 fixed-high/singleton graph, extended by a legal
   prefix of empty-host choices. High vertices are 0..6, singleton vertices
   7..20, pair vertices 21..41, and empty vertices 42..48. B is a subgraph of
   any putative completion in this branch.
2. A completion has degree seven at every pair vertex p, its two fixed high
   neighbors, no more than one empty neighbor, and all other neighbors among
   active vertices 7..41. The active neighbors' high-support sets partition
   all seven high labels, as in the accepted complete-host residual API.
3. If p is not yet hosted and can become hosted in a legal continuation, the
   caller supplies future_host_possible=True. Overestimation is allowed.
   reference.future_possible computes a safe overestimate from the complete
   remaining per-empty host-option lists, ignoring conflicts between options.

The native function checks basic layout only. It does not establish these
three structural premises. A host driver must derive them from its reviewed
input cover and legal host-prefix traversal; passing arbitrary graphs is not
a supported graph-exclusion argument.

## Necessary row domains

A hosted pair needs exactly four active neighbors. An unhosted pair needs
five if it never acquires an empty neighbor, or four if it does. Thus permit
size four for hosted pairs; size five for unhosted pairs; and additionally
size four for unhosted pairs whenever a future host is possible. At a full
host prefix future_host_possible=False, yielding exactly the existing
complete-host domain.

For each allowed size, enumerate distinct active vertices other than p and
its known neighbors. Their high supports must be disjoint and cover all
seven labels. Adding this star at p to B must preserve C4-freeness. The star
condition is tested by requiring no common B-neighbor between a candidate
v and any existing neighbor of p, and no common B-neighbor between two
selected candidates. B itself is C4-free by premise 1.

## Soundness argument

Any completion supplies its actual set R of active neighbors of p. Its size
is one of those retained above by premises 2 and 3. Its supports form the
required partition. The graph B plus the edges p--R is a subgraph of that
completion, so the star checks cannot reject R. Therefore the optimistic
domain contains R. If all allowed domains at p are empty, there can be no
completion of the host prefix.

The native colour-first DFS exhausts these rows by taking the least
uncovered high label and considering its unique owner in R. The Python
reference instead visits active vertices in increasing order. UNKNOWN from
either operation or time exhaustion is never an empty-domain certificate.
Only COMPLETE with an empty rows array permits pruning.

## Evidence and limits

test.py samples 17 deterministic COMPLETE F5 host fixtures from the reviewed
2663 cover. It compares 1,071 domains at depths 0,3,7 against the independently
coded Python reference, retains every one of 4,788 complete-row occurrences
under projection, and checks 357 final-prefix domains against the accepted
2127 independent row library. There are 971 positive domains; zero-node caps
return UNKNOWN and wrong-target vertices return INVALID_INPUT. These are
fixture checks, not exhaustive host-domain verification or a new exclusion.

Before integration into a host search: independently review this argument,
code and pins; ensure the caller's future-option lists remain complete; keep
empty-domain evidence separate from budget exhaustion; preserve exact prefix
keys and enough input data for an independent endpoint check.
