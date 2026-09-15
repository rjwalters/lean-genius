# Cached pair-row host integration — candidate API, no F0 closure

This a7-only implementation adds the accepted2666 optimistic pair-row test to the accepted2123 host enumerator. The validator explicitly requires mixed==7 and canonical singleton/pair/empty classes. High/support/degree/C4 base checks and the legal disjoint host traversal are inherited. This package is not an a6 API.

## Soundness and coverage

For each pair vertex, prepare all size4 and size5 residual-row templates in the fixed base graph. The exhaustive least-uncovered-colour DFS uses the same support partition and star-C4 conditions as2666. Any row compatible with a later prefix is in this base set because the prefix only adds edges. The prefix check removes templates whose stars now violate the C4 condition; it stops at the first valid row. A pair may prune only after exhausting every allowed template.

Hosted pairs allow size4. Unhosted pairs always allow size5 and allow size4 if the OR of all remaining per-empty host-option masks includes that pair. Options are complete before filtering, and their suffix OR is computed after host ordering and any explicit fixed-option restriction. Ignoring conflicts among future options safely overestimates possible hosts. At depth7 the suffix OR is zero.

Every pair prune saves depth,pair_vertex,chosen[7],future_pairs. The structural cover verifier checks that chosen masks form a legal prefix of the exhaustive matching-options tree; the endpoint verifier independently rebuilds the suffix OR and partial graph and exhausts the2666 increasing-vertex Python row domain. Singleton pruning is unchanged. Any completion of the branch is a supergraph of the prefix, so supplies a retained row; empty allowed domains contradict it. Initial validity and legal traversal establish the caller premises of2666 (alternatively a prefix already containing a C4 cannot have any completion).

One shared tick counter and deadline governs preparation, singleton tests, pair template generation, row attempts and traversal. There is no internal budget reset. Budget exhaustion propagates to the outer UNKNOWN handler; partial prepared data never produces a negative endpoint. Per-row star checks have bounded cardinality at most5; a tick charges each attempted row, analogous to the existing singleton-row loop. Template construction also charges its candidate/setup loops and DFS. These units are stricter than the original host API's units, so equal numeric caps are not equal work budgets.

## Evidence and performance

The baseline regenerates pair domains at every prefix. On twelve whole-high fixtures (eight prior operation-capped F0 and four prior COMPLETE F5), all reached100001 shared units. Every saved prune was checked, but none gave complete coverage.

The cached version prepares templates once. At the same100000-unit cap, two F5 fixtures finish with no leaves (88221 and84626 units), while the other two F5 and all eight F0 remain UNKNOWN. It emits2422 verified pair prunes. Four known fixed F5 host assignments finish with complete independently checked coverage in both versions (cached46481–47452 units). These controls validate components; they are not new root exclusions. Baseline evidence remains under baseline/, cached evidence under cached/.

The fixed controls and two complete whole-high controls pass unchanged structural coverage plus independent pair-row exhaustion and accepted singleton-star checks. Node0 returns UNKNOWN. Independent peer review of the integrated caller/coverage chain is required before any whole-case use. No full F0 pass was run; no cap was raised. This calibration does not justify calling F0 closed or calling the API effective on its hard inputs at100000 units.
