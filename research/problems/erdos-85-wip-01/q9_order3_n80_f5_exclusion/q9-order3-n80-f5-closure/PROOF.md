# Finite exclusion chain for N80 with five order-three fixed vertices

Verified finite claim (all stages independently accepted, including2214): a C4-free graph on80 vertices with minimum degree at least9 cannot admit an automorphism of order3 fixing exactly five vertices. Consequently accepted2176 leaves exactly two fixed vertices for any order3 automorphism at80.

Accepted2179 gives five attached nine-vertex groups and a30-vertex4regular residual graph with ten free order-three orbits. Accepted2184/2190 translate every such graph into attached S3 permutations, color words and necessary quotient constraints. Accepted2199 covers all necessary labelled attached-permutation assignments; accepted2200 reduces them to exactly1284 symmetry representatives while preserving possible graph realizations.

The completed exclusion stages form a disjoint exact partition of those1284 representative codes:

| Stage | Completed excluded representatives | Evidence |
|---|---:|---|
|2201|708|Exact Farkas certificates for shared-color multiplicities|
|2204|516|Completed integer-color search with residual row support|
|2205|58|Exact Farkas certificates for symmetric fractional residual weights|
|2209|1|Exact Farkas certificate adding the double-entry budget|
|2214|1|Empty local-row-support fixed point for24538199|

The sixty capped2204 cases are not treated as exclusions. They are exactly the cases discharged by the subsequent58+1+1 distinct necessary models. Failed rationalizations and no-certificate results remain recorded as unresolved in their original stage; later stages supply separate completed evidence. Numerical LP outputs alone are never counted as negative proofs.

verify.py checks all linked artifact pins, the exact representative set, disjointness and equality of the completed negative-code union, and the saved peer-review statuses. Review2214 is now PASS FULL N80/F5, including an independent audit of the complete disjoint partition. The artifact reports VERIFIED_ACCEPTED_FINITE_CHAIN. The verifier does not rerun searches or replace their independent proof/coverage audits.

Scope is only the N80/F5 order-three case. It gives no exclusion ofN80/F2, graphs without order3 symmetry, the N78 fixed-count cases, or Erdős85 as a whole. This is a finite computational proof chain, not a fully formalized Lean theorem.
