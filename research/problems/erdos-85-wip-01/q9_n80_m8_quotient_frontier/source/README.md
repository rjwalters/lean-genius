# N80/m8 necessary quotient frontier — incomplete

All13 original sorted-first-row cases reached100000 tested-row assignments. Every case is UNKNOWN; none is complete or unvisited. The pass saved24 candidate matrices and took0.0308913 seconds. No capped domain was rerun or enlarged, and zero retained candidates are not exclusions.

Accepted2140 forces9regularity. Ten8vertex orbits give symmetric integer Q, row sum9, internal degree0..2, cross degree<=3. C4-freeness gives Q² diagonal<=16 and offdiagonal<=8; diagonal parity equals row sum parity, so diagonal<=15. These constraints produce7846 ordered row profiles and13 sorted first-row representatives.

Accepted2164 additionally forbids positive cross entries between two internal-degree-one orbits and requires bipartite positive support on the internal-degree-two indices. At completed matrices, the accepted saturated-cross triangle argument2148 removes any row of odd cross degree whose positive cross pairs all have square entry8: the mixed triangles meeting a free8orbit would number8*odd/2 but must come in free orbits of size8.

The native traversal joins rows by their already assigned symmetric prefix, checks exact row inner products, and checks bipartiteness on completed indices. Original caps:100000 tested row assignments per root,60 seconds aggregate,20MB retained-matrix stream. Each cap records UNKNOWN; aggregate stops retain unvisited counts. Source/executable hashes are recorded in launch.json before execution. The raw stream remains local; its gzip equivalent is pinned for archival use.

The independent retained-only verifier checks all24 matrices and all13 ordered UNKNOWN receipts. It derives sorted roots separately and uses exhaustive binary colourings instead of producer BFS for the internal-degree-two support. It does not repeat the capped search. It checks validity and status fidelity, not coverage of unvisited branches.

This is neither a full quotient cover nor an N80/m8 exclusion or graph witness. No full80vertex graph search, graph solver or CNF change occurred. Positive-control policy is unchanged.
