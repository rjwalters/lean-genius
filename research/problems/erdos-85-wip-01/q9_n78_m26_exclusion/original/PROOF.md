# Proposed exclusion of N78/minimum-degree9/free-Z26

The accepted necessary-quotient review2141 leaves, up to orbit permutation, internal degrees(1,2,2) and cross degrees(4,4,3) for the three26-vertex orbits A,B,C. This premise follows from regularity below81, internal circulant degree<=2, within-orbit two-step bounds, and the antipodal-edge obstruction eliminating(1,1,1).

Fix a vertex v in B, one of the two orbits with internal degree2. Count its length-two walks ending in C, the other such orbit:

- Through A:4 first neighbours, each with4 neighbours in C, giving16 walks.
- Through B:2 first neighbours, each with3 neighbours in C, giving6 walks.
- Through C:3 first neighbours, each with2 neighbours within C, giving6 walks.

There are28 walks ending in the26 vertices of C. Each is a path with distinct endpoints, since v is in B and its endpoint in C. If two paths share an endpoint, their intermediate vertices are distinct and give a C4 with v and that endpoint. C4-freeness therefore requires at most26 walks, contradicting28.

Thus the N78/delta9/free-Z26 class is empty, subject to independent review of this consequence and its accepted2141 premise. No graph enumeration or solver call is used. The frozen generic N78/m26 CNF remains unchanged and unlaunched. This does not exclude N78 graphs with other actions or no such action, N80 graphs, or Erdős85 globally. It is a paper proof, not a Lean theorem or SAT verdict.
