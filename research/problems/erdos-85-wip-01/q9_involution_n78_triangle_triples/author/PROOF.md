# Each odd missing-pair permutation admits local residual triples

This package concerns only the residual label triples of the N78/F6 triangle case. Label each of the three six-element sets by0..5 with involution x->x xor1. Normalize the missing A1--A2 and A1--A3 bijections to the identity. Let pi be the missing A2--A3 bijection. The separate paper parity result2247 requires pi odd and commuting with the involution.

The centralizer is generated explicitly by a permutation of the three pairs and three independent flips. Keeping the four odd-parity flip choices gives all24 odd permutations, with no relabelling quotient applied. For every such pi, results.json provides fifteen triple-orbit representatives with their first coordinate even. Expand each(x,y,z) to itself and(x xor1,y xor1,z xor1). The resulting thirty triples project bijectively to all pairs except(x,x) in coordinates12 and13, and except(y,pi(y)) in coordinates23.

A witness is therefore directly verifiable by three set comparisons. Each coordinate label automatically occurs five times. This realizes all the stated pair-incidence and involution constraints, but includes no residual edges, no attached internal matchings, and no leaf-group incidences.

check.py uses45 pair-orbit exact-cover constraints. Each eligible triple orbit covers one constraint of each pair type. The search stops at the first witness for each pi, under original aggregate60seconds and100000nodes per root. All24 roots returned witnesses in about0.0065seconds,525 total recursive nodes and maximum53 for one root. There were no UNKNOWN or negative roots. No search completeness is needed to verify these positive witnesses. This is not complete enumeration of triple systems or phases and is not full graph feasibility.
