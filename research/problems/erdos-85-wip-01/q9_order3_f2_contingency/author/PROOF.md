# Local attached-pair contingency coverage for N80/F2

Conditional on2219. Label each attached set's three free orbits0,1,2, with0 internally isolated and1,2 internally matched. Write E for the3x3 matrix exchanging1,2 and killing0. The A--B orbit matching is a partial permutation matrix P with exactly two or three entries1. There are18 choices with two entries and6 with three.

For residual orbits having both an A and a B neighbour, let T_ab count those meeting attached labels a,b. Counting two-step walks from one vertex in A_a into the three vertices in B_b yields

 T+EP+PE <=3J.

Each residual orbit counted by T contributes one matching-composition path; the other two terms are the internal matching on the A or B side. There are no fixed-vertex middle paths because the two fixed vertices are nonadjacent and their attached sets disjoint. These terms exhaust possible middle vertices.

If P has two entries1, every residual orbit meets both sides. The row margins of T are r_a=8-e_a-c_a, where e=(0,1,1) and c_a is the row sum of P; column margins are the analogous8-e_b-column_sum(P). Each margin total is20.

If P has three entries1, each side misses exactly one residual orbit. If the missing orbits coincide, T has margins(7,6,6) on both sides and total19. If they are distinct, let i be the A label of the B-missing orbit and j the B label of the A-missing orbit. Then T has row margins(7,6,6)-unit_i and column margins(7,6,6)-unit_j, total18. There are nine such ordered label choices. This gives18+6*(1+9)=78 rooted local states; phases and residual Q are not represented.

run.py enumerates each first and second row within its entry capacities and required row sum. Column margins uniquely determine the third row, which is checked against capacities and its row sum. Thus each nonnegative integer table satisfying the stated conditions occurs exactly once per rooted state. Original60s aggregate cap, no retry: all78 states COMPLETE in about0.0023s, with672 tables saved. Every state has at least one table. Therefore this local condition alone excludes none of the rooted states and provides no graph existence or exclusion claim.

missing_labels=null means all20 residual orbits meet both sides for cross_orbits=2, and the same missing orbit for cross_orbits=3. For distinct missing orbits it records(i,j) as defined above.
