# Exact binary encoding of the remaining F2 residual quotient constraints

Fix one of the117 table representatives of accepted2226. Expand it into20 residual orbit words as in2219/2221. This note gives an exact encoding of the necessary integral quotient system, including the offdiagonal two-step inequalities omitted from2227. It does not encode edge phases or claim that a quotient lifts to a graph.

For every unordered pair{i,j}, including diagonal pairs, introduce binary variables b_ij,d_ij, symmetric by indexing. Impose d_ij<=b_ij and define q_ij=b_ij+d_ij. Thus q is0,1 or2. Impose b_ii=d_ii, so diagonal entries are0or2. For every row impose sum_j d_ij<=1 and sum_j q_ij=9-a_i-b_i, where a_i,b_i here denote presence of the two attached neighbours (these presence constants are distinct from the binary variables).

Impose the six attached marginal upper bounds stated in2224/2227, replacing each quotient entry by its b+d expression. These linear conditions capture all the earlier degree, diagonal and norm restrictions: q(q-1)=2d, hence the row norm-degree excess is at most2.

For every pair i<j and every middle index k, introduce three nonnegative continuous auxiliaries z0_ijk,z1_ijk,z2_ijk. They have the lower bounds

 z0_ijk >= b_ik+b_jk-1,
 z1_ijk >= d_ik+b_jk-1,
 z2_ijk >= b_ik+d_jk-1.

Finally impose, for each i<j,

 sum_k(z0_ijk+z1_ijk+z2_ijk) <= 3-h_ij,

where h_ij is the number of attached labels shared by both residual words, counting only present labels.

## Exactness of the auxiliary formulation

For binary u,v, a nonnegative variable z with z>=u+v-1 satisfies z>=uv, and z=uv is allowed. Since row k has at most one double entry, d_ik*d_jk=0 whenever i!=j. Therefore

 q_ik*q_jk = b_ik*b_jk + d_ik*b_jk + b_ik*d_jk.

This identity also holds when k=i or k=j; the diagonal restriction causes no exception. Every feasible auxiliary assignment thus forces (Q²)_ij+h_ij<=3. Conversely, whenever an integral symmetric Q satisfies the stated necessary system, set b=[q>=1], d=[q=2] and set the three auxiliaries to their respective binary products. Every displayed inequality then holds. Upper bounds or integrality on the auxiliary z variables are unnecessary.

There are210 unordered matrix positions,420 binary variables, and11400 nonnegative auxiliaries (190 endpoint pairs times20 middle indices times3 products). This establishes exactness for the specified integral quotient conditions, unlike the earlier fractional relaxation. It still leaves the actual Z/3 edge offsets and finer lifted codegrees unencoded.

validate.py exhausts all binary-product lower-bound cases and all admissible pairs of quotient entries with at most one2, including the diagonal specialization. It also verifies the variable counts. No optimization or graph search is run, no quotient is declared feasible/infeasible, and no capped search is restarted.
