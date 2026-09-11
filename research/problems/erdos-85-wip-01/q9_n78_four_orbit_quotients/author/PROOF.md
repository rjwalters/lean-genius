# Four automorphism orbits force sizes 6,24,24,24

Assume G is simple, C4-free and nine-regular on 78 vertices, and its full automorphism group A has exactly four vertex orbits. Accepted 2264 gives |A| dividing 48. We prove |A| is 24 or 48, the orbit sizes are 6,24,24,24, and only two canonical degree quotients remain. This result does not assume acceptance of the separate three-orbit exclusion assembly.

## Exact finite necessary quotient conditions

Every orbit size divides |A|. If |A|<=16, four orbits have at most 64 vertices. The only larger divisors of 48 are 24 and 48. Enumerating four nondecreasing divisors with sum 78 gives one partition at order 24 and six at order 48, recorded in results.json.

For orbit sizes n_i, let q_ij be the number of neighbors in orbit j of any vertex in orbit i. Automorphism transitivity makes it well-defined. Row sums are nine, off-diagonal entries are nonnegative integers, diagonal entries lie from zero to n_i-1, and edge balance gives n_i q_ij=n_j q_ji.

For each i, counting pairs of vertices within orbit i via their common neighbor gives

    sum_j n_j * choose(q_ji,2) <= choose(n_i,2).

For distinct i,k, counting pairs with one endpoint in each gives

    sum_j n_j * q_ji * q_jk <= n_i*n_k.

These bounds hold because every distinct endpoint pair has at most one common neighbor in a C4-free graph. They include contributions from every possible common-neighbor orbit, including endpoint orbits themselves. There is no same-endpoint term in the cross inequality.

The checker parameterizes each balanced off-diagonal pair as q_ij=(n_j/d)t and q_ji=(n_i/d)t, with d=gcd(n_i,n_j) and t from zero to the largest value keeping both degrees at most nine. It enumerates these six parameters completely, determines diagonals from row sums, and applies the two displayed exact integer bounds. Thus every realizable quotient is covered; no graph existence is inferred from survival.

## Complete output and the eight-vertex obstruction

The original 30-second finite arithmetic check finishes COMPLETE in 0.111 seconds. It tests 59374 off-diagonal assignments across the seven order/partition cases. Results are:

* Order 24: (6,24,24,24), six labelled quotients.
* Order 48: (2,4,24,48), (2,12,16,48), (3,3,24,48), (6,12,12,48), no quotient.
* Order 48: (6,8,16,48), one quotient.
* Order 48: (6,24,24,24), the same six labelled quotients.

The unique (6,8,16,48) quotient has diagonal entry three on its eight-vertex orbit. This would induce a cubic C4-free graph on eight vertices, impossible. Here is a self-contained proof. At a vertex v of such a graph, its three neighbors induce a matching of size at most one. The six nonreturn two-step walks from v have distinct endpoints by C4-freeness. If the neighbors had no internal edge, all six endpoints would lie outside the four vertices consisting of v and its neighbors, where only four vertices are available. Therefore every neighborhood has exactly one edge. Each vertex consequently lies in exactly one triangle, partitioning eight vertices into triples, a contradiction.

Only (6,24,24,24) remains. Relabel the 24-vertex orbits as U,V,R so the six-vertex orbit F has no R neighbors. The six recorded quotients differ only by this choice and the following two alternatives:

    F: 1, 4,   4,   0
    U: 1, a,   5-a, 3
    V: 1, 5-a, a,   3
    R: 0, 3,   3,   3

where a is either 1 or 4. The row/column order is F,U,V,R. Both are necessary quotients, not asserted realizable. No UNKNOWN or unvisited case occurs.

## Forced matching and deficiency structure

The induced F graph is a matching of three edges. Each vertex of U or V has exactly one F neighbor, and each center has four U and four V neighbors. No residual vertex in R has an F neighbor. Thus no two distinct F vertices have any common G-neighbor: not in F (a matching), not in U or V (unique F neighbor), and not in R.

For N78, E=8I+J-A_G^2 is the five-regular zero-codegree graph. Hence E induces K6 on F and has no edge from F to the complement. Every outside vertex therefore has exactly one common G-neighbor with each center. This forces the familiar matching structure directly, without assuming an involution fixes F: an attached vertex has exactly one internal neighbor in its own center group, none in its matching partner's group, and one in each of the other four groups; each R vertex has one neighbor in each of the six attached groups. These assertions follow by identifying the only possible common-neighbor slot for each center.

Finally every vertex stabilizer in A has order a power of two: at F its order is 4 or 8, and at each 24-orbit it is 1 or 2. Consequently every order-three element acts freely on the whole graph.

This finite necessary quotient restriction leaves two four-orbit degree patterns. It does not exclude four or more orbits, all N78 graphs, N80, or Erdős85. No graph solver or Lean formalization is used.
