# Residual normal form for two order-three fixed-point cases

This is conditional on the order-three fixed-count proof submitted as2176. It concerns N78 with F3 fixed vertices, and N80 with F5 fixed vertices. In both cases N=75+F, the fixed set is independent, and every fixed vertex lies in exactly three triangles. No graph existence or exclusion is claimed.

For each fixed vertex u, let B_u=N_G(u), of size9. These sets are pairwise disjoint because a moved vertex has at most one fixed neighbour. Each B_u contains three moved3orbits. Its induced graph is a matching of three edges plus three isolated vertices: the matching edges correspond exactly to the three triangles through u. Let U_u be those three isolated vertices; they form one moved orbit. The other two moved orbits are joined by a perfect matching (an odd3orbit cannot internally be1regular).

Let R be the set of unattached vertices, those with no fixed neighbour, and put k=9-F. Then

`|R|=N-F-9F=75-9F=9k-6`.

For x outside B_u and the fixed set, its neighbours in B_u are common neighbours of x and u, so there is at most one. In particular every cross graph B_u--B_v is a matching (possibly not yet perfect). If x in B_u has internal degree e_x=0or1, its neighbours outside R consist of u, e_x internal neighbours, and at most F-1 neighbours in other B_v. Thus x has at least k-e_x neighbours in R. Summing over B_u, where the internal degree sum is6, gives at least9k-6=|R| edges from B_u to R. Each R vertex has at most one neighbour in B_u, giving the reverse bound. Therefore equality holds everywhere.

Consequently:

1. Every B_u--B_v graph is a perfect matching on9 vertices.
2. Every R vertex has exactly one neighbour in each B_u.
3. The induced graph G[R] is kregular, since its vertices have no fixed neighbours and have exactly F attached neighbours.
4. For each u, the sets C_{u,x}=N_G(x) intersect R, for x in B_u, partition R into9 cells. The three cells indexed by U_u have size k; the other six have size k-1.
5. Cells belonging to different such partitions intersect in at most one vertex. Otherwise two R vertices would share two distinct attached neighbours, making a C4.
6. Any two distinct vertices of one cell have no common neighbour inside R, since they already share its indexing attached neighbour. The graph induced on a cell is therefore a matching and isolated vertices.

Thus the two residual parameter sets are:

| Original (N,F) | Residual (|R|,degree) | Number of partitions | Cell sizes in each partition |
|---|---|---:|---|
| (78,3) | (48,6) |3| three6s and six5s |
| (80,5) | (30,4) |5| three4s and six3s |

The original order-three action preserves R, each B_u, and each U_u. It acts freely on R and cycles the cells in three triples in each partition. The normal form applies to these two fixed-count cases only; it does not cover free order3 at78 or F2 at80. It provides no claim that the residual regular graph and partitions can or cannot be realized simultaneously, and involves no graph search, CNF or solver run.
