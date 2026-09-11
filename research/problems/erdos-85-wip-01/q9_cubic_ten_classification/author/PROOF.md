# Three cubic C4-free graphs on ten vertices

Every finite simple cubic C4-free graph on ten vertices is isomorphic to exactly one of the three explicit graphs in representatives.json. Their numbers of triangles are respectively0,2,3, so they are pairwise nonisomorphic. The proof below does not assume connectedness and involves no enumeration of arbitrary ten-vertex graphs.

## Triangle-free case

Choose a vertex u and its three neighbors a_1,a_2,a_3. They are pairwise nonadjacent. Each a_i has two other neighbors; all six of these vertices are distinct, outside u and the a_i, because a repeated vertex would produce a triangle or a four-cycle. This accounts for all ten vertices.

Each of the six final vertices has exactly one neighbor among the a_i: adjacency to another would give a four-cycle through u. It therefore has exactly two neighbors among the six final vertices. Their induced graph is2regular and triangle-free, hence a six-cycle (two three-cycles are forbidden). The two vertices attached to the same a_i cannot be adjacent, or they form a triangle with a_i, and cannot be distance two on the six-cycle, or they form a four-cycle with a_i. They are therefore opposite vertices of that cycle.

This uniquely specifies the first graph: vertex0 joins1,2,3; the six-cycle is4-5-6-7-8-9-4; vertices1,2,3 join the opposite pairs(4,7),(5,8),(6,9).

## A graph containing a triangle

Choose a triangle on vertices a_1,a_2,a_3. Let x_i be the third neighbor of a_i. These three vertices are outside the triangle and distinct: a common x for two triangle vertices, together with the third triangle vertex, gives a four-cycle. No x_i is adjacent to x_j, since x_i-a_i-a_j-x_j-x_i would be a four-cycle.

Let Y be the remaining four vertices. Every x_i has exactly two neighbors in Y. Thus there are six x--Y edges, and the degree sum in Y is12. The induced graph on Y has exactly three edges. A simple four-vertex graph with three edges is either a path P4, a star K1,3, or a triangle plus an isolated vertex. (If connected it is a tree of one of the first two forms; if disconnected the only way to have three edges is the triangle.)

Record the two Y-neighbors of each x_i as an unordered pair. These three pairs must be distinct, otherwise two Y vertices share two x-neighbors. Also, no chosen pair may have a common neighbor within Y, again by C4-freeness. The number of chosen pairs containing y is exactly3-degree_Y(y).

* If Y is a star, its center has demand0 and each leaf demand2. Every pair of leaves has the center as a common neighbor, so no permissible pairs can meet those demands. This case is impossible.
* If Y is a path y_1-y_2-y_3-y_4, the demands are(2,1,1,2). The distance-two pairs are forbidden. The only possible three pairs are{y_1,y_2},{y_1,y_4},{y_3,y_4}: both end vertices require both available partners. These pairs give the third explicit graph, which has three triangles.
* If Y is a triangle on y_1,y_2,y_3 plus isolated y_4, the demands are(1,1,1,3). Pairs within the triangle are forbidden, leaving exactly{y_1,y_4},{y_2,y_4},{y_3,y_4}. These give the second explicit graph, which has two triangles.

Permuting the x_i together with their triangle vertices absorbs every assignment of the three pairs to the three x_i, so each surviving Y form yields a single isomorphism type. Every potential graph has been covered by these cases.

## Verification and application

The included audit.py verifies every displayed representative is simple, cubic and C4-free by direct common-neighbor counts, and computes triangle counts0,2,3. It also independently checks all twenty choices of three distinct Y-pairs for each of the three possible Y forms, obtaining exactly the possibilities used above. This small check supports the explicit constructions; completeness follows from the structural proof.

For accepted2223/2225, the ten-vertex fixed graph H in the N78/F10 involution case can consequently be restricted to these three graphs. The same applies to the cubic alternative atN80/F10. None of the three is asserted to extend to a full78- or80-vertex graph. This does not classify the one-leaf fixed graph alternative at80, and is not a full involution-case or Erdős85 exclusion.
