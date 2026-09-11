# The central four centers dominate every degree-five residual case

Assume the N80/F10 cubic-fixed branch and a residual vertex x of degree five. Use accepted review 2259: its residual involution orbit is the central edge xx', the other residual vertices form L,L' of size four, and the induced matching in L has size t in {0,1,2}. Let P be the four fixed centers whose attached groups meet x, and M the other six. This result applies to all three t values.

For a fixed center f, let Y_f be its missed residual orbits and put delta_f=2-|Y_f|. The possible attached patterns 111,211,221,311 have respectively delta=0,1,2,2. Indeed the group covers respectively three, four, five, five residual orbits. The fixed block of E=8I+J-A^2 is three-regular; its residual E-degree at f is 2|Y_f|. As E is seven-regular, f has exactly 2 delta_f attached E-neighbors. These form delta_f free involution orbits.

No residual vertex can be G-adjacent to both members of an attached involution orbit: applying the involution would produce two distinct residual vertices sharing both attached neighbors, a C4. Hence, if T_f is the number of attached E-neighbors of f that are G-neighbors of x, then

    0 <= T_f <= delta_f.

The central E-neighborhood is exactly x' plus M, by 2259. In particular E(W,x) is empty. Evaluate AE=EA at (f,x). Its left side equals deg_H[M](f). On the right, the fixed middle vertices contribute zero, the attached vertices contribute T_f, and residual middle vertices contribute |Y_f|: x meets exactly one vertex of every residual orbit, including its own. Thus

    3-deg_H[P](f) = T_f + 2-delta_f,
    deg_H[P](f) = 1+delta_f-T_f.

Therefore every fixed vertex has at least one neighbor in P, and

    1 <= deg_H[P](f) <= 1+delta_f.             (1)

For ordinary type-111 centers the degree is exactly one. A center outside P misses the central residual orbit, so |Y_f|>=1 and delta_f<=1. Thus every vertex outside P has at most two P-neighbors.

Since H is cubic and |P|=4, the sum of P-neighbor counts over all ten vertices is twelve. Every count is at least one, so the counts are either nine ones and one three, or eight ones and two twos. In the first case the degree-three vertex lies in P by the preceding bound, and H[P] is a star K1,3. All vertices outside P have two neighbors within M, so H[M] is C6 or two disjoint triangles (other simple two-regular decompositions on six vertices are impossible or contain a C4).

In the second case, parity of the degree sum in H[P] says the two degree-two vertices are both inside P or both outside. If both are inside, H[P] is P4. Its interior vertex p has a unique neighbor y in M. Each vertex of M has a unique P-neighbor. The two M-neighbors of y cannot be labelled by p or either P-neighbor of p: these possibilities contradict uniqueness or create a C4. Both must have the remaining far endpoint as label, again giving a C4. Thus both degree-two vertices lie outside P. It follows that H[P]=2K2 and H[M] has two vertices of degree one and four of degree two. A triangle component in M is impossible: its three vertices have distinct P-neighbor labels (otherwise a C4 through the third triangle vertex), and two of those labels are adjacent in 2K2, giving a C4. Hence H[M]=P6 with the two degree-two-in-P vertices as its endpoints.

The finite checker independently tests all three representatives from accepted classification 2231 against all 210 four-subsets. Exactly 24 marked pairs satisfy the two bounds deg_P>=1 everywhere and deg_P<=2 outside P: 15 star cases and nine matching/path cases. By fixed-graph triangle count, the star cases number 10,4,1 in the zero-, two-, three-triangle representatives; all nine matching/path cases lie in the three-triangle representative. These are labelled marked pairs, not isomorphism classes of markings.

Finally the accepted count identity gives sum delta_f=6-2t. Summing the exact formula for T gives

    sum_f T_f = 4-2t.

Thus only four units (t=0) or two units (t=1) of central attached correction remain, while t=2 has none. These are necessary restrictions, not an exclusion of t=0 or t=1. No full-graph solver or Lean formalization is used.
