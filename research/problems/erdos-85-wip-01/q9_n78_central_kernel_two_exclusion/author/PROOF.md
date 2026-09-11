# Exclusion of the three-two-orbit kernel-two subcase

Let G be simple, C4-free and nine-regular on78 vertices, with full automorphism group A of order16. Suppose the nonfree locus S from accepted2419 has three A-orbits of size2 and the kernel of A acting on S has order2. Accepted2430 gives the following necessary structure:

* S induces3K2 with each edge an A-orbit.
* W is a union of three regular16-orbits W0,W1,W2, one attached to each S edge. Every W vertex has its unique S-neighbor in that edge.
* R=X unionY, where X is a transitive8-orbit and Y a regular16-orbit. X induces a matching; X-to-Y degree is2, Y-to-X degree is1, and Y has internal degree2.
* Every R vertex has one neighbor in each of the six center-neighborhood groups B_s. Thus it has two neighbors in each W_i.

Because Y and each W_i both have size16 and are transitive, the last assertion and edge balance imply that every W_i vertex has exactly two Y-neighbors. Every X vertex also has two Y-neighbors, and every Y vertex has two Y-neighbors. Consequently every vertex outside S has exactly two neighbors in Y. No Y vertex is adjacent to S.

Fix y in Y. Its nine neighbors all lie outside S, and each has exactly two neighbors in Y, one of which is y. Thus there are exactly nine nonreturning length-two walks from y ending in Y minus{y}: one through each neighbor of y. At most nine distinct vertices of Y minus{y} can have a common neighbor with y. Since Y minus{y} has15 vertices, at least six have no common neighbor with y.

On the other hand, every vertex in a simple C4-free nine-regular graph on78 vertices has exactly five other vertices with no common neighbor. Indeed there are9*8=72 nonreturning length-two walks from any vertex. Their endpoints differ from the initial vertex, and no two walks have the same endpoint, since two distinct middle vertices would give a C4. Thus exactly72 of the77 other vertices have a common neighbor with it, leaving five. Equivalently the zero-codegree graph E=8I+J-M^2 is five-regular, as also recorded in2419.

The at-least-six count inside Y contradicts the total count five. Therefore the three-two-orbit S-action with kernel of order2 is impossible.

This excludes the entire subcase2430, independently of the optional group-table and residual enumerations2434/2435. Their24 models and4224 necessary residual graphs were correctly enumerated, but none can extend to the full graph under these hypotheses. No pending enumeration, finite search, capped-domain retry or Lean formalization is used here. Full order16 with larger S-action kernel or a different S-orbit pattern remains open, as does global Erdős85.
