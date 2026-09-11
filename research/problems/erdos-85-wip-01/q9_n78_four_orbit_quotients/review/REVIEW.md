# Review2314: PASS necessary four-orbit quotient cover

The five packet pins, external manifest digest and all files pinned by that external manifest match. A fresh2264 snapshot is PASS. The result does not need the pending three-orbit assembly.

Orbit-stabilizer and |A| dividing48 imply order24 or48 when four orbits sum to78. An independent ordered-three-divisor enumeration with the fourth size determined by subtraction reproduces exactly the seven order/partition cases, including checking all divisors of48 as possible group orders.

The independent quotient recursion fills rows by compositions of the remaining row sum, propagating exact edge balance to later rows. It also enforces the simple-graph capacity q_ij<=n_j. It evaluates the ordered endpoint-pair form of the common-neighbor bounds. It reproduces every saved surviving matrix exactly: six labelled matrices on6,24,24,24 at either order, one on6,8,16,48, none elsewhere. Relabelling the residual orbit gives precisely the stated two canonical matrices a=1,4.

An initial audit assertion incorrectly required equal intermediate degree-pass counts despite the independent recursion's extra early simple-graph bound. That assertion failed after the corresponding survivor-set comparison passed. The first script and diagnosis are preserved. Removing only that unjustified intermediate-count equality allowed the full independent audit to finish in0.016 seconds under its original30-second cap. No capped UNKNOWN was retried, and no producer script was executed.

The remaining6,8,16,48 quotient has cubic degree on eight vertices. In a cubic C4-free graph, a neighborhood has maximum induced degree one; two adjacent neighbors of the same neighbor would make a C4 through the base vertex. With no neighborhood edge, the six nonreturn two-step endpoints require six vertices outside the four-vertex closed neighborhood, but only four exist. Therefore each vertex lies in exactly one triangle. Distinct such triangles partition the vertex set, contradicting eight. This paper obstruction validly eliminates that quotient.

For the remaining quotients F is a matching and no two F vertices share a neighbor anywhere. Five-regular E is therefore saturated by K6 on F. Each outside vertex has exactly one common neighbor with each F vertex. The unique attachment and matching partner identify the internal and cross matching slots and the one-per-center R incidences exactly as stated. The stabilizer orders4/8 and1/2 have no factor three, so every element of order three acts freely.

This is complete necessary quotient coverage and its paper consequences, not a four-orbit graph exclusion or proof that either surviving matrix is realizable. No full graph solver or Lean theorem is claimed.
