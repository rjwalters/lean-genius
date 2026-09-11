# Finite exclusion of the faithful three-orbit action on F

Assume the N78 three-orbit form2264 and the action reduction2268. If the action of A=Aut(G) on the six-element matching F were faithful, it would identify A with all48 permutations of F preserving its three edges. This finite check excludes that faithful alternative. It does not exclude a nontrivial action kernel or all three-orbit graphs.

Label F by0..5 with matching i--(i xor1). Represent A as the permutations p satisfying p(i xor1)=p(i) xor1. Choose a base vertex w in the regular48-orbit W adjacent to centre0. Identify W with A by g corresponding to g(w); its attached centre is then g(0). Composition is (g h)(i)=g(h(i)).

The induced graph on W is a Cayley graph with a connection set S of size five, because the accepted quotient gives W-degree five. It excludes the identity and is closed under inversion, since the graph is simple and undirected. At the identity vertex the matching saturation in2264 gives exactly one W-neighbor attached to each centre other than1 (the partner of0), and none attached to1. Therefore the multiplicities of s(0), for s in S, are exactly(1,0,1,1,1,1).

For any nonidentity g, the common W-neighbors of the identity and g are exactly S intersect gS. Those two W vertices additionally share an F-neighbor precisely when g(0)=0. Hence a necessary C4-free condition on the induced F+W graph is

    |S intersect gS| <= 0 if g(0)=0, and <=1 otherwise.

Every full graph in this faithful case must provide such an S. No edge to the remaining24 vertices can repair a violation within F+W.

check.py constructs all48 matching-preserving permutations directly from the720 permutations of six points and computes their composition and inversion tables. Excluding the identity, there are19 involutions and14 inverse pairs of noninvolutions. Every inverse-closed five-element set has exactly k inverse pairs and5-2k involutions, for k=0,1,2. Thus the loop enumerates each such set exactly once, without a symmetry quotient or pruning that could omit a case.

The exact count is choose(19,5)+choose(14,1)*choose(19,3)+choose(14,2)*choose(19,1)=26923. Exactly380 sets satisfy the six target multiplicities. None satisfies all the displayed intersection bounds. The original60-second run completed in about0.055seconds, with all roots visited and no UNKNOWN or retry. results.json records the complete group ordering, counts and empty survivor list. This is exhaustive finite verification of the specified local connection-set problem, not a general full-graph solver.

Conditional on independent acceptance of the model reduction and enumeration, the kernel K of A acting on F must therefore be nontrivial. By2268 its order is2,4,or8. It contains an involution fixing exactly F pointwise and acting freely outside F. This connects every remaining three-orbit case to the six-fixed matching-involution structure. No full N78 exclusion or Lean formalization is claimed.
