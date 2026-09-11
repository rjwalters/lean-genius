# Excluding the last six-orbit pattern by matched Klein-four stabilizers

Assume a simple C4-free nine-regular graph on78 vertices with six full automorphism orbits, satisfying the remaining pattern(6,12,12,12,12,24) of accepted2349. That result gives |A|=24, Klein-four stabilizers at the six-orbit F, and48 surviving necessary quotients. They all have the following properties: F induces3K2; each center has two neighbors in each of two12-orbits B,C and four in the24-orbit U; B,C,U vertices each have exactlyone F neighbor; the other two12-orbits have none. The deterministic cover.json checks these exact properties for every retained quotient.

Let f,f' be a matched pair in F. Their stabilizers coincide, H=A_f=A_f', since either endpoint determines its unique F matching partner. Thus H is a Klein-four group with three nonidentity involutions.

At f, H acts transitively on each of the two two-element attached fibers and the four-element U fiber. To see this, A transitivity on the corresponding whole orbit supplies an element taking one fiber vertex to another, and uniqueness of its F neighbor forces that element to fix f. The four-element action of H is regular. Each two-element action has an order2 kernel; its unique nonidentity element fixes both points, whereas the other two involutions swap them.

The two order2 kernels are different. If they agreed, their involution would fix all four vertices of the two fibers plus f' in N(f). This violates accepted2257's bound of one or three fixed neighbors at a fixed vertex. Hence exactly two of H's three involutions fix two attached neighbors at f, and the third fixes none. The four-element regular fiber contributes no fixed attached vertex.

The same argument at f' gives another two-element subset of the three nonidentity involutions in the very same group H. These subsets intersect. Choose an involution t in their intersection. It fixes f,f', two attached neighbors of f and two attached neighbors of f'. The four attached vertices are distinct because every attached vertex has a unique F neighbor. The fixed-count bound six in2257 makes these exactly the fixed vertices of t.

In the induced fixed graph, f and f' are adjacent vertices of degree3. They have no common G-neighbor: F is a matching, attached vertices have at mostone F neighbor, and the remaining vertices have none. But the only induced fixed graphs on six vertices allowed by2257 are3K2 and a triangle with a pendant leaf at each triangle vertex. The first has no cubic vertices; in the second any edge between cubic vertices lies in the triangle and has a common neighbor. Both contradict the established properties of ff'.

Thus all48 remaining quotients of this size pattern are impossible. This proof is a local variant of accepted2317's matched-center argument, using intersection of two pairs among three Klein-four involutions instead of dihedral reflection classes.

The separate degree-two-orbit packet2351 addresses the other six-orbit size pattern. Only after its independent acceptance can these results be assembled to exclude exactly six orbits. This packet makes no claim about five or seven-plus orbits, allN78, N80 or Erdős85. No graph search or Lean formalization is used.
