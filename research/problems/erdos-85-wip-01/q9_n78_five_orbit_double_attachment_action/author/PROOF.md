# Two faithful S4 actions in the order24 double-attachment case

Assume a simple C4-free nine-regular graph on78 vertices has full automorphism group A of order24 and five orbits F6,B12,C12,U24,V24. Assume the double-attachment quotient type among the four such quotients in accepted2335: F is a matching, B vertices have two F neighbors, each F vertex has four B neighbors, and one regular24 orbit supplies the other four F neighbors. The two24 orbits are regular A actions. We classify the necessary action on F and B, not full graph adjacency.

The equivariant map b -> N(b) intersect F injects B into unordered F pairs, since repeated pairs give a C4. The kernel K of the F action therefore fixes all18 vertices in F union B. K is a subgroup of A_f of order4. Any nontrivial K contains an involution fixing18 vertices, contradicting accepted2257's upper bound six. Hence A acts faithfully on F and is an index2 subgroup of the matching group M=F2^3 semidirect S3, order48.

Write pi:M->S3 for permutation of matching edges and D=A intersect F2^3. A is transitive on F and hence on its three matching edges, so pi(A) has order3 or6. The image of B is an A orbit of size12 on unordered F pairs. None of the three matching pairs can lie in that orbit, because their orbit has size3. Hence B identifies with all twelve nonmatching pairs.

If |pi(A)|=3 then D=F2^3 and A is the full preimage F2^3 semidirect C3. In particular it contains a flip of one matching edge, fixing four F vertices and four nonmatching pairs among them. That involution fixes at least eight vertices, contradicting2257. Thus pi(A)=S3 and |D|=4.

Since D is a coordinate-permutation invariant codimension-one subspace of F2^3, it is the kernel of a nonzero invariant linear functional. The only such functional is coordinate sum: coordinate permutation invariance makes its three coefficients equal. Thus D is the even-weight plane. The quotient M/D is C2 times S3 and A/D projects isomorphically onto S3. It is the graph of a homomorphism S3->C2. Such a homomorphism is either zero or permutation sign: three-cycles map to zero and conjugate transpositions share an image. Exactly two necessary actions remain:

    A0 = {(v,sigma): sum(v)=0},
    A1 = {(v,sigma): sum(v)=sign(sigma)}.

Both are isomorphic to S4. For a direct proof, M acts on the four antipodal pairs of cube diagonals. Its kernel consists of identity and global flip: fixing the all-positive diagonal forces all coordinate signs equal; after global negation, fixing the three other diagonals forces the coordinate permutation to be identity. Global flip has odd flip parity and identity permutation and lies in neither A0 nor A1. Both order24 groups therefore embed faithfully in S4.

A0 has center stabilizer V4: fixing a chosen oriented coordinate axis forces its flip bit zero, the other two flip bits equal, and permits identity or interchange on those two coordinates. These two commuting involutions generate all four elements. A1 has center stabilizer C4: choose the interchange of the other two coordinates and unequal flip bits there; its square flips both, so it has order4. These are the same signed-group classifications used in accepted2306, with no reuse of that packet's distinct residual-stabilizer hypothesis that excluded A0 in its three-orbit setting.

In either case F and B have the stated natural actions, U,V are regular, and the remaining C12 is A/L for an order2 subgroup L. No further restriction on L or invariant adjacencies is claimed here. In particular neither A0 nor A1 is excluded, and no full five-orbit or global graph exclusion is asserted. This is a paper argument without graph enumeration or Lean formalization.
