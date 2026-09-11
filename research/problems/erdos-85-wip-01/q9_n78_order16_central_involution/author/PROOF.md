# Every full order-sixteen action has a central six-fixed involution

Let G be simple, C4-free and nine-regular on78 vertices, and let its full automorphism group A have order16. Accepted2422 gives two alternatives: A has a central involution fixing the six matching centers S exactly, or A acts faithfully on S and is C2 x D8. We exclude the faithful alternative using accepted2425 and an unordered-pair capacity argument.

## A free-middle pair lemma

Suppose a group A acts by automorphisms on a C4-free simple graph, Y is an invariant vertex set, and M is a regular A-orbit. Every vertex m in M has the same number b of neighbors in Y. Consider incidences (m,{y,y'}) where y,y' are distinct Y-neighbors of m. There are |A|*binomial(b,2) incidences, and A acts freely on them because it acts freely on their first coordinate.

Forgetting the middle m maps these incidences injectively to unordered pairs of Y vertices. Indeed two distinct middles for the same pair give a C4, since in a simple graph neither middle is an endpoint of its neighbor pair. This map is equivariant. Therefore its image is a disjoint union of exactly binomial(b,2) free A-orbits on unordered Y-pairs.

The images obtained from two disjoint regular middle orbits are also disjoint, by the same unique-common-neighbor condition. This statement applies when M=Y and Y itself is regular: a middle is still distinct from its two endpoints, and the injectivity argument is unchanged.

If Y is a regular A-orbit, its free unordered-pair orbits can be counted directly from A. Identify Y with A under left multiplication. Translate any pair to{1,d}, d not identity. Such a pair has a nontrivial setwise stabilizer precisely when d has order2: a nonidentity stabilizer must swap its two elements, forcing d^2=1. Otherwise its stabilizer is trivial. Two such origin pairs belong to the same orbit precisely when their differences are d and d^-1. Hence the number of free pair orbits is half the number of nonidentity elements whose order is not2.

## Capacity required by the faithful branch

In the faithful alternative, accepted2425 gives W=W0 unionW1 unionW2, three regular A-orbits of size16, and R=X unionY where X has size8 and Y is regular of size16. The induced Y graph has degree2. The saturated structure2419 gives every vertex of Y exactly six W-neighbors.

Let b_i be the number of Y-neighbors of any vertex in W_i. Since W_i and Y are transitive of the same size, edge balance gives that every Y vertex has exactly b_i neighbors in W_i. Thus b0+b1+b2=6.

Apply the free-middle lemma to the three W_i. They require sum_i binomial(b_i,2) distinct free pair orbits on Y. For nonnegative integers b_i summing to6,

sum_i binomial(b_i,2)=3+(1/2)*sum_i(b_i-2)^2 >=3.

Apply the same lemma to the middle orbit Y itself, whose internal degree is2. This requires one additional free pair orbit, disjoint from those contributed by W. Therefore the regular Y-action must have at least four free unordered-pair orbits. Equivalently, A must have at least eight nonidentity elements of order other than2.

But C2 x D8 has exactly four such elements. Write D8=<r,s | r^4=s^2=1,srs=r^-1>. The only order4 elements are r and r^3. Taking either C2 coordinate gives four order4 elements in the direct product. Every other nonidentity element is an involution. Thus its regular action has only two free unordered-pair orbits, contradicting the required four.

The faithful alternative is impossible. By accepted2422, every full automorphism group of order16 therefore has a central involution fixing exactly S, whose fixed graph is3K2. This is a universal structural restriction at order16, not an exclusion of order16 itself. The central fixed-matching branch remains open.

The free-middle capacity lemma also applies to any other action with three regular W16 orbits, regular Y16 of internal degree2, and Y-to-W degree6; it does not require the faithful S-action except to obtain those hypotheses. No finite graph search, pending group-table classification, capped-domain retry or Lean formalization is used.
