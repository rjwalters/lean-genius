# Complete order24 single-attachment five-orbit action cover

Assume G is simple, C4-free and nine-regular on78 vertices, A=Aut(G) has order24, and the orbit sizes are F6,B12,C12,U24,V24. Consider the first eight quotients in accepted2335, those in which F induces a matching, each F vertex has four neighbors in U and four in V, every U/V vertex has a unique F neighbor, and B,C have no F neighbors.

After swapping B,C if needed, the quotient has U-to-B degree one and U-to-C degree two, with V-to-B degree two and V-to-C degree one. Hence B-to-U,V degrees are two and four; C-to-U,V degrees are four and two. Both U and V have equal internal degree a in{1,2,3,4} and cross degree5-a. The induced graph on B union C is cubic, but neither12-orbit is regular, and no cubic Cayley hypothesis on it is made.

## Complete group cover from the12-orbit stabilizer

Every12-orbit has a point stabilizer L of order two. If its generating involution were central in A, it would fix all12 vertices of that orbit, contradicting accepted2257's bound of six fixed vertices. In particular A cannot be abelian or have a unique involution.

The group-classification argument of accepted2319 can therefore be reused with this replacement for its elementary Cayley obstructions. If the Sylow3 subgroup is normal, A=C3 semidirect P8, with all five groups P8 and all binary characters:22 models. If there are four Sylow3 subgroups, their permutation action gives A=S4 or a central extension of A4. In the latter case its normal Sylow2 group is E8 or Q8; Q8 gives a unique involution and is excluded by the preceding fixed-point argument. The E8 action gives A4 times C2. Thus the same24 labelled group tables cover every group here, independently of any residual Cayley graph.

Accepted2322 verifies these tables. The nine models whose saved cubic Cayley lists are empty can also be excluded HERE, but for a different reason: direct table inspection shows that every involution in each is central. They are C8 with either character, C4xC2 with characters00000000 and00110011, E8 with character00000000, and Q8 with any character. Their numbers of involutions are respectively1,1,3,3,7,1,1,1,1; each commutes with all24 elements. A saved direct verification records this. None can provide the required12-orbit stabilizer. Consequently the remaining15 tables suffice, and every H4/matching record of2322 can be reused as a complete six-center action list.

## Six-center and partial-graph parameters

For each group choose every order-four subgroup H and every matching coset aH in N_A(H)/H different from H with a^2 in H. The six-center action is A/H with matching gH--gaH, exactly as proved in2319 and exhaustively listed in2322. Choose origins in U,V over H, so Ug,Vg both attach to gH.

For each internal degree a in{1,2,3,4}, choose inverse-closed internal sets SU,SV of size a, omitting identity, and a cross set T of size5-a. The labels of SU and T together are exactly the five cosets other than the matching partner of H, each once. The same holds for SV and T^-1. This is the five-slot saturation in the single-attachment quotient. No inverse closure is imposed on T.

Left translates supply all edges. The same UU,VV,UV common-neighbor formulas from accepted2325 apply: both U and V attach to the same six-center orbit, so even the mixed pair U1,Vg has a fixed-center contribution1[gH=H]. Here all four internal degrees are allowed, rather than only1 and4. Exhausting those choices gives a complete necessary F+U+V domain.

## Necessary12-orbit incidence parameters

It suffices for an obstruction to test the required B orbit, with two U and four V neighbors at a vertex. Select a B vertex b and translate a chosen U-neighbor to U1. In the resulting coordinates the stabilizer of b is an order-two subgroup L={1,l}; enumerate every nonidentity involution l to cover the possible conjugated stabilizer.

Its two U-neighbors must be exactly{U1,Ul}, since L acts freely on U. Its four V-neighbors must be two disjoint pairs of the form{Vg,Vlg}. The six chosen vertices must project bijectively to all six fixed centers; a repeated center would give b and that center two common attached neighbors. Every chosen pair must have zero common neighbors in the partial graph. These conditions cover every normalized base neighborhood X.

The other B-neighborhoods are gX indexed by left cosets gL. For each g outside L, require |X intersect gX|<=1. This is necessary since the corresponding B vertices are distinct; for g in L the intersection is all of X by invariance. If X has a larger stabilizer, the outside-L test rejects it, as two distinct B vertices would then have identical neighborhoods. These tests do not use C, B/C internal edges, or any full graph completion.

This paper gives a complete necessary parameterization for the single-attachment case, not an enumeration outcome or exclusion. It does not reuse the cubic residual hypothesis of the four-orbit case. No full graph solver or Lean formalization is included.
