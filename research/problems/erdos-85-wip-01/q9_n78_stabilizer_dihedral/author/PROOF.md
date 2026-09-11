# An order16 vertex stabilizer is dihedral (conditional on2260)

Assume the necessary equality form2260 for a two-subgroup H of order16 fixing a vertex of the N78 graph. In particular H has distinct conjugacy classes T_v,T_x of involutions, each of size four; any member of either has centralizer of order four. Then H is dihedral of order16. This classification uses no enumeration of groups.

Choose t in T_v. There exists s in T_x not commuting with t. Otherwise the centralizer of t, of size four, would contain all four members of T_x as well as the identity, impossible. Put r=ts. Since s and t are involutions, t r t=r^-1. The subgroup K=<t,s>=<r,t> is dihedral of order twice the order of r. To justify that cardinality, every word reduces to r^i or r^i t. If t belonged to <r>, then s=t r would belong to the same cyclic group and commute with t, contrary to choice. Thus the two cosets are distinct.

The order of r is a power of two, is greater than two because s and t do not commute, and is at most eight because |K|<=|H|=16. Consequently it is four or eight.

Suppose it is four. Then K is dihedral of order eight and has index two in H, hence is normal. Its five nonidentity involutions are r^2, t, r^2 t, s, r^2 s. Within K, t and r^2 t are conjugate, as are s and r^2 s. Hence the second pair belongs to T_x and cannot belong to T_v. The central involution r^2 has centralizer in H containing K, so of order at least eight; it cannot be H-conjugate to t, whose centralizer has order four. It follows that at most the two elements t,r^2 t of K lie in T_v. But normality of K requires the entire H-conjugacy class T_v, of size four, to lie in K. Contradiction.

Therefore r has order eight. The sixteen elements r^i and r^i t exhaust H, with t^2=1 and t r t=r^-1. These give the usual dihedral group of order16 (the symmetry group of an octagon).

This classifies the equality stabilizer but does not exclude its occurrence or an order32 two-subgroup in the graph. It is a paper implication conditional on2260 and must not be used as accepted graph evidence before that premise and this proof are independently reviewed. No graph or group search and no Lean formalization are used.
